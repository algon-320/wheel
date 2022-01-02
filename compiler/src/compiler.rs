use log::debug;
use std::collections::{BTreeMap, HashMap};
type Stack<T> = std::vec::Vec<T>;

use crate::ast::{DataDef, Def, Expr, Field, FuncDef, Program};
use crate::error::Error;
use crate::ty::{Category, ResolvedType, Type, TypedExpr};
use spec::Instruction as I;

fn load_nb(nb: u8) -> I {
    match nb {
        1 => I::Load08,
        2 => I::Load16,
        4 => I::Load32,
        8 => I::Load64,
        _ => unimplemented!(),
    }
}

fn store_nb(nb: u8) -> I {
    match nb {
        1 => I::Store08,
        2 => I::Store16,
        4 => I::Store32,
        8 => I::Store64,
        _ => unimplemented!(),
    }
}

fn eq_nb(nb: u8) -> I {
    match nb {
        1 => I::Eq08,
        2 => I::Eq16,
        4 => I::Eq32,
        8 => I::Eq64,
        _ => unimplemented!(),
    }
}

#[derive(Debug, Clone)]
enum Ir {
    OpCode(I),
    RawBytes(Vec<u8>),
    Pointer(PointerId),
    Pointee(PointerId),
}
impl From<I> for Ir {
    fn from(i: I) -> Ir {
        Ir::OpCode(i)
    }
}
macro_rules! impl_from_int {
    ($t:ty) => {
        impl From<$t> for Ir {
            fn from(x: $t) -> Self {
                Self::RawBytes(x.to_le_bytes().to_vec())
            }
        }
    };
}
impl_from_int! {u8}
impl_from_int! {u16}
impl_from_int! {u32}
impl_from_int! {u64}

impl From<Ir> for Vec<u8> {
    fn from(ir: Ir) -> Vec<u8> {
        use Ir::*;
        match ir {
            OpCode(op) => vec![op.into()],
            RawBytes(bytes) => bytes,
            Pointer(_) => vec![0xAA_u8; 8],
            Pointee(_) => vec![],
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PointerId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct BlockId(u64);

#[derive(Clone)]
struct BasicBlock {
    id: BlockId,
    buf: Vec<Ir>,
}

impl std::fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "id:{}", self.id.0)?;
        for e in &self.buf {
            writeln!(f, "\t{:?}", e)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
enum Addr {
    BpRel(i64),
    Static(PointerId),
}

struct FunctionContext {
    stack_cursor: u64,
    required_memory: u64,
    return_bb_addr: PointerId,
}
impl FunctionContext {
    fn new(return_bb_addr: PointerId) -> Self {
        Self {
            stack_cursor: 0,
            required_memory: 0,
            return_bb_addr,
        }
    }

    fn allocate(&mut self, size: u64) -> u64 {
        self.stack_cursor += size;
        self.required_memory = std::cmp::max(self.required_memory, self.stack_cursor);
        self.stack_cursor
    }

    fn deallocate(&mut self, size: u64) -> u64 {
        self.stack_cursor -= size;
        self.stack_cursor
    }
}

struct LoopContext {
    begin_of_loop: PointerId,
    end_of_loop: PointerId,
}

struct Scope {
    dict: HashMap<String, (Addr, ResolvedType)>,
}
impl Scope {
    fn size(&self) -> u64 {
        let mut sum = 0;
        for (_, ty) in self.dict.values() {
            sum += ty.size_of();
        }
        sum
    }
}

struct Environment {
    scopes: Stack<Scope>,
}
impl Environment {
    pub fn new() -> Self {
        Self {
            scopes: Stack::new(),
        }
    }

    pub fn create_new_scope(&mut self) {
        self.scopes.push(Scope {
            dict: HashMap::new(),
        });
    }
    pub fn pop_scope(&mut self) -> Option<Scope> {
        let scope = self.scopes.pop()?;
        Some(scope)
    }

    pub fn insert(&mut self, name: String, addr: Addr, ty: ResolvedType) {
        let scope = &mut self.scopes.last_mut().unwrap();
        let old = scope.dict.insert(name.clone(), (addr, ty));
        if old.is_some() {
            log::warn!("variable shadowed: {}", name);
        }
    }

    pub fn get(&self, var_name: &str) -> Option<(Addr, &ResolvedType)> {
        for scope in self.scopes.iter().rev() {
            if let Some((addr, ty)) = scope.dict.get(var_name) {
                return Some((*addr, ty));
            }
        }
        None
    }
}

type StructLayout = HashMap<String, u64>;

pub struct Compiler {
    debug: bool,

    bbs: HashMap<BlockId, BasicBlock>,
    emit_bb: BlockId,
    next_bb: BlockId,
    next_ptr_id: PointerId,

    entry_point_bb: BlockId,
    static_data_bb: BlockId,

    env: Environment,
    struct_layout: HashMap<String, StructLayout>,
    func_ctx: Option<FunctionContext>,
    loop_ctx: Stack<LoopContext>,
}

impl Compiler {
    pub fn new(debug: bool) -> Self {
        log::info!("debug: {}", if debug { "enabled" } else { "disabled" });

        let mut env = Environment::new();
        env.create_new_scope();

        let mut struct_layout = HashMap::new();
        struct_layout.insert("internal.slice".to_owned(), {
            let mut layout = StructLayout::new();
            layout.insert("ptr".to_owned(), 0);
            layout.insert("len".to_owned(), 8);
            layout
        });

        let mut c = Self {
            debug,

            bbs: HashMap::new(),
            emit_bb: BlockId(0),
            next_bb: BlockId(0),
            next_ptr_id: PointerId(1),

            entry_point_bb: BlockId(0),
            static_data_bb: BlockId(0),

            env,
            struct_layout,
            func_ctx: None,
            loop_ctx: Stack::new(),
        };

        // Initialize special basic blocks
        {
            let (ep, _) = c.new_block();
            c.set_insertion_point(ep);
            c.entry_point_bb = ep;

            let (data_bb, _) = c.new_block();
            c.static_data_bb = data_bb;
        }

        c
    }

    fn new_block(&mut self) -> (BlockId, PointerId) {
        let bid = self.next_bb;
        self.next_bb = BlockId(self.next_bb.0 + 1);

        let ptr_id = self.new_pointer();

        let buf = vec![Ir::Pointee(ptr_id)];
        let bb = BasicBlock { id: bid, buf };
        self.bbs.insert(bid, bb);

        (bid, ptr_id)
    }

    fn new_pointer(&mut self) -> PointerId {
        let ptr_id = self.next_ptr_id;
        self.next_ptr_id = PointerId(self.next_ptr_id.0 + 1);
        ptr_id
    }

    fn set_insertion_point(&mut self, id: BlockId) {
        self.emit_bb = id;
    }

    fn emit<T: Into<Ir>>(&mut self, e: T) {
        let bb = self.bbs.get_mut(&self.emit_bb).unwrap();
        bb.buf.push(e.into());
    }

    fn emit_debug_comment(&mut self, comment: &str) {
        if self.debug {
            let bb = self.bbs.get_mut(&self.emit_bb).unwrap();
            bb.buf.push(I::DebugComment.into());
            let utf8_bytes = comment.as_bytes();
            assert!(utf8_bytes.len() < 256);
            let len = utf8_bytes.len() as u8;

            let mut bytes = vec![len];
            bytes.extend(utf8_bytes);
            bb.buf.push(Ir::RawBytes(bytes));
        }
    }

    fn generate_function_call_no_arg(
        &mut self,
        name: String,
        ret_ty: ResolvedType,
    ) -> Result<(), Error> {
        use Expr::*;
        let func = TypedExpr {
            e: Var(name),
            ty: Type::Ptr(Box::new(
                Type::Func {
                    params: vec![],
                    ret_ty: ret_ty.clone().into(),
                }
                .into(),
            ))
            .into(),
            cat: Category::Regular,
        };
        let call = TypedExpr {
            e: Call {
                func: func.into(),
                args: vec![],
            },
            ty: ret_ty,
            cat: Category::Regular,
        };
        self.compile_expr(call.into())?;
        Ok(())
    }

    fn generate_store(&mut self, size: u64) {
        match size {
            0 => panic!("store zero sized value"),
            1 => self.emit(I::Store08),
            2 => self.emit(I::Store16),
            4 => self.emit(I::Store32),
            8 => self.emit(I::Store64),
            _ => {
                self.emit_debug_comment(&format!("store {} bytes: begin", size));
                let mut r = size;
                let mut p = 0_u64;
                while r > 0 {
                    let n = match r {
                        8.. => 8,
                        4.. => 4,
                        2.. => 2,
                        1 => 1,
                        0 => unreachable!(),
                    };

                    // load [src+p..src+p+n]
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(8 + p);
                    self.emit(I::Add64);
                    self.emit(load_nb(n as u8));

                    // load dst
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(n);
                    self.emit(I::Add64);
                    self.emit(I::Load64);
                    // +p
                    self.emit(I::Lit64);
                    self.emit(p);
                    self.emit(I::Add64);

                    // store
                    self.emit(store_nb(n as u8));

                    p += n;
                    r -= n;
                }

                self.generate_drop(size + 8 /*dst*/);
                self.emit_debug_comment(&format!("store {} bytes: end", size));
            }
        }
    }

    fn generate_load(&mut self, size: u64) {
        match size {
            0 => panic!("load zero sized value"),
            1 => self.emit(I::Load08),
            2 => self.emit(I::Load16),
            4 => self.emit(I::Load32),
            8 => self.emit(I::Load64),
            _ => {
                if size >= 8 {
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(size - 8);
                    self.emit(I::Sub64);
                    self.emit(I::SetSp);

                    // copy src
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(size - 8);
                    self.emit(I::Add64);
                    self.emit(I::Load64);
                }

                let mut r = size;
                let mut p = 0_u64;
                while r > 0 {
                    let n = match r {
                        8.. => 8,
                        4.. => 4,
                        2.. => 2,
                        1 => 1,
                        0 => unreachable!(),
                    };

                    // load src
                    self.emit(I::GetSp);
                    self.emit(I::Load64);
                    // +p
                    self.emit(I::Lit64);
                    self.emit(p);
                    self.emit(I::Add64);

                    // load value (n-bytes)
                    self.emit(load_nb(n as u8));

                    // calculate dst
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(n + 8 + p);
                    self.emit(I::Add64);

                    // store value (n-bytes)
                    self.emit(store_nb(n as u8));

                    p += n;
                    r -= n;
                }

                if size < 8 {
                    self.generate_drop(8 - size);
                } else {
                    self.emit(I::Drop64); // src
                }
            }
        }
    }

    fn generate_drop(&mut self, n: u64) {
        match n {
            0 => {}
            1 => self.emit(I::Drop08),
            2 => self.emit(I::Drop16),
            4 => self.emit(I::Drop32),
            8 => self.emit(I::Drop64),
            // OPTIMIZE: combining multiple DropXX's could be better
            // e.g. for 16-bytes drop, [Drop64, Drop64]
            // is better than the direct modification of SP
            _ => {
                self.emit(I::GetSp);
                self.emit(I::Lit64);
                self.emit(n);
                self.emit(I::Add64);
                self.emit(I::SetSp);
            }
        }
    }

    pub fn compile(mut self, prog: Program<TypedExpr, ResolvedType>) -> Result<Vec<u8>, Error> {
        for def in prog.defs {
            match def {
                Def::Struct(def) => {
                    let mut layout = StructLayout::new();
                    let mut offset = 0;
                    for Field { name, ty } in def.fields {
                        layout.insert(name, offset);
                        offset += ty.size_of();
                    }
                    debug!("struct {} (size={}): {:?}", def.name, offset, layout);
                    self.struct_layout.insert(def.name, layout);
                }
                Def::Data(data) => {
                    self.compile_static_data(data)?;
                }
                Def::Func(fun) => {
                    self.compile_function(fun)?;
                }
            }
        }

        let entry_point = self.entry_point_bb;
        {
            self.set_insertion_point(entry_point);

            // Call the main
            self.generate_function_call_no_arg("main".to_owned(), Type::U64.into())?; // FIXME: return type
            self.emit(I::Abort);
        }

        debug!("entry = {:?}", entry_point);
        for bb in self.bbs.values() {
            debug!("{:?}", bb);
        }

        let mut text = Vec::new();
        {
            let mut pointees = HashMap::new();
            let mut unresolved: HashMap<PointerId, Vec<usize>> = HashMap::new();

            let mut compile_basic_block = |id: BlockId, bb: BasicBlock| {
                debug!("block {:?} ==> {}", id, text.len());
                for e in bb.buf {
                    match e {
                        Ir::Pointer(ptr_id) => {
                            let pos = unresolved.entry(ptr_id).or_insert_with(Vec::new);
                            pos.push(text.len());
                        }
                        Ir::Pointee(ptr_id) => {
                            debug!("pointee {:?} ==> {}", ptr_id, text.len());
                            pointees.insert(ptr_id, text.len());
                        }
                        _ => {}
                    }
                    text.extend(Vec::<u8>::from(e));
                }
            };

            let entry_point_bb = self.entry_point_bb;
            let entry = self.bbs.remove(&entry_point_bb).unwrap();
            let data_bb = self.static_data_bb;
            let data_section = self.bbs.remove(&data_bb).unwrap();

            // Put the entry point bb at the very beginning
            compile_basic_block(entry_point, entry);
            for (id, bs) in self.bbs {
                compile_basic_block(id, bs);
            }
            // Put the data section at the end
            compile_basic_block(data_bb, data_section);

            for (id, pos) in unresolved {
                let bytes = pointees[&id].to_le_bytes();
                for p in pos {
                    debug_assert_eq!(&text[p..p + 8], &[0xAA_u8; 8]);
                    text[p..(p + 8)].copy_from_slice(&bytes);
                }
            }
        }
        Ok(text)
    }

    fn choose_temporal_name(&mut self, prefix: &str) -> String {
        for i in 0..usize::MAX {
            let name = format!("{}.{}", prefix, i);
            if self.env.get(&name).is_some() {
                continue;
            }
            return name;
        }
        panic!("too many conflicts");
    }

    fn compile_static_data(&mut self, data: DataDef<TypedExpr, ResolvedType>) -> Result<(), Error> {
        let ty = data.initializer.ty.clone();

        let initializer_name = self.choose_temporal_name("internal.initializer");
        self.compile_function(FuncDef {
            name: initializer_name.clone(),
            ret_ty: ty.clone(),
            params: vec![],
            body: data.initializer.clone(),
        })?;

        let data_location = self.new_pointer();
        let addr = Addr::Static(data_location);
        self.env.insert(data.name, addr, ty.clone());

        let old_bb = self.emit_bb;

        // Append a call for the initializer
        {
            self.set_insertion_point(self.entry_point_bb);

            // Call initializer
            self.generate_function_call_no_arg(initializer_name, ty.clone())?;
            // Store the return value at the data location
            if ty.size_of() > 0 {
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(data_location));
                self.generate_store(ty.size_of());
            }
        }

        // Extend the data_bb
        {
            self.set_insertion_point(self.static_data_bb);

            self.emit(Ir::Pointee(data_location));
            let size = ty.size_of();
            // NOTE: the value 0xBB is meaningless (just for ease of debuging)
            self.emit(Ir::RawBytes(vec![0xBB; size as usize]));
        }

        self.set_insertion_point(old_bb);
        Ok(())
    }

    fn compile_function(&mut self, fun: FuncDef<TypedExpr, ResolvedType>) -> Result<(), Error> {
        let (func_bb, func_addr) = self.new_block();
        let (return_bb, return_addr) = self.new_block();

        self.set_insertion_point(func_bb);

        let addr = Addr::Static(func_addr);
        let func_ty = Type::Func {
            params: fun.params.iter().map(|f| f.ty.clone()).collect(),
            ret_ty: fun.ret_ty.clone().into(),
        };
        self.env.insert(fun.name, addr, func_ty.into());

        //----------------------------------------------------------------------
        // create a scope for parameter
        self.env.create_new_scope();

        let mut offset = 16; // return IP + caller BP
        for p in fun.params.iter() {
            let addr = Addr::BpRel(offset);
            self.env.insert(p.name.clone(), addr, p.ty.clone());
            offset += p.ty.size_of() as i64;
        }

        self.func_ctx = Some(FunctionContext::new(return_addr));
        self.compile_expr(fun.body)?;
        let fctx = self.func_ctx.take().unwrap();

        self.env.pop_scope().expect("scope unbalanced");
        //----------------------------------------------------------------------

        let local_vars_size = fctx.required_memory;
        debug!("local_vars_size: {}", local_vars_size);

        // Prologue
        {
            let old_bb = self.emit_bb;

            let bb = self.bbs.get_mut(&func_bb).unwrap();
            let mut old_buf = std::mem::take(&mut bb.buf);

            bb.buf.push(old_buf[0].clone()); // pointer
            self.set_insertion_point(func_bb);

            // SP = SP - local_vars_size
            self.emit(I::GetSp);
            self.emit(I::Lit64);
            self.emit(local_vars_size);
            self.emit(I::Sub64);
            self.emit(I::SetSp);

            let bb = self.bbs.get_mut(&func_bb).unwrap();
            bb.buf.extend(old_buf.drain(1..));

            self.set_insertion_point(old_bb);
        }

        // Epilogue
        {
            self.emit(I::Lit64);
            self.emit(Ir::Pointer(return_addr));
            self.emit(I::Jump);

            self.set_insertion_point(return_bb);

            //                <-- SP
            // [ ret val    ]
            // [ local vars ]
            // -------------- <-- BP
            // [ caller BP  ]
            // [ return IP  ]
            // [ args       ]
            // [ ret val    ]
            // [ ********** ]

            // save the return value
            let ret_ty = &fun.ret_ty;
            if ret_ty.size_of() > 0 {
                let args_size: u64 = fun.params.iter().map(|p| p.ty.size_of()).sum();
                let ret_val_offset = 8/* caller BP */ + 8/* return IP */ + args_size;
                self.emit(I::GetBp);
                self.emit(I::Lit64);
                self.emit(ret_val_offset);
                self.emit(I::Add64);
                self.generate_store(ret_ty.size_of());
            }

            // Drop local variables (and temporal values)
            self.emit(I::GetBp);
            self.emit(I::SetSp);

            // Retrieve the return address
            self.emit(I::GetBp);
            self.emit(I::Lit64);
            self.emit(8_u64);
            self.emit(I::Add64);
            {
                // Restore BP
                self.emit(I::GetBp);
                self.emit(I::Load64);
                self.emit(I::SetBp);
            }
            // Return to the caller
            self.emit(I::Load64);
            self.emit(I::Jump);
        }

        Ok(())
    }

    #[allow(clippy::boxed_local)]
    fn compile_expr(&mut self, expr: Box<TypedExpr>) -> Result<(), Error> {
        let expr_ty = expr.ty.clone();
        let expr_cat = expr.cat;

        use Expr::*;
        match expr.e {
            LiteralVoid => {}
            LiteralBool(b) => {
                self.emit(I::Lit08);
                self.emit(b as u8);
            }
            LiteralU08(v) => {
                self.emit(I::Lit08);
                self.emit(v);
            }
            LiteralU16(v) => {
                self.emit(I::Lit16);
                self.emit(v);
            }
            LiteralU32(v) => {
                self.emit(I::Lit32);
                self.emit(v);
            }
            LiteralU64(v) => {
                self.emit(I::Lit64);
                self.emit(v);
            }

            LiteralArray(elems) => {
                for e in elems.into_iter().rev() {
                    self.compile_expr(e)?;
                }
            }

            LiteralSliceFromPtr { ptr, size } => {
                self.compile_expr(size)?;
                self.compile_expr(ptr)?;
            }

            LiteralSliceFromArray {
                mut array,
                begin,
                end,
            } => {
                let elem_ty = match &array.ty.0 {
                    Type::Array(elem_ty, _) => elem_ty.clone(),
                    _ => unreachable!(),
                };

                // size: end - begin
                self.compile_expr(end)?;
                self.compile_expr(begin.clone())?;
                self.emit(I::Sub64);

                array.cat = Category::Location;
                self.compile_expr(array)?;

                self.compile_expr(begin)?;
                self.emit(I::Lit64);
                self.emit(elem_ty.size_of());
                self.emit(I::Mul64);
                self.emit(I::Add64);
            }

            LiteralStruct {
                name: struct_name,
                fields,
            } => {
                let layout = match self.struct_layout.get(&struct_name) {
                    Some(l) => l,
                    None => {
                        return Err(Error::UndefinedType { name: struct_name });
                    }
                };

                let mut value_offset = BTreeMap::new();
                for (name, value) in fields {
                    if let Some(offset) = layout.get(&name).copied() {
                        value_offset.insert(offset, value);
                    } else {
                        return Err(Error::UndefinedField {
                            struct_name,
                            field_name: name,
                        });
                    }
                }

                // push each field in reverse order
                for (_, value) in value_offset.into_iter().rev() {
                    self.compile_expr(value)?;
                }
            }

            LiteralString(bytes) => {
                let ptr = self.new_pointer();
                let size = bytes.len() as u64;

                let old_bb = self.emit_bb;
                {
                    self.set_insertion_point(self.static_data_bb);

                    self.emit(Ir::Pointee(ptr));
                    self.emit(Ir::RawBytes(bytes));
                }
                self.set_insertion_point(old_bb);

                self.emit(I::Lit64);
                self.emit(size);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(ptr));
            }

            Var(_) if expr_ty.size_of() == 0 => {}
            Var(name) => {
                let (addr, var_ty) = match self.env.get(&name) {
                    Some((addr, var_ty)) => (addr, var_ty.clone()),
                    None => return Err(Error::UndefinedVar { name }),
                };

                match addr {
                    Addr::Static(location) => {
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(location));

                        match var_ty.0 {
                            Type::Func { .. } => {
                                // If the variable represents a function,
                                // We treat it as a pointer to the function.
                                // That is, no loading from `location` needed in this case.
                                assert_eq!(
                                    expr_cat,
                                    Category::Regular,
                                    "function is not a location expression"
                                );
                            }
                            _ => {
                                if expr_cat == Category::Regular {
                                    self.generate_load(expr_ty.size_of());
                                }
                            }
                        }
                    }

                    Addr::BpRel(offset) => {
                        self.emit(I::GetBp);
                        self.emit(I::Lit64);
                        self.emit(offset.abs() as u64);
                        if offset > 0 {
                            self.emit(I::Add64); // function argument
                        } else {
                            self.emit(I::Sub64); // local variable
                        }

                        match var_ty.0 {
                            Type::Func { .. } => unimplemented!("function on the stack"),
                            _ => {
                                if expr_cat == Category::Regular {
                                    self.generate_load(expr_ty.size_of());
                                }
                            }
                        }
                    }
                }
            }

            AddrOf(location) => {
                self.compile_expr(location)?;
            }

            PtrDeref(ptr) => {
                self.compile_expr(ptr)?;
                if expr_cat == Category::Regular {
                    assert_ne!(expr_ty.0, Type::Void, "deref of *()");
                    self.generate_load(expr_ty.size_of());
                }
            }

            IndexAccess { ptr, idx } => match &ptr.ty.0 {
                Type::Array(_, len) => {
                    let elem_ty = expr_ty;
                    let elem_size = elem_ty.size_of();
                    let len = *len as u64;

                    self.compile_expr(ptr)?;

                    if expr_cat == Category::Location {
                        // SP + (idx * elem_size)
                        self.compile_expr(idx)?;
                        self.emit(I::Lit64);
                        self.emit(elem_size);
                        self.emit(I::Mul64);
                        self.emit(I::Add64);
                    } else {
                        // extract the idx'th element

                        // load idx'th element
                        // SP + (idx * elem_size)
                        self.emit(I::GetSp);
                        self.compile_expr(idx)?;
                        self.emit(I::Lit64);
                        self.emit(elem_size);
                        self.emit(I::Mul64);
                        self.emit(I::Add64);
                        self.generate_load(elem_size);

                        // copy it to the bottom of this array
                        // SP + (len * elem_size)
                        self.emit(I::GetSp);
                        self.emit(I::Lit64);
                        self.emit(len); // (len - elem) + elem
                        self.emit(I::Lit64);
                        self.emit(elem_size);
                        self.emit(I::Mul64);
                        self.emit(I::Add64);
                        self.generate_store(elem_size);

                        // discard other values
                        self.generate_drop((len - 1) * elem_size);
                    }
                }

                Type::Slice(_) => {
                    self.compile_expr(ptr)?;

                    if expr_cat == Category::Location {
                        self.emit(I::Load64); // load ptr
                        self.compile_expr(idx)?;
                        self.emit(I::Lit64);
                        self.emit(expr_ty.size_of());
                        self.emit(I::Mul64);
                        self.emit(I::Add64);
                    } else {
                        // slice.ptr
                        self.emit(I::GetSp);
                        self.emit(I::Lit64);
                        self.emit(8_u64);
                        self.emit(I::Add64);
                        self.emit(I::Store64);

                        // ptr + idx * sizeof(ty)
                        self.compile_expr(idx)?;
                        self.emit(I::Lit64);
                        self.emit(expr_ty.size_of());
                        self.emit(I::Mul64);
                        self.emit(I::Add64);

                        self.generate_load(expr_ty.size_of());
                    }
                }

                _ => unreachable!("type error"),
            },

            MemberAccess { obj, field } => {
                let obj_ty = obj.ty.clone();
                let obj_cat = obj.cat;

                // TODO: avoid redundant laod
                self.compile_expr(obj)?;

                let layout = match &obj_ty.0 {
                    Type::Struct { name, .. } => &self.struct_layout[name],
                    Type::Slice(_) => &self.struct_layout["internal.slice"],
                    _ => todo!("member access for non-struct value"),
                };
                let offset = layout[&field];

                if obj_cat == Category::Location {
                    self.emit(I::Lit64);
                    self.emit(offset);
                    self.emit(I::Add64);
                } else {
                    assert_eq!(expr_cat, Category::Regular);
                    let size = expr_ty.size_of();

                    // Example: extract obj.field2
                    //
                    //    8: [ field1  ]
                    //    9: [ field2  ]
                    //   10: [ field3  ]

                    // 1. load the field
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(offset);
                    self.emit(I::Add64);
                    self.generate_load(size);

                    //    7: [ field2 ]
                    //       ----------
                    //    8: [ field1 ]
                    //    9: [ field2 ]
                    //   10: [ field3 ]

                    // 2. replace the obj with the value

                    // 2.1 calculate store address
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(obj_ty.size_of()); // size + sizeof(obj) - size
                    self.emit(I::Add64);

                    //    6: [ 10     ]
                    //    7: [ field2 ]
                    //       ----------
                    //    8: [ field1 ]
                    //    9: [ field2 ]
                    //   10: [ field3 ]

                    // 2.2 store the value
                    self.generate_store(size);

                    //    8: [ field1 ]
                    //    9: [ field2 ]
                    //   10: [ field2 ]

                    // 2.3 dicard uninterestead fields
                    self.generate_drop(obj_ty.size_of() - size);

                    //   10: [ field2 ]
                }
            }

            Cast(e, ty) => {
                fn literal(c: &mut Compiler, ty: &ResolvedType, v: u8) {
                    match &ty.0 {
                        Type::U08 => {
                            c.emit(I::Lit08);
                            c.emit(v as u8);
                        }
                        Type::U16 => {
                            c.emit(I::Lit16);
                            c.emit(v as u16);
                        }
                        Type::U32 => {
                            c.emit(I::Lit32);
                            c.emit(v as u32);
                        }
                        Type::U64 => {
                            c.emit(I::Lit64);
                            c.emit(v as u64);
                        }
                        _ => panic!(),
                    }
                }

                let from = &e.ty.clone();
                let to = &ty;

                match (&from.0, &to.0) {
                    (
                        Type::U08 | Type::U16 | Type::U32 | Type::U64,
                        Type::U08 | Type::U16 | Type::U32 | Type::U64,
                    ) => {
                        self.compile_expr(e)?;

                        use std::cmp::Ordering;
                        match u64::cmp(&from.size_of(), &to.size_of()) {
                            Ordering::Less => {
                                let gap = to.size_of() - from.size_of() * 2;
                                if gap > 0 {
                                    self.emit(I::GetSp);
                                    self.emit(I::Lit64);
                                    self.emit(gap);
                                    self.emit(I::Sub64);
                                    self.emit(I::SetSp);
                                }

                                // copy the value
                                for _ in 0..from.size_of() {
                                    self.emit(I::GetSp);
                                    self.emit(I::Lit64);
                                    self.emit(gap + from.size_of() - 1);
                                    self.emit(I::Add64);
                                    self.emit(I::Load08);
                                }

                                // fill with zero
                                for i in 0..from.size_of() {
                                    self.emit(I::Lit08);
                                    self.emit(0_u8);

                                    self.emit(I::GetSp);
                                    self.emit(I::Lit64);
                                    self.emit(to.size_of() - i);
                                    self.emit(I::Add64);
                                    self.emit(I::Store08);
                                }
                            }
                            Ordering::Greater => {
                                // Keep first `to.size_of()` bytes
                                for _ in 0..to.size_of() {
                                    self.emit(I::GetSp);
                                    self.emit(I::Lit64);
                                    self.emit(from.size_of() - to.size_of());
                                    self.emit(I::Add64);
                                    self.emit(I::Store08);
                                }
                                let rest = from.size_of() - to.size_of() * 2;
                                if rest > 0 {
                                    self.generate_drop(rest as u64);
                                }
                            }
                            Ordering::Equal => {
                                // no actual conversion needed
                            }
                        }
                    }

                    (Type::Bool, Type::U08 | Type::U16 | Type::U32 | Type::U64) => {
                        let (true_bb, true_addr) = self.new_block();
                        let (merge_bb, merge_addr) = self.new_block();

                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(true_addr));

                        self.compile_expr(e)?;

                        self.emit(I::JumpIf);

                        // false --> 0
                        literal(self, to, 0);
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(merge_addr));
                        self.emit(I::Jump);

                        self.set_insertion_point(true_bb);
                        // true --> 1
                        literal(self, to, 1);
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(merge_addr));
                        self.emit(I::Jump);

                        self.set_insertion_point(merge_bb);
                    }

                    (Type::U08 | Type::U16 | Type::U32 | Type::U64, Type::Bool) => {
                        let (false_bb, false_addr) = self.new_block();
                        let (merge_bb, merge_addr) = self.new_block();

                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(false_addr));

                        self.compile_expr(e)?;
                        literal(self, from, 0);
                        self.emit(eq_nb(from.size_of() as u8));

                        self.emit(I::JumpIf);

                        // --> true
                        self.emit(I::Lit08);
                        self.emit(1_u8);
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(merge_addr));
                        self.emit(I::Jump);

                        self.set_insertion_point(false_bb);
                        // --> false
                        self.emit(I::Lit08);
                        self.emit(0_u8);
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(merge_addr));
                        self.emit(I::Jump);

                        self.set_insertion_point(merge_bb);
                    }

                    (Type::Ptr(_) | Type::U64, Type::Ptr(_) | Type::U64) => {
                        self.compile_expr(e)?;
                        // no actual conversion needed
                    }

                    _ => unreachable!("invalid cast"),
                }
            }

            Add(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Slice { .. }
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
                    Type::U08 => self.emit(I::Add08),
                    Type::U16 => self.emit(I::Add16),
                    Type::U32 => self.emit(I::Add32),
                    Type::U64 => self.emit(I::Add64),
                    Type::Func { .. } => unimplemented!(),
                }
            }
            Sub(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Slice { .. }
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
                    Type::U08 => self.emit(I::Sub08),
                    Type::U16 => self.emit(I::Sub16),
                    Type::U32 => self.emit(I::Sub32),
                    Type::U64 => self.emit(I::Sub64),
                    Type::Func { .. } => unimplemented!(),
                }
            }
            Mul(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Slice { .. }
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
                    Type::U08 => self.emit(I::Mul08),
                    Type::U16 => self.emit(I::Mul16),
                    Type::U32 => self.emit(I::Mul32),
                    Type::U64 => self.emit(I::Mul64),
                    Type::Func { .. } => unimplemented!(),
                }
            }
            Div(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Slice { .. }
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
                    Type::U08 => self.emit(I::Div08),
                    Type::U16 => self.emit(I::Div16),
                    Type::U32 => self.emit(I::Div32),
                    Type::U64 => self.emit(I::Div64),
                    Type::Func { .. } => unimplemented!(),
                }
            }

            Eq(lhs, rhs) => {
                let ty = lhs.ty.clone();
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match ty.0 {
                    Type::Void => {
                        // Always true
                        self.emit(I::Lit08);
                        self.emit(1_u8);
                    }
                    Type::Bool => self.emit(I::Eq08),
                    Type::U08 => self.emit(I::Eq08),
                    Type::U16 => self.emit(I::Eq16),
                    Type::U32 => self.emit(I::Eq32),
                    Type::U64 | Type::Ptr(_) => self.emit(I::Eq64),
                    Type::Array(_, _) => todo!("array comparison"),
                    Type::Slice { .. } => todo!("slice comparison"),
                    Type::Struct { .. } => todo!("struct comparison"),
                    Type::Func { .. } => unimplemented!(),
                }
            }
            Lt(lhs, rhs) => {
                let ty = lhs.ty.clone();
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match ty.0 {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Lt08),
                    Type::U08 => self.emit(I::Lt08),
                    Type::U16 => self.emit(I::Lt16),
                    Type::U32 => self.emit(I::Lt32),
                    Type::U64 | Type::Ptr(_) => self.emit(I::Lt64),
                    Type::Array(_, _) => todo!("array comparison"),
                    Type::Slice { .. } => todo!("slice comparison"),
                    Type::Struct { .. } => todo!("struct comparison"),
                    Type::Func { .. } => unimplemented!(),
                }
            }
            Gt(lhs, rhs) => {
                let ty = lhs.ty.clone();
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match ty.0 {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Gt08),
                    Type::U08 => self.emit(I::Gt08),
                    Type::U16 => self.emit(I::Gt16),
                    Type::U32 => self.emit(I::Gt32),
                    Type::Array(_, _) => todo!("array comparison"),
                    Type::Slice { .. } => todo!("slice comparison"),
                    Type::Struct { .. } => todo!("struct comparison"),
                    Type::U64 | Type::Ptr(_) => self.emit(I::Gt64),
                    Type::Func { .. } => unimplemented!(),
                }
            }

            LNot(e) => {
                // top == 0
                self.compile_expr(e)?;
                self.emit(I::Lit08);
                self.emit(0_u8);
                self.emit(I::Eq08);
            }
            Neq(lhs, rhs) => {
                // Eq(lhs, rhs) == 0
                self.compile_expr(
                    TypedExpr {
                        e: Eq(lhs, rhs),
                        ty: Type::Bool.into(),
                        cat: Category::Regular,
                    }
                    .into(),
                )?;
                self.emit(I::Lit08);
                self.emit(0_u8);
                self.emit(I::Eq08);
            }
            Leq(lhs, rhs) => {
                // Gt(lhs, rhs) == 0
                self.compile_expr(
                    TypedExpr {
                        e: Gt(lhs, rhs),
                        ty: Type::Bool.into(),
                        cat: Category::Regular,
                    }
                    .into(),
                )?;
                self.emit(I::Lit08);
                self.emit(0_u8);
                self.emit(I::Eq08);
            }
            Geq(lhs, rhs) => {
                // Lt(lhs, rhs) == 0
                self.compile_expr(
                    TypedExpr {
                        e: Lt(lhs, rhs),
                        ty: Type::Bool.into(),
                        cat: Category::Regular,
                    }
                    .into(),
                )?;
                self.emit(I::Lit08);
                self.emit(0_u8);
                self.emit(I::Eq08);
            }
            LAnd(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                self.emit(I::Mul08);
            }
            LOr(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;

                // lhs + rhs > 0
                self.emit(I::Add08);
                self.emit(I::Lit08);
                self.emit(0_u8);
                self.emit(I::Gt08);
            }

            Call { func, args } => {
                // (lower address)
                //       ^
                //       |
                //       |
                // ------------- <--(callee BP)
                // [ caller BP ]
                // [ return IP ]
                // [ arg0      ]
                // [ arg1      ]
                // [ ....      ]
                // [ ret val   ]
                // [ ********* ]
                // ------------- <--(caller BP)
                //       |
                //       |
                //       v
                // (higher address)

                let fun_ty = func.ty.clone();
                let (params_ty, ret_ty) = match fun_ty.0 {
                    Type::Ptr(inner) => match inner.0 {
                        Type::Func { params, ret_ty } => (params, *ret_ty),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                // make a space for the return value
                match &ret_ty.0 {
                    Type::Void => {}
                    Type::Bool => {
                        self.emit(I::Lit08);
                        self.emit(0xFF_u8);
                    }
                    Type::U08 => {
                        self.emit(I::Lit08);
                        self.emit(0xFF_u8);
                    }
                    Type::U16 => {
                        self.emit(I::Lit16);
                        self.emit(0xFFFF_u16);
                    }
                    Type::U32 => {
                        self.emit(I::Lit32);
                        self.emit(0xFFFF_FFFF_u32);
                    }
                    Type::U64 | Type::Ptr(_) => {
                        self.emit(I::Lit64);
                        self.emit(0xFFFF_FFFF_FFFF_FFFF_u64);
                    }
                    Type::Struct { .. } | Type::Array(_, _) | Type::Slice { .. } => {
                        let size = ret_ty.size_of();
                        for _ in 0..size {
                            self.emit(I::Lit08);
                            self.emit(0xFF_u8);
                        }
                        // OPTIMIZE: this is better for larger arrays
                        // (but it doesn't fill the area with 0xFF)
                        // self.emit(I::GetSp);
                        // self.emit(I::Lit64);
                        // self.emit(size as u64);
                        // self.emit(I::Sub64);
                        // self.emit(I::SetSp);
                    }
                    Type::Func { .. } => unreachable!(),
                }

                // push arguments (in reverse order)
                for arg in args.into_iter().rev() {
                    self.compile_expr(arg)?;
                }

                // push return address
                let cont_addr = self.new_pointer();
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(cont_addr));

                // push BP
                self.emit(I::GetBp);

                // put function address
                // NOTE: This evaluation must be done before renewing the BP.
                self.compile_expr(func)?;

                // set BP
                self.emit(I::GetSp);
                self.emit(I::Lit64);
                self.emit(8_u64);
                self.emit(I::Add64);
                self.emit(I::SetBp);

                // jump to the function
                self.emit(I::Jump);

                //------------------------------------------------------------
                self.emit(Ir::Pointee(cont_addr));

                // [ ret val    ]
                // [ local vars ]
                // -------------- <-- SP
                // [ caller BP  ]
                // [ return IP  ]
                // [ args       ]
                // [ ret val    ]
                // [ ********** ]
                // -------------- <-- BP

                // drop BP, and return addr
                self.emit(I::Drop64);
                self.emit(I::Drop64);

                // drop arguments
                for ty in params_ty.iter() {
                    if ty.size_of() > 0 {
                        self.generate_drop(ty.size_of());
                    }
                }
            }

            Return(e) => {
                let func_ctx = self
                    .func_ctx
                    .as_ref()
                    .expect("return is only allowed in a function body");
                let ret_addr = Ir::Pointer(func_ctx.return_bb_addr);

                self.compile_expr(e)?;
                self.emit(I::Lit64);
                self.emit(ret_addr);
                self.emit(I::Jump);
            }

            If {
                branches,
                else_block,
            } => {
                let old_bb = self.emit_bb;
                let (merge_bb, merge_addr) = self.new_block();

                let mut branch_cond_addr = Vec::new();
                for (cond, block) in branches {
                    let (bb, addr) = self.new_block();

                    self.set_insertion_point(bb);
                    self.compile_expr(block)?;
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(merge_addr));
                    self.emit(I::Jump);

                    branch_cond_addr.push((cond, addr));
                }

                let else_addr = if let Some(else_block) = else_block {
                    let (else_bb, else_addr) = self.new_block();
                    self.set_insertion_point(else_bb);
                    self.compile_expr(else_block)?;
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(merge_addr));
                    self.emit(I::Jump);
                    Some(else_addr)
                } else {
                    None
                };

                self.set_insertion_point(old_bb);

                for (cond, addr) in branch_cond_addr {
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(addr));
                    self.compile_expr(cond)?;
                    self.emit(I::JumpIf);
                }

                if let Some(else_addr) = else_addr {
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(else_addr));
                    self.emit(I::Jump);
                } else {
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(merge_addr));
                    self.emit(I::Jump);
                }

                self.set_insertion_point(merge_bb);
            }

            Loop { body } => {
                let begin = self.new_pointer();
                let cont = self.new_pointer();
                self.loop_ctx.push(LoopContext {
                    begin_of_loop: begin,
                    end_of_loop: cont,
                });
                {
                    self.emit(Ir::Pointee(begin));

                    self.compile_expr(body)?;

                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(begin));
                    self.emit(I::Jump);
                }
                self.loop_ctx.pop();
                self.emit(Ir::Pointee(cont));
            }

            While { cond, body } => {
                let begin = self.new_pointer();
                let cont = self.new_pointer();
                self.loop_ctx.push(LoopContext {
                    begin_of_loop: begin,
                    end_of_loop: cont,
                });

                {
                    self.emit(Ir::Pointee(begin));

                    // jump to cont if cond is not met
                    {
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(cont));

                        // negate
                        self.compile_expr(cond)?;
                        self.emit(I::Lit08);
                        self.emit(0_u8);
                        self.emit(I::Eq08);

                        self.emit(I::JumpIf);
                    }

                    self.compile_expr(body)?;

                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(begin));
                    self.emit(I::Jump);
                }

                self.loop_ctx.pop();
                self.emit(Ir::Pointee(cont));
            }

            For {
                init,
                cond,
                update,
                body,
            } => {
                //--------------------------------------------------------------
                self.env.create_new_scope();

                self.compile_expr(init)?;

                let begin = self.new_pointer();
                let check = self.new_pointer();
                let cont = self.new_pointer();
                self.loop_ctx.push(LoopContext {
                    begin_of_loop: begin,
                    end_of_loop: cont,
                });

                // skip the first evaluation of `update`
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(check));
                self.emit(I::Jump);

                {
                    self.emit(Ir::Pointee(begin));
                    self.compile_expr(update)?;

                    self.emit(Ir::Pointee(check));
                    {
                        self.emit(I::Lit64);
                        self.emit(Ir::Pointer(cont));

                        self.compile_expr(cond)?;
                        self.emit(I::Lit08);
                        self.emit(0_u8);
                        self.emit(I::Eq08);

                        self.emit(I::JumpIf);
                    }

                    self.compile_expr(body)?;

                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(begin));
                    self.emit(I::Jump);
                }

                self.loop_ctx.pop();
                self.emit(Ir::Pointee(cont));

                let scope = self.env.pop_scope().expect("scope unbalanced");
                self.func_ctx.as_mut().unwrap().deallocate(scope.size());
                //--------------------------------------------------------------
            }

            Break => {
                // FIXME: Drop temporal values when getting out of a loop
                // Current implementation possibly lets temporal values remain
                // on the stack, and causes "stack leak".
                // e.g. `loop { loop { f(break, 123) } }`
                // endlessly consumes the stack.

                let cont = match self.loop_ctx.last() {
                    None => todo!("`break` only allowed inside a loop"),
                    Some(lc) => lc.end_of_loop,
                };
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(cont));
                self.emit(I::Jump);
            }
            Continue => {
                // FIXME: Drop temporal values when getting back to the begining.
                let begin = match self.loop_ctx.last() {
                    None => todo!("`continue` only allowed inside a loop"),
                    Some(lc) => lc.begin_of_loop,
                };
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(begin));
                self.emit(I::Jump);
            }

            Let { name, value } => {
                let var_ty = value.ty.clone();
                let var_size = var_ty.size_of();
                let offset = self.func_ctx.as_mut().unwrap().allocate(var_size);

                self.compile_expr(value)?;

                if var_size > 0 {
                    self.emit(I::GetBp);
                    self.emit(I::Lit64);
                    self.emit(offset);
                    self.emit(I::Sub64);
                    self.generate_store(var_size);
                }

                let addr = Addr::BpRel(-(offset as i64));
                self.env.insert(name, addr, var_ty);
            }

            Assignment { location, value } => {
                let ty = value.ty.clone();
                self.compile_expr(value)?;
                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignAdd { location, value } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U08 => {
                        self.emit(I::Load08);
                        self.emit(I::Add08);
                    }
                    Type::U16 => {
                        self.emit(I::Load16);
                        self.emit(I::Add16);
                    }
                    Type::U32 => {
                        self.emit(I::Load32);
                        self.emit(I::Add32);
                    }
                    Type::U64 => {
                        self.emit(I::Load64);
                        self.emit(I::Add64);
                    }
                    _ => todo!(),
                }

                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignSub { location, value } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U08 => {
                        self.emit(I::Load08);
                        self.emit(I::Sub08);
                    }
                    Type::U16 => {
                        self.emit(I::Load16);
                        self.emit(I::Sub16);
                    }
                    Type::U32 => {
                        self.emit(I::Load32);
                        self.emit(I::Sub32);
                    }
                    Type::U64 => {
                        self.emit(I::Load64);
                        self.emit(I::Sub64);
                    }
                    _ => todo!(),
                }

                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignMul { location, value } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U08 => {
                        self.emit(I::Load08);
                        self.emit(I::Mul08);
                    }
                    Type::U16 => {
                        self.emit(I::Load16);
                        self.emit(I::Mul16);
                    }
                    Type::U32 => {
                        self.emit(I::Load32);
                        self.emit(I::Mul32);
                    }
                    Type::U64 => {
                        self.emit(I::Load64);
                        self.emit(I::Mul64);
                    }
                    _ => todo!(),
                }

                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignDiv { location, value } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U08 => {
                        self.emit(I::Load08);
                        self.emit(I::Div08);
                    }
                    Type::U16 => {
                        self.emit(I::Load16);
                        self.emit(I::Div16);
                    }
                    Type::U32 => {
                        self.emit(I::Load32);
                        self.emit(I::Div32);
                    }
                    Type::U64 => {
                        self.emit(I::Load64);
                        self.emit(I::Div64);
                    }
                    _ => todo!(),
                }

                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }

            Block(exprs) => {
                //--------------------------------------------------------------
                self.env.create_new_scope();

                let len = exprs.len();
                for (i, e) in exprs.into_iter().enumerate() {
                    let ty = e.ty.clone();
                    self.compile_expr(e)?;
                    if i + 1 < len && ty.size_of() > 0 {
                        self.generate_drop(ty.size_of());
                    }
                }

                let scope = self.env.pop_scope().expect("scope unbalanced");
                self.func_ctx.as_mut().unwrap().deallocate(scope.size());
                //--------------------------------------------------------------
            }
        }

        Ok(())
    }
}
