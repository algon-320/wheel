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
    Function(PointerId),
    BpRel(i64),
    Data(PointerId),
    ArrayBpRel(i64),
    ArrayData(PointerId),
}

struct FunctionContext {
    stack_cursor: u64,
    required_memory: u64,
}
impl FunctionContext {
    fn new() -> Self {
        Self {
            stack_cursor: 0,
            required_memory: 0,
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
    dict: HashMap<String, Addr>,
    size: u64,
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
            size: 0,
        });
    }
    pub fn pop_scope(&mut self) -> Option<Scope> {
        let scope = self.scopes.pop()?;
        Some(scope)
    }

    pub fn insert(&mut self, name: String, addr: Addr, size: u64) {
        let scope = &mut self.scopes.last_mut().unwrap();
        scope.size += size;

        let old = scope.dict.insert(name.clone(), addr);
        if old.is_some() {
            log::warn!("variable shadowed: {}", name);
        }
    }

    pub fn get(&self, var_name: &str) -> Option<Addr> {
        for scope in self.scopes.iter().rev() {
            if let Some(&addr) = scope.dict.get(var_name) {
                return Some(addr);
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

        let mut c = Self {
            debug,

            bbs: HashMap::new(),
            emit_bb: BlockId(0),
            next_bb: BlockId(0),
            next_ptr_id: PointerId(1),

            entry_point_bb: BlockId(0),
            static_data_bb: BlockId(0),

            env,
            struct_layout: HashMap::new(),
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
        let addr = if ty.is_array() {
            Addr::ArrayData(data_location)
        } else {
            Addr::Data(data_location)
        };
        self.env.insert(data.name, addr, ty.size_of() as u64);

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
        self.set_insertion_point(func_bb);

        self.env.insert(fun.name, Addr::Function(func_addr), 0);

        //----------------------------------------------------------------------
        // create a scope for parameter
        self.env.create_new_scope();

        let mut offset = 16; // return IP + caller BP
        for p in fun.params.iter() {
            let addr = if p.ty.is_array() {
                Addr::ArrayBpRel(offset)
            } else {
                Addr::BpRel(offset)
            };

            let size = p.ty.size_of() as u64;
            self.env.insert(p.name.clone(), addr, size);
            offset += size as i64;
        }

        self.func_ctx = Some(FunctionContext::new());
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
            LiteralU64(v) => {
                self.emit(I::Lit64);
                self.emit(v);
            }

            LiteralArray(elems) => {
                for e in elems.into_iter().rev() {
                    self.compile_expr(e)?;
                }
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

            Var(_) if expr_ty.size_of() == 0 => {}
            Var(name) => {
                match self.env.get(&name) {
                    Some(addr) => match addr {
                        Addr::Data(location) => {
                            self.emit(I::Lit64);
                            self.emit(Ir::Pointer(location));
                            if expr_cat == Category::Regular {
                                self.generate_load(expr_ty.size_of());
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
                            if expr_cat == Category::Regular {
                                self.generate_load(expr_ty.size_of());
                            }
                        }

                        Addr::ArrayData(location) => {
                            if expr_cat == Category::Regular {
                                self.emit(I::Lit64);
                                self.emit(Ir::Pointer(location));
                            } else {
                                todo!("array itself cannot be a location expression");
                            }
                        }

                        Addr::ArrayBpRel(offset) => {
                            if expr_cat == Category::Regular {
                                self.emit(I::GetBp);
                                self.emit(I::Lit64);
                                self.emit(offset.abs() as u64);
                                if offset > 0 {
                                    self.emit(I::Add64); // function argument
                                } else {
                                    self.emit(I::Sub64); // local variable
                                }
                            } else {
                                todo!("array itself cannot be a location expression");
                            }
                        }

                        Addr::Function(p) => {
                            if expr_cat == Category::Regular {
                                self.emit(I::Lit64);
                                self.emit(Ir::Pointer(p));
                            } else {
                                todo!("function cannot be a location expression");
                            }
                        }
                    },
                    None => {
                        todo!("undefined variable");
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

            ArrayAccess { ptr, idx } => {
                self.compile_expr(ptr)?;

                // ptr + idx * sizeof(ty)
                self.compile_expr(idx)?;
                self.emit(I::Lit64);
                self.emit(expr_ty.size_of());
                self.emit(I::Mul64);
                self.emit(I::Add64);

                if expr_cat == Category::Regular {
                    assert_ne!(expr_ty.0, Type::Void, "deref of *()");
                    self.generate_load(expr_ty.size_of());
                }
            }

            MemberAccess { obj, field } => {
                let obj_ty = obj.ty.clone();
                let obj_cat = obj.cat;

                // TODO: avoid redundant laod
                self.compile_expr(obj)?;

                let layout = match &obj_ty.0 {
                    Type::Struct { name, .. } => &self.struct_layout[name],
                    _ => todo!("member access for non-struct value"),
                };
                let offset = layout[&field];

                if obj_cat == Category::Location {
                    self.emit(I::Lit64);
                    self.emit(offset);
                    self.emit(I::Add64);
                } else if obj_cat == Category::Regular {
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

            Add(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
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
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
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
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
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
                    | Type::Struct { .. }
                    | Type::Ptr(_) => todo!(),
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
                    Type::Array(_, _) => todo!("array comparison"),
                    Type::Struct { .. } => todo!("struct comparison"),
                    Type::U64 | Type::Ptr(_) => self.emit(I::Eq64),
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
                    Type::Array(_, _) => todo!("array comparison"),
                    Type::Struct { .. } => todo!("struct comparison"),
                    Type::U64 | Type::Ptr(_) => self.emit(I::Lt64),
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
                    Type::Array(_, _) => todo!("array comparison"),
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
                    Type::U64 | Type::Ptr(_) => {
                        self.emit(I::Lit64);
                        self.emit(0xFFFF_FFFF_FFFF_FFFF_u64);
                    }
                    Type::Struct { .. } | Type::Array(_, _) => {
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
                    match ty.0 {
                        Type::Void => {}
                        Type::Bool => self.emit(I::Drop08),
                        Type::U64 | Type::Ptr(_) => self.emit(I::Drop64),
                        Type::Struct { .. } | Type::Array(_, _) => {
                            self.generate_drop(ty.size_of());
                        }
                        Type::Func { .. } => unreachable!(),
                    }
                }
            }

            If {
                cond,
                then_expr,
                else_expr: Some(else_expr),
            } => {
                let old_bb = self.emit_bb;

                let (merge_bb, merge_addr) = self.new_block();
                let (then_bb, then_addr) = self.new_block();
                let (else_bb, else_addr) = self.new_block();

                self.set_insertion_point(then_bb);
                self.compile_expr(then_expr)?;
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(merge_addr));
                self.emit(I::Jump);

                self.set_insertion_point(else_bb);
                self.compile_expr(else_expr)?;
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(merge_addr));
                self.emit(I::Jump);

                self.set_insertion_point(old_bb);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(then_addr));
                self.compile_expr(cond)?;
                self.emit(I::JumpIf);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(else_addr));
                self.emit(I::Jump);

                self.set_insertion_point(merge_bb);
            }

            If {
                cond,
                then_expr,
                else_expr: None,
            } => {
                let old_bb = self.emit_bb;

                let merge_addr = self.new_pointer();
                let (then_bb, then_addr) = self.new_block();

                self.set_insertion_point(then_bb);
                self.compile_expr(then_expr)?;
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(merge_addr));
                self.emit(I::Jump);

                self.set_insertion_point(old_bb);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(then_addr));
                self.compile_expr(cond)?;
                self.emit(I::JumpIf);

                self.emit(Ir::Pointee(merge_addr));
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
                self.func_ctx.as_mut().unwrap().deallocate(scope.size);
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
                    self.generate_store(var_ty.size_of());
                }

                let addr = if var_ty.is_array() {
                    Addr::ArrayBpRel(-(offset as i64))
                } else {
                    Addr::BpRel(-(offset as i64))
                };
                self.env.insert(name, addr, var_size);
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
                    if i + 1 < len {
                        match ty.0 {
                            Type::Void => {}
                            Type::Bool => self.emit(I::Drop08),
                            Type::U64 | Type::Ptr(_) => self.emit(I::Drop64),
                            Type::Struct { .. } | Type::Array(_, _) => {
                                self.generate_drop(ty.size_of());
                            }
                            Type::Func { .. } => unimplemented!(),
                        }
                    }
                }

                let scope = self.env.pop_scope().expect("scope unbalanced");
                self.func_ctx.as_mut().unwrap().deallocate(scope.size);
                //--------------------------------------------------------------
            }
        }

        Ok(())
    }
}
