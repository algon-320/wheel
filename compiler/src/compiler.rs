use log::debug;
use std::collections::HashMap;
type Stack<T> = std::vec::Vec<T>;

use crate::ast::{DataDef, Def, Expr, FuncDef, Program};
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

#[derive(Debug, Clone, Copy)]
enum Ir {
    OpCode(I),
    Data08(u8),
    Data16(u16),
    Data32(u32),
    Data64(u64),
    Pointer(PointerId),
    Pointee(PointerId),
}
macro_rules! impl_from {
    ($t:ty, $var:ident) => {
        impl From<$t> for Ir {
            fn from(x: $t) -> Self {
                Self::$var(x)
            }
        }
    };
}
impl_from! {I,   OpCode}
impl_from! {u8,  Data08}
impl_from! {u16, Data16}
impl_from! {u32, Data32}
impl_from! {u64, Data64}

impl From<Ir> for Vec<u8> {
    fn from(ir: Ir) -> Vec<u8> {
        use Ir::*;
        match ir {
            OpCode(op) => vec![op.into()],
            Data08(x) => vec![x],
            Data16(x) => x.to_le_bytes().to_vec(),
            Data32(x) => x.to_le_bytes().to_vec(),
            Data64(x) => x.to_le_bytes().to_vec(),
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

#[derive(Debug, Clone)]
struct StaticData {
    data_location: PointerId,
    ty: ResolvedType,
    initializer_name: String,
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
    stack: Stack<Scope>,
    mem_cur: u64,
    mem_max: u64,
}
impl Environment {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
            mem_cur: 0,
            mem_max: 0,
        }
    }

    pub fn create_new_scope(&mut self) {
        self.stack.push(Scope {
            dict: HashMap::new(),
            size: 0,
        });
    }
    pub fn pop_scope(&mut self) -> Option<Scope> {
        let scope = self.stack.pop()?;
        self.mem_cur -= scope.size;
        Some(scope)
    }

    pub fn insert(&mut self, name: String, addr: Addr, size: Option<u64>) {
        let scope = &mut self.stack.last_mut().unwrap();

        scope.size += size.unwrap_or(0);
        self.mem_cur += size.unwrap_or(0);
        self.mem_max = std::cmp::max(self.mem_max, self.mem_cur);

        let old = scope.dict.insert(name.clone(), addr);
        if old.is_some() {
            log::warn!("variable shadowed: {}", name);
        }
    }

    pub fn get(&self, var_name: &str) -> Option<Addr> {
        for scope in self.stack.iter().rev() {
            if let Some(&addr) = scope.dict.get(var_name) {
                return Some(addr);
            }
        }
        None
    }
}

struct Compiler {
    bbs: HashMap<BlockId, BasicBlock>,
    emit_bb: BlockId,
    next_bb: BlockId,
    next_ptr_id: PointerId,

    env: Environment,
    static_data: Vec<StaticData>,
    loop_context: Stack<LoopContext>,
}

impl Compiler {
    fn new() -> Self {
        let mut env = Environment::new();
        env.create_new_scope();

        Self {
            bbs: HashMap::new(),
            emit_bb: BlockId(0),
            next_bb: BlockId(1),
            next_ptr_id: PointerId(1),
            env,
            static_data: Vec::new(),
            loop_context: Stack::new(),
        }
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

    fn generate_function_call_no_arg(
        &mut self,
        name: String,
        ret_ty: ResolvedType,
    ) -> Result<(), Error> {
        use Expr::*;
        let func = TypedExpr {
            e: Var(name),
            ty: Type::FuncPtr {
                params: vec![],
                ret_ty: ret_ty.clone().into(),
            }
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
                    self.emit(I::SetSp);
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
                    self.emit(I::Lit64);
                    self.emit(8_u64);
                    self.emit(I::Add64);
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

                self.emit(I::Drop64); // src
                if size < 8 {
                    self.generate_drop(8 - size);
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

    fn compile(mut self, prog: Program<TypedExpr, ResolvedType>) -> Result<Vec<u8>, Error> {
        for def in prog.defs {
            match def {
                Def::Data(data) => {
                    self.compile_static_data(data)?;
                }
                Def::Func(fun) => {
                    self.compile_function(fun)?;
                }
            }
        }

        let static_data = self.static_data.clone();

        let (entry_point, _) = self.new_block();
        {
            self.set_insertion_point(entry_point);

            // Initialize static data
            for sd in static_data.iter() {
                // Call initializer
                let ret_ty = sd.ty.clone();
                let name = sd.initializer_name.clone();
                self.generate_function_call_no_arg(name, ret_ty)?;

                // Store the returned value at the data location
                if sd.ty.size_of() > 0 {
                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(sd.data_location));
                    self.generate_store(sd.ty.size_of());
                }
            }

            // Call the main
            self.generate_function_call_no_arg("main".to_owned(), Type::U64.into())?; // FIXME: return type
            self.emit(I::Abort);
        }

        // Make space for static data
        let (data_bb, _) = self.new_block();
        self.set_insertion_point(data_bb);
        for sd in static_data {
            self.emit(Ir::Pointee(sd.data_location));
            let size = sd.ty.size_of();
            for _ in 0..size {
                // NOTE: the value 0xBB is meaningless (just for ease of debuging)
                self.emit(Ir::Data08(0xBB));
            }
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

            let entry = self.bbs.remove(&entry_point).unwrap();
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
        self.env.insert(data.name, addr, None);

        self.static_data.push(StaticData {
            data_location,
            ty,
            initializer_name,
        });

        Ok(())
    }

    fn compile_function(&mut self, fun: FuncDef<TypedExpr, ResolvedType>) -> Result<(), Error> {
        let (func_bb, func_addr) = self.new_block();
        self.set_insertion_point(func_bb);

        self.env.insert(fun.name, Addr::Function(func_addr), None);

        //----------------------------------------------------------------------
        // create a scope for parameter
        self.env.create_new_scope();

        let mut offset = 16;
        for p in fun.params.iter() {
            let addr = if p.ty.is_array() {
                Addr::ArrayBpRel(offset)
            } else {
                Addr::BpRel(offset)
            };

            self.env.insert(p.name.clone(), addr, None);
            offset += p.ty.size_of() as i64;
        }

        self.env.mem_max = 0;
        self.env.mem_cur = 0;

        self.compile_expr(fun.body)?;

        let local_vars_size = self.env.mem_max;

        self.env.pop_scope().expect("scope unbalanced");
        //----------------------------------------------------------------------

        debug!("local_vars_size: {}", local_vars_size);

        // make space for local variables
        // FIXME
        {
            let old_bb = self.emit_bb;

            let bb = self.bbs.get_mut(&func_bb).unwrap();
            let mut old_buf = std::mem::take(&mut bb.buf);

            bb.buf.push(old_buf[0]); // pointer
            self.set_insertion_point(func_bb);
            {
                // SP = SP - local_vars_size
                self.emit(I::GetSp);
                self.emit(I::Lit64);
                self.emit(local_vars_size);
                self.emit(I::Sub64);
                self.emit(I::SetSp);

                let bb = self.bbs.get_mut(&func_bb).unwrap();
                bb.buf.extend(old_buf.drain(1..));
            }
            self.set_insertion_point(old_bb);
        }

        // Return
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
            // Jump to the caller
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

            Add(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Ptr(_)
                    | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Add64),
                }
            }
            Sub(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Ptr(_)
                    | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Sub64),
                }
            }
            Mul(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Ptr(_)
                    | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Mul64),
                }
            }
            Div(lhs, rhs) => {
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                match expr_ty.0 {
                    Type::Void
                    | Type::Bool
                    | Type::Array(_, _)
                    | Type::Ptr(_)
                    | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Div64),
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
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Eq64),
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
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Lt64),
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
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Gt64),
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
                    Type::FuncPtr { params, ret_ty } => (params, *ret_ty),
                    _ => unreachable!(),
                };

                // make a space for the return value
                match &ret_ty.0 {
                    Type::Void => {}
                    Type::Bool => {
                        self.emit(I::Lit08);
                        self.emit(0xFF_u8);
                    }
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => {
                        self.emit(I::Lit64);
                        self.emit(0xFFFF_FFFF_FFFF_FFFF_u64);
                    }
                    Type::Array(_, _) => {
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
                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Drop64),
                        Type::Array(_, _) => {
                            self.generate_drop(ty.size_of());
                        }
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
                self.loop_context.push(LoopContext {
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
                self.loop_context.pop();
                self.emit(Ir::Pointee(cont));
            }

            While { cond, body } => {
                let begin = self.new_pointer();
                let cont = self.new_pointer();
                self.loop_context.push(LoopContext {
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

                self.loop_context.pop();
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
                self.loop_context.push(LoopContext {
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

                self.loop_context.pop();
                self.emit(Ir::Pointee(cont));

                self.env.pop_scope().expect("scope unbalanced");
                //--------------------------------------------------------------
            }

            Break => {
                // FIXME: Drop temporal values when getting out of a loop
                // Current implementation possibly lets temporal values remain
                // on the stack, and causes "stack leak".
                // e.g. `loop { loop { f(break, 123) } }`
                // endlessly consumes the stack.

                let cont = match self.loop_context.last() {
                    None => todo!("`break` only allowed inside a loop"),
                    Some(lc) => lc.end_of_loop,
                };
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(cont));
                self.emit(I::Jump);
            }
            Continue => {
                // FIXME: Drop temporal values when getting back to the begining.
                let begin = match self.loop_context.last() {
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
                let offset = self.env.mem_cur + var_size;

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
                self.env.insert(name, addr, Some(var_size));
            }

            Assignment { location, value } => {
                let ty = value.ty.clone();
                self.compile_expr(value)?;
                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignAdd {
                mut location,
                value,
            } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                location.cat = Category::Regular;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U64 => self.emit(I::Add64),
                    _ => todo!(),
                }

                location.cat = Category::Location;
                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignSub {
                mut location,
                value,
            } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                location.cat = Category::Regular;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U64 => self.emit(I::Sub64),
                    _ => todo!(),
                }

                location.cat = Category::Location;
                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignMul {
                mut location,
                value,
            } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                location.cat = Category::Regular;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U64 => self.emit(I::Mul64),
                    _ => todo!(),
                }

                location.cat = Category::Location;
                self.compile_expr(location)?;
                if ty.size_of() > 0 {
                    self.generate_store(ty.size_of());
                }
            }
            AssignDiv {
                mut location,
                value,
            } => {
                assert_eq!(location.cat, Category::Location);
                let ty = value.ty.clone();

                self.compile_expr(value)?;
                location.cat = Category::Regular;
                self.compile_expr(location.clone())?;
                match ty.0 {
                    Type::U64 => self.emit(I::Div64),
                    _ => todo!(),
                }

                location.cat = Category::Location;
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
                            Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Drop64),
                            Type::Array(_, _) => {
                                self.generate_drop(ty.size_of());
                            }
                        }
                    }
                }

                self.env.pop_scope().expect("scope unbalanced");
                //--------------------------------------------------------------
            }
        }

        Ok(())
    }
}

pub fn compile(prog: Program<TypedExpr, ResolvedType>) -> Vec<u8> {
    Compiler::new().compile(prog).expect("compilation error")
}
