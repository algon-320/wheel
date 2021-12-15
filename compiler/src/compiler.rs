use log::debug;
use std::collections::HashMap;
type Stack<T> = std::vec::Vec<T>;

use crate::expr::{Expr, TypedExpr};
use crate::prog::Program;
use crate::ty::{Category, Type};
use spec::Instruction as I;

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
impl_from! {I,  OpCode}
impl_from! {u8,  Data08}
impl_from! {u16, Data16}
impl_from! {u32, Data32}
impl_from! {u64, Data64}

impl Into<Vec<u8>> for Ir {
    fn into(self) -> Vec<u8> {
        use Ir::*;
        match self {
            OpCode(op) => vec![op.into()],
            Data08(x) => vec![x],
            Data16(x) => x.to_le_bytes().to_vec(),
            Data32(x) => x.to_le_bytes().to_vec(),
            Data64(x) => x.to_le_bytes().to_vec(),
            Pointer(_) => 0xAAAAAAAAAAAAAAAAu64.to_le_bytes().to_vec(),
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
    Function(PointerId),
}

struct LoopContext {
    end_of_loop: PointerId,
}

struct Compiler {
    bbs: HashMap<BlockId, BasicBlock>,
    emit_bb: BlockId,
    next_bb: BlockId,
    next_ptr_id: PointerId,

    var_addr: HashMap<String, Addr>,
    local_vars_size: u64,
    local_vars_size_max: u64,
    loop_context: Stack<LoopContext>,
}

impl Compiler {
    fn new() -> Self {
        Self {
            bbs: HashMap::new(),
            emit_bb: BlockId(0),
            next_bb: BlockId(1),
            next_ptr_id: PointerId(1),
            var_addr: HashMap::new(),
            local_vars_size: 0,
            local_vars_size_max: 0,
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

    fn compile(mut self, prog: Program) -> Vec<u8> {
        for fun in prog.functions {
            let (func_bb, func_addr) = self.new_block();
            self.set_insertion_point(func_bb);

            self.var_addr.insert(fun.name, Addr::Function(func_addr));

            let mut old_vars = Vec::new();
            let mut offset = 16;
            for p in fun.params.iter() {
                let addr = Addr::BpRel(offset);
                offset += p.ty.size_of() as i64;

                let old = self.var_addr.insert(p.name.clone(), addr);
                old_vars.push(old);
            }

            self.local_vars_size = 0;
            self.local_vars_size_max = 0;
            self.compile_expr(*fun.body);
            let local_vars_size = self.local_vars_size_max;
            debug!("local_vars_size: {}", local_vars_size);

            // make space for local variables
            // FIXME
            {
                let old_bb = self.emit_bb;

                let bb = self.bbs.get_mut(&func_bb).unwrap();
                let mut old_buf = std::mem::replace(&mut bb.buf, Vec::new());

                bb.buf.push(old_buf[0]); // pointer
                self.set_insertion_point(func_bb);
                {
                    // SP = SP - local_vars_size
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(local_vars_size as u64);
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
                    let args_size: u64 = fun.params.iter().map(|p| p.ty.size_of() as u64).sum();
                    let ret_val_offset = 8/* caller BP */ + 8/* return IP */ + args_size;
                    self.emit(I::GetBp);
                    self.emit(I::Lit64);
                    self.emit(ret_val_offset as u64);
                    self.emit(I::Add64);
                    match ret_ty {
                        Type::Void => unreachable!(),
                        Type::Bool => self.emit(I::Store08),
                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Store64),
                    }
                }

                // Drop local variables (and temporal values)
                self.emit(I::GetBp);
                self.emit(I::SetSp);

                // Retrieve the return address
                self.emit(I::GetBp);
                self.emit(I::Lit64);
                self.emit(8 as u64);
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

            for (p, old) in fun.params.iter().zip(old_vars.into_iter()) {
                if let Some(old) = old {
                    self.var_addr.insert(p.name.clone(), old);
                }
            }
        }

        let (entry_point, _) = self.new_block();
        self.set_insertion_point(entry_point);
        {
            // FIXME
            use Expr::*;
            self.compile_expr(TypedExpr {
                e: Call {
                    func: TypedExpr {
                        e: Var("main".into()).into(),
                        t: Some(Type::FuncPtr {
                            params: vec![],
                            ret_ty: Type::U64.into(),
                        }),
                        c: Some(Category::Regular),
                    }
                    .into(),
                    args: vec![],
                },
                t: Some(Type::U64),
                c: Some(Category::Regular),
            });
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
                            let pos = unresolved.entry(ptr_id).or_insert_with(|| Vec::new());
                            pos.push(text.len());
                        }
                        Ir::Pointee(ptr_id) => {
                            debug!("pointee {:?} ==> {}", ptr_id, text.len());
                            pointees.insert(ptr_id, text.len());
                        }
                        _ => {}
                    }
                    let bytes: Vec<u8> = e.into();
                    text.extend(bytes);
                }
            };

            let entry = self.bbs.remove(&entry_point).unwrap();
            compile_basic_block(entry_point, entry);

            for (id, bs) in self.bbs {
                compile_basic_block(id, bs);
            }

            for (id, pos) in unresolved {
                let bytes = pointees[&id].to_le_bytes();
                for p in pos {
                    for (i, &b) in bytes.iter().enumerate() {
                        debug_assert_eq!(text[p + i], 0xAA);
                        text[p + i] = b;
                    }
                }
            }
        }
        text
    }

    fn compile_expr(&mut self, expr: TypedExpr) {
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

            Var(name) => {
                let ty = expr.t.as_ref().unwrap();
                let cat = expr.c.unwrap();
                if ty.size_of() > 0 {
                    match self.var_addr.get(&name).copied() {
                        Some(addr) => match addr {
                            Addr::BpRel(offset) => {
                                self.emit(I::GetBp);
                                self.emit(I::Lit64);
                                self.emit(offset.abs() as u64);
                                if offset > 0 {
                                    self.emit(I::Add64); // function argument
                                } else {
                                    self.emit(I::Sub64); // local variable
                                }

                                if cat == Category::Regular {
                                    match expr.t.unwrap() {
                                        Type::Void => unreachable!(),
                                        Type::Bool => self.emit(I::Load08),
                                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => {
                                            self.emit(I::Load64)
                                        }
                                    }
                                }
                            }
                            Addr::Function(p) => {
                                if cat == Category::Regular {
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
            }

            AddrOf(location) => {
                self.compile_expr(*location);
            }

            PtrDeref(ptr) => {
                self.compile_expr(*ptr);
                if expr.c.unwrap() == Category::Regular {
                    match expr.t.unwrap() {
                        Type::Void => todo!("deref of *()"),
                        Type::Bool => self.emit(I::Load08),
                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Load64),
                    }
                }
            }

            Add(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::Ptr(_) | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Add64),
                }
            }
            Sub(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::Ptr(_) | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Sub64),
                }
            }
            Mul(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::Ptr(_) | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Mul64),
                }
            }
            Div(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::Ptr(_) | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Div64),
                }
            }

            Eq(lhs, rhs) => {
                let ty = lhs.t.clone().unwrap();
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match ty {
                    Type::Void => {
                        // Always true
                        self.emit(I::Lit08);
                        self.emit(1 as u8);
                    }
                    Type::Bool => self.emit(I::Eq08),
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Eq64),
                }
            }
            Lt(lhs, rhs) => {
                let ty = lhs.t.clone().unwrap();
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match ty {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Lt08),
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Lt64),
                }
            }
            Gt(lhs, rhs) => {
                let ty = lhs.t.clone().unwrap();
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match ty {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Gt08),
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Gt64),
                }
            }

            LNot(e) => {
                // top == 0
                self.compile_expr(*e);
                self.emit(I::Lit08);
                self.emit(0 as u8);
                self.emit(I::Eq08);
            }
            Neq(lhs, rhs) => {
                // Eq(lhs, rhs) == 0
                self.compile_expr(TypedExpr {
                    e: Eq(lhs, rhs),
                    t: expr.t,
                    c: Some(Category::Regular),
                });
                self.emit(I::Lit08);
                self.emit(0 as u8);
                self.emit(I::Eq08);
            }
            Leq(lhs, rhs) => {
                // Gt(lhs, rhs) == 0
                self.compile_expr(TypedExpr {
                    e: Gt(lhs, rhs),
                    t: expr.t,
                    c: Some(Category::Regular),
                });
                self.emit(I::Lit08);
                self.emit(0 as u8);
                self.emit(I::Eq08);
            }
            Geq(lhs, rhs) => {
                // Lt(lhs, rhs) == 0
                self.compile_expr(TypedExpr {
                    e: Lt(lhs, rhs),
                    t: expr.t,
                    c: Some(Category::Regular),
                });
                self.emit(I::Lit08);
                self.emit(0 as u8);
                self.emit(I::Eq08);
            }
            LAnd(lhs, rhs) => {
                assert_eq!(lhs.t.as_ref(), Some(&Type::Bool));
                assert_eq!(rhs.t.as_ref(), Some(&Type::Bool));
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                self.emit(I::Mul08);
            }
            LOr(lhs, rhs) => {
                assert_eq!(lhs.t.as_ref(), Some(&Type::Bool));
                assert_eq!(rhs.t.as_ref(), Some(&Type::Bool));
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);

                // lhs + rhs > 0
                self.emit(I::Add08);
                self.emit(I::Lit08);
                self.emit(0 as u8);
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

                let fun_ty = func.t.clone().unwrap();
                let (params_ty, ret_ty) = match fun_ty {
                    Type::FuncPtr { params, ret_ty } => (params, *ret_ty),
                    _ => unreachable!(),
                };

                // make a space for the return value
                match &ret_ty {
                    Type::Void => {}
                    Type::Bool => {
                        self.emit(I::Lit08);
                        self.emit(0xFF as u8);
                    }
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => {
                        self.emit(I::Lit64);
                        self.emit(0xFFFF_FFFF_FFFF_FFFF as u64);
                    }
                }

                // push arguments (in reverse order)
                for arg in args.into_iter().rev() {
                    self.compile_expr(arg);
                }

                // push return address
                let cont_addr = self.new_pointer();
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(cont_addr));

                // push BP
                self.emit(I::GetBp);

                // put function address
                // NOTE: This evaluation must be done before renewing the BP.
                self.compile_expr(*func);

                // set BP
                self.emit(I::GetSp);
                self.emit(I::Lit64);
                self.emit(8 as u64);
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
                    match ty {
                        Type::Void => {}
                        Type::Bool => self.emit(I::Drop08),
                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Drop64),
                    }
                }
            }

            If {
                cond,
                then_expr,
                else_expr,
            } => {
                let old_bb = self.emit_bb;

                let (merge_bb, merge_addr) = self.new_block();
                let (then_bb, then_addr) = self.new_block();
                let (else_bb, else_addr) = self.new_block();

                self.set_insertion_point(then_bb);
                self.compile_expr(*then_expr);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(merge_addr));
                self.emit(I::Jump);

                self.set_insertion_point(else_bb);
                self.compile_expr(*else_expr);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(merge_addr));
                self.emit(I::Jump);

                self.set_insertion_point(old_bb);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(then_addr));
                self.compile_expr(*cond);
                self.emit(I::JumpIf);
                self.emit(I::Lit64);
                self.emit(Ir::Pointer(else_addr));
                self.emit(I::Jump);

                self.set_insertion_point(merge_bb);
            }

            Loop { body } => {
                let cont = self.new_pointer();
                self.loop_context.push(LoopContext { end_of_loop: cont });
                {
                    let begin = self.new_pointer();
                    self.emit(Ir::Pointee(begin));

                    self.compile_expr(*body);

                    self.emit(I::Lit64);
                    self.emit(Ir::Pointer(begin));
                    self.emit(I::Jump);
                }
                self.loop_context.pop();
                self.emit(Ir::Pointee(cont));
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

            Let {
                name,
                value,
                expr: in_,
            } => {
                let var_ty = value.t.clone().unwrap();
                let var_size = var_ty.size_of() as u64;
                self.local_vars_size += var_size;
                self.local_vars_size_max =
                    std::cmp::max(self.local_vars_size_max, self.local_vars_size);
                let offset = self.local_vars_size;

                self.compile_expr(*value);

                if var_size > 0 {
                    self.emit(I::GetBp);
                    self.emit(I::Lit64);
                    self.emit(offset);
                    self.emit(I::Sub64);
                    match var_ty {
                        Type::Void => unreachable!(),
                        Type::Bool => self.emit(I::Store08),
                        Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Store64),
                    }
                }

                let addr = Addr::BpRel(-(offset as i64));
                let old = self.var_addr.insert(name.clone(), addr);

                self.compile_expr(*in_);

                if let Some(old) = old {
                    self.var_addr.insert(name, old);
                }

                self.local_vars_size -= var_size;
            }

            Assignment { location, value } => {
                let ty = value.t.clone().unwrap();
                self.compile_expr(*value);
                self.compile_expr(*location);
                match ty {
                    Type::Void => {}
                    Type::Bool => self.emit(I::Store08),
                    Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Store64),
                }
            }

            Block(exprs, is_void) => {
                let len = exprs.len();
                for (i, e) in exprs.into_iter().enumerate() {
                    let ty = e.t.clone().unwrap();
                    self.compile_expr(e);
                    if is_void || i + 1 < len {
                        match ty {
                            Type::Void => {}
                            Type::Bool => self.emit(I::Drop08),
                            Type::U64 | Type::Ptr(_) | Type::FuncPtr { .. } => self.emit(I::Drop64),
                        }
                    }
                }
            }
        }
    }
}

pub fn compile(prog: Program) -> Vec<u8> {
    Compiler::new().compile(prog)
}
