use log::debug;
use std::collections::HashMap;

use crate::expr::{Expr, TypedExpr};
use crate::prog::Program;
use crate::ty::Type;
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
    Unresolved(PointerId),
}

struct Compiler {
    bbs: HashMap<BlockId, BasicBlock>,
    emit_bb: BlockId,
    next_bb: BlockId,
    next_ptr_id: PointerId,

    var_addr: HashMap<String, Addr>,
    local_vars_size: u64,
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

            self.var_addr.insert(fun.name, Addr::Unresolved(func_addr));

            let mut old_vars = Vec::new();
            let mut offset = 16;
            for p in fun.params.iter() {
                let addr = Addr::BpRel(offset);
                offset += p.ty.size_of() as i64;

                let old = self.var_addr.insert(p.name.clone(), addr);
                old_vars.push(old);
            }

            self.local_vars_size = 0;
            self.compile_expr(*fun.body);
            let local_vars_size = self.local_vars_size;

            // make space for local variables
            // FIXME
            {
                let old_bb = self.emit_bb;

                let bb = self.bbs.get_mut(&func_bb).unwrap();
                let mut old_buf = std::mem::replace(&mut bb.buf, Vec::new());

                bb.buf.push(old_buf[0]); // pointer
                self.set_insertion_point(func_bb);

                debug!("local_vars_size: {}", local_vars_size);
                let mut r = local_vars_size;
                while r > 0 {
                    if r >= 8 {
                        self.emit(I::Lit64);
                        self.emit(0 as u64);
                        r -= 8;
                    } else if r >= 4 {
                        self.emit(I::Lit32);
                        self.emit(0 as u32);
                        r -= 4;
                    } else if r >= 2 {
                        self.emit(I::Lit16);
                        self.emit(0 as u16);
                        r -= 2;
                    } else {
                        self.emit(I::Lit08);
                        self.emit(0 as u8);
                        r -= 1;
                    }
                }

                let bb = self.bbs.get_mut(&func_bb).unwrap();
                bb.buf.extend(old_buf.drain(1..));

                self.set_insertion_point(old_bb);
            }

            // Return
            {
                // Retrieve the return address
                self.emit(I::GetBp);
                self.emit(I::Lit64);
                self.emit(8 as u64);
                self.emit(I::Add64);
                // Restore BP
                self.emit(I::GetBp);
                self.emit(I::Load64);
                self.emit(I::SetBp);
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
                    }
                    .into(),
                    args: vec![],
                },
                t: Some(Type::U64),
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
                if ty.size_of() > 0 {
                    match self.var_addr.get(&name).copied() {
                        Some(addr) => match addr {
                            Addr::Unresolved(u) => {
                                self.emit(I::Lit64);
                                self.emit(Ir::Pointer(u));
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
                                match expr.t.unwrap() {
                                    Type::Void => unreachable!(),
                                    Type::Bool => self.emit(I::Load08),
                                    Type::U64 => self.emit(I::Load64),
                                    Type::FuncPtr { .. } => self.emit(I::Load64),
                                }
                            }
                        },
                        None => {
                            todo!("undefined variable");
                        }
                    }
                }
            }

            Let {
                name,
                value,
                expr: in_,
            } => {
                let var_ty = value.t.clone().unwrap();
                let var_size = var_ty.size_of() as u64;
                self.local_vars_size += var_size;
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
                        Type::U64 => self.emit(I::Store64),
                        Type::FuncPtr { .. } => self.emit(I::Store64),
                    }
                }

                let addr = Addr::BpRel(-(offset as i64));
                let old = self.var_addr.insert(name.clone(), addr);

                self.compile_expr(*in_);

                if let Some(old) = old {
                    self.var_addr.insert(name, old);
                }
            }

            Add(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Add64),
                }
            }
            Sub(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Sub64),
                }
            }
            Mul(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::FuncPtr { .. } => todo!(),
                    Type::U64 => self.emit(I::Mul64),
                }
            }
            Div(lhs, rhs) => {
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match expr.t.unwrap() {
                    Type::Void | Type::Bool | Type::FuncPtr { .. } => todo!(),
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
                    Type::U64 | Type::FuncPtr { .. } => self.emit(I::Eq64),
                }
            }
            Lt(lhs, rhs) => {
                let ty = lhs.t.clone().unwrap();
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match ty {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Lt08),
                    Type::U64 | Type::FuncPtr { .. } => self.emit(I::Lt64),
                }
            }
            Gt(lhs, rhs) => {
                let ty = lhs.t.clone().unwrap();
                self.compile_expr(*lhs);
                self.compile_expr(*rhs);
                match ty {
                    Type::Void => todo!("void comp"),
                    Type::Bool => self.emit(I::Gt08),
                    Type::U64 | Type::FuncPtr { .. } => self.emit(I::Gt64),
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
                    Type::U64 | Type::FuncPtr { .. } => {
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

                self.emit(Ir::Pointee(cont_addr));

                // save the return value
                if ret_ty.size_of() > 0 {
                    let ret_val_size = ret_ty.size_of() as u64;
                    let args_size: u64 = params_ty.iter().map(|p| p.size_of() as u64).sum();
                    let ret_val_offset: u64 =
                        args_size + 8 /* return addr */ + 8 /* old BP */ + ret_val_size;
                    self.emit(I::GetSp);
                    self.emit(I::Lit64);
                    self.emit(ret_val_offset);
                    self.emit(I::Add64);

                    match ret_ty {
                        Type::Void => unreachable!(),
                        Type::Bool => self.emit(I::Store08),
                        Type::U64 => self.emit(I::Store64),
                        Type::FuncPtr { .. } => self.emit(I::Store64),
                    }
                }

                // drop BP, and return addr
                self.emit(I::Drop64);
                self.emit(I::Drop64);

                // drop arguments
                for ty in params_ty.iter() {
                    match ty {
                        Type::Void => {}
                        Type::Bool => self.emit(I::Drop08),
                        Type::U64 => self.emit(I::Drop64),
                        Type::FuncPtr { .. } => self.emit(I::Drop64),
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

            Block(exprs, is_void) => {
                let len = exprs.len();
                for (i, e) in exprs.into_iter().enumerate() {
                    let ty = e.t.clone().unwrap();
                    self.compile_expr(e);
                    if is_void || i + 1 < len {
                        match ty {
                            Type::Void => {}
                            Type::Bool => self.emit(I::Drop08),
                            Type::U64 | Type::FuncPtr { .. } => self.emit(I::Drop64),
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
