use crate::error::Error;
use crate::expr::{Expr, ExprTag, E};
use crate::parser::Parsed;
use crate::prog::{DataDef, Def, FuncDef, Program};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Void,
    Bool,
    U64,
    Array(Box<Type>, usize),
    Ptr(Box<Type>),
    FuncPtr {
        params: Vec<Type>,
        ret_ty: Box<Type>,
    },
}

impl Type {
    pub fn size_of(&self) -> u64 {
        match self {
            Type::Void => 0,
            Type::Bool => 1,
            Type::U64 => 8,
            Type::Array(elem, len) => elem.size_of() * (*len as u64),
            Type::Ptr(_) | Type::FuncPtr { .. } => 8,
        }
    }
    pub fn is_array(&self) -> bool {
        matches!(self, Type::Array(_, _))
    }
}

fn assert_type_eq(ty: &Type, expect: &Type) -> Result<(), Error> {
    if ty != expect {
        Err(Error::TypeMismatch {
            expect: Some(expect.clone()),
            actual: ty.clone(),
        })
    } else {
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Category {
    Location,
    Regular,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Typed {
    pub ty: Type,
    pub cat: Category,
}
impl ExprTag for Typed {}

impl Expr<Typed> {
    pub fn ty(&self) -> &Type {
        &self.tag.ty
    }

    pub fn cat(&self) -> Category {
        self.tag.cat
    }
}

type BinCtor = fn(Box<Expr<Typed>>, Box<Expr<Typed>>) -> E<Typed>;

use std::collections::HashMap;
struct TypeEnv {
    stack: Vec<HashMap<String, Type>>,
}
impl TypeEnv {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn create_new_scope(&mut self) {
        self.stack.push(HashMap::new());
    }
    pub fn pop_scope(&mut self) {
        self.stack.pop();
    }

    pub fn insert(&mut self, name: String, ty: Type) {
        let dict = &mut self.stack.last_mut().unwrap();
        let old = dict.insert(name.clone(), ty);
        if old.is_some() {
            log::warn!("variable shadowed: {}", name);
        }
    }

    pub fn get(&self, var_name: &str) -> Option<&Type> {
        for scope in self.stack.iter().rev() {
            if let Some(val) = scope.get(var_name) {
                return Some(val);
            }
        }
        None
    }
}

pub fn type_program(prog: Program<Parsed>) -> Result<Program<Typed>, Error> {
    let mut typed_prog = Program { defs: Vec::new() };
    let mut env = TypeEnv::new();
    env.create_new_scope();
    for def in prog.defs {
        let typed_def = match def {
            Def::Data(data) => Def::Data(type_data_def(&mut env, data)?),
            Def::Func(func) => Def::Func(type_func_def(&mut env, func)?),
        };
        typed_prog.defs.push(typed_def);
    }
    Ok(typed_prog)
}

fn type_data_def(env: &mut TypeEnv, data: DataDef<Parsed>) -> Result<DataDef<Typed>, Error> {
    let DataDef {
        name,
        ty,
        initializer,
    } = data;

    let initializer = type_expr(env, initializer, Category::Regular)?;
    assert_type_eq(initializer.ty(), &ty)?;

    let mut ty = ty;
    // Implicit conversion: [T; _] -> *T
    if let Type::Array(e, _) = ty {
        ty = Type::Ptr(e);
    }

    env.insert(name.clone(), ty.clone());

    Ok(DataDef {
        name,
        ty,
        initializer,
    })
}

fn type_func_def(env: &mut TypeEnv, func: FuncDef<Parsed>) -> Result<FuncDef<Typed>, Error> {
    let FuncDef {
        name,
        params,
        ret_ty,
        body,
    } = func;

    let ty = Type::FuncPtr {
        params: params.iter().map(|p| p.ty.clone()).collect(),
        ret_ty: ret_ty.clone().into(),
    };
    env.insert(name.clone(), ty);

    //------------------------------------------------------
    env.create_new_scope();

    for p in params.iter() {
        let mut ty = p.ty.clone();
        // Implicit conversion: [T; _] -> *T
        if let Type::Array(e, _) = ty {
            ty = Type::Ptr(e);
        }

        env.insert(p.name.clone(), ty);
    }

    let body = type_expr(env, body, Category::Regular)?;
    assert_type_eq(body.ty(), &ret_ty)?;

    env.pop_scope();
    //------------------------------------------------------

    Ok(FuncDef {
        name,
        params,
        ret_ty,
        body,
    })
}

#[allow(clippy::boxed_local)]
fn type_expr(
    env: &mut TypeEnv,
    expr: Box<Expr<Parsed>>,
    cat: Category,
) -> Result<Box<Expr<Typed>>, Error> {
    // verify category
    match &expr.e {
        Var(_) | PtrDeref(_) | ArrayAccess { .. } => {}
        _ => {
            if cat == Category::Location {
                return Err(Error::CategoryMismatch);
            }
        }
    }

    let wrap = |e: E<Typed>, ty: Type| {
        Box::new(Expr {
            e,
            tag: Typed { ty, cat },
        })
    };

    use E::*;
    let typed_expr = match expr.e {
        LiteralVoid => wrap(LiteralVoid, Type::Void),
        LiteralBool(b) => wrap(LiteralBool(b), Type::Bool),
        LiteralU64(val) => wrap(LiteralU64(val), Type::U64),

        LiteralArray(elems) => {
            let mut typed_elems = Vec::new();
            for e in elems {
                typed_elems.push(type_expr(env, e, Category::Regular)?);
            }

            let elem_ty = typed_elems.first().expect("empty array").ty().clone();
            for e in typed_elems.iter() {
                assert_type_eq(e.ty(), &elem_ty)?;
            }

            let ty = Type::Array(elem_ty.into(), typed_elems.len());
            wrap(LiteralArray(typed_elems), ty)
        }

        Var(var_name) => match env.get(&var_name) {
            Some(ty) => wrap(Var(var_name), ty.clone()),
            None => {
                return Err(Error::UndefVar {
                    name: var_name.clone(),
                })
            }
        },

        AddrOf(loc) => {
            let loc = type_expr(env, loc, Category::Location)?;
            let inner_ty = loc.ty().clone();
            let ty = Type::Ptr(inner_ty.into());
            wrap(AddrOf(loc), ty)
        }

        PtrDeref(ptr) => {
            let ptr = type_expr(env, ptr, Category::Regular)?;
            if let Type::Ptr(inner) = ptr.ty() {
                let ty = *inner.clone();
                wrap(PtrDeref(ptr), ty)
            } else {
                todo!("dereference of non-pointer type: {:?}", ptr.ty());
            }
        }

        ArrayAccess { ptr, idx } => {
            let ptr = type_expr(env, ptr, Category::Regular)?;
            let idx = type_expr(env, idx, Category::Regular)?;
            assert_type_eq(idx.ty(), &Type::U64)?;

            if let Type::Ptr(inner) = ptr.ty() {
                let ty = *inner.clone();
                wrap(ArrayAccess { ptr, idx }, ty)
            } else {
                todo!("index access for non-array type: {:?}", ptr.ty());
            }
        }

        Add(_, _) | Sub(_, _) | Mul(_, _) | Div(_, _) => {
            let (ctor, lhs, rhs): (BinCtor, _, _) = match expr.e {
                Add(l, r) => (Add, l, r),
                Sub(l, r) => (Sub, l, r),
                Mul(l, r) => (Mul, l, r),
                Div(l, r) => (Div, l, r),
                _ => unreachable!(),
            };

            let lhs = type_expr(env, lhs, Category::Regular)?;
            let rhs = type_expr(env, rhs, Category::Regular)?;
            assert_type_eq(lhs.ty(), rhs.ty())?;
            let ty = lhs.ty().clone();
            assert_type_eq(&ty, &Type::U64)?; // TODO: support other types
            wrap(ctor(lhs, rhs), ty)
        }

        Eq(_, _) | Neq(_, _) | Lt(_, _) | Gt(_, _) | Leq(_, _) | Geq(_, _) => {
            let (ctor, lhs, rhs): (BinCtor, _, _) = match expr.e {
                Eq(l, r) => (Eq, l, r),
                Neq(l, r) => (Neq, l, r),
                Lt(l, r) => (Lt, l, r),
                Gt(l, r) => (Gt, l, r),
                Leq(l, r) => (Leq, l, r),
                Geq(l, r) => (Geq, l, r),
                _ => unreachable!(),
            };

            let lhs = type_expr(env, lhs, Category::Regular)?;
            let rhs = type_expr(env, rhs, Category::Regular)?;
            assert_type_eq(lhs.ty(), rhs.ty())?;
            wrap(ctor(lhs, rhs), Type::Bool)
        }

        LAnd(_, _) | LOr(_, _) => {
            let (ctor, lhs, rhs): (BinCtor, _, _) = match expr.e {
                LAnd(l, r) => (LAnd, l, r),
                LOr(l, r) => (LOr, l, r),
                _ => unreachable!(),
            };
            let lhs = type_expr(env, lhs, Category::Regular)?;
            let rhs = type_expr(env, rhs, Category::Regular)?;
            assert_type_eq(lhs.ty(), &Type::Bool)?;
            assert_type_eq(rhs.ty(), &Type::Bool)?;
            wrap(ctor(lhs, rhs), Type::Bool)
        }
        LNot(cond) => {
            let cond = type_expr(env, cond, Category::Regular)?;
            assert_type_eq(cond.ty(), &Type::Bool)?;
            wrap(LNot(cond), Type::Bool)
        }

        Call { func, args } => {
            let func = type_expr(env, func, Category::Regular)?;

            let mut typed_args = Vec::new();
            for arg in args {
                let arg = type_expr(env, arg, Category::Regular)?;
                typed_args.push(arg);
            }
            let arg_ty: Vec<Type> = typed_args.iter().map(|e| e.ty().clone()).collect();

            match func.ty().clone() {
                Type::FuncPtr { params, ret_ty } => {
                    if params == arg_ty {
                        let call = Call {
                            func,
                            args: typed_args,
                        };
                        wrap(call, *ret_ty)
                    } else {
                        todo!("type mismatch in function argument")
                    }
                }
                _ => {
                    todo!("not a callable type")
                }
            }
        }

        If {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = type_expr(env, cond, Category::Regular)?;
            assert_type_eq(cond.ty(), &Type::Bool)?;

            match else_expr {
                Some(else_expr) => {
                    let then_expr = type_expr(env, then_expr, Category::Regular)?;
                    let else_expr = type_expr(env, else_expr, Category::Regular)?;
                    assert_type_eq(then_expr.ty(), else_expr.ty())?;
                    let ty = then_expr.ty().clone();
                    let if_expr = If {
                        cond,
                        then_expr,
                        else_expr: Some(else_expr),
                    };
                    wrap(if_expr, ty)
                }
                None => {
                    let then_expr = type_expr(env, then_expr, Category::Regular)?;
                    assert_type_eq(then_expr.ty(), &Type::Void)?;
                    let if_expr = If {
                        cond,
                        then_expr,
                        else_expr: None,
                    };
                    wrap(if_expr, Type::Void)
                }
            }
        }

        Loop { body } => {
            let body = type_expr(env, body, Category::Regular)?;
            wrap(Loop { body }, Type::Void)
        }

        Break => wrap(Break, Type::Void),

        Let { name, value } => {
            let value = type_expr(env, value, Category::Regular)?;

            let mut ty = value.ty().clone();
            // Implicit conversion: [T; _] -> *T
            if let Type::Array(e, _) = ty {
                ty = Type::Ptr(e);
            }
            env.insert(name.clone(), ty);

            wrap(Let { name, value }, Type::Void)
        }

        Assignment { location, value } => {
            let location = type_expr(env, location, Category::Location)?;
            let value = type_expr(env, value, Category::Regular)?;
            assert_type_eq(location.ty(), value.ty())?;
            wrap(Assignment { location, value }, Type::Void)
        }
        AssignAdd { location, value } => {
            let location = type_expr(env, location, Category::Location)?;
            let value = type_expr(env, value, Category::Regular)?;
            assert_type_eq(location.ty(), value.ty())?;
            wrap(AssignAdd { location, value }, Type::Void)
        }
        AssignSub { location, value } => {
            let location = type_expr(env, location, Category::Location)?;
            let value = type_expr(env, value, Category::Regular)?;
            assert_type_eq(location.ty(), value.ty())?;
            wrap(AssignSub { location, value }, Type::Void)
        }
        AssignMul { location, value } => {
            let location = type_expr(env, location, Category::Location)?;
            let value = type_expr(env, value, Category::Regular)?;
            assert_type_eq(location.ty(), value.ty())?;
            wrap(AssignMul { location, value }, Type::Void)
        }
        AssignDiv { location, value } => {
            let location = type_expr(env, location, Category::Location)?;
            let value = type_expr(env, value, Category::Regular)?;
            assert_type_eq(location.ty(), value.ty())?;
            wrap(AssignDiv { location, value }, Type::Void)
        }

        Block(exprs) => {
            //------------------------------------------------------
            env.create_new_scope();

            let mut typed_exprs = Vec::new();
            for e in exprs {
                let e = type_expr(env, e, Category::Regular)?;
                typed_exprs.push(e);
            }
            let ty = typed_exprs
                .last()
                .map(|e| e.ty().clone())
                .unwrap_or(Type::Void);

            env.pop_scope();
            //------------------------------------------------------

            wrap(Block(typed_exprs), ty)
        }
    };
    Ok(typed_expr)
}
