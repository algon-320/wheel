use crate::error::Error;
use crate::expr::{Expr, TypedExpr};
use crate::prog::{Def, Program};

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

fn assert_type_eq(ty: &Option<Type>, expect: Type) -> Result<(), Error> {
    let ty = ty.as_ref().expect("not yet typed");
    if ty != &expect {
        Err(Error::TypeMismatch {
            expect: Some(expect),
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

use std::collections::HashMap;
type TypeEnv = HashMap<String, Type>;

pub fn type_tree(prog: &mut Program) -> Result<(), Error> {
    let mut env = TypeEnv::new();
    for def in prog.defs.iter_mut() {
        let fun = match def {
            Def::Data(data) => {
                type_tree_impl(&mut env, &mut data.initializer)?;
                assert_type_eq(&data.initializer.t, data.ty.clone())?;

                let mut ty = data.ty.clone();
                // Implicit conversion: [T; _] -> *T
                if let Type::Array(e, _) = ty {
                    ty = Type::Ptr(e);
                }

                env.insert(data.name.clone(), ty);
                continue;
            }
            Def::Func(fun) => fun,
        };

        let ty = Type::FuncPtr {
            params: fun.params.iter().map(|p| p.ty.clone()).collect(),
            ret_ty: fun.ret_ty.clone().into(),
        };
        env.insert(fun.name.clone(), ty);

        let mut old_vars = Vec::new();
        for p in fun.params.iter() {
            let mut ty = p.ty.clone();
            // Implicit conversion: [T; _] -> *T
            if let Type::Array(e, _) = ty {
                ty = Type::Ptr(e);
            }

            let old = env.insert(p.name.clone(), ty);
            old_vars.push(old);
        }

        type_tree_impl(&mut env, &mut fun.body)?;
        assert_type_eq(&fun.body.t, fun.ret_ty.clone())?;

        for (p, old) in fun.params.iter().zip(old_vars.into_iter()) {
            if let Some(old) = old {
                env.insert(p.name.clone(), old);
            } else {
                env.remove(&p.name.clone());
            }
        }
    }
    Ok(())
}

fn type_tree_impl(env: &mut TypeEnv, expr: &mut TypedExpr) -> Result<(), Error> {
    use Expr::*;
    match &mut expr.e {
        LiteralVoid => {
            expr.t = Some(Type::Void);
        }
        LiteralBool(_) => {
            expr.t = Some(Type::Bool);
        }
        LiteralU64(_) => {
            expr.t = Some(Type::U64);
        }

        LiteralArray(elems) => {
            for e in elems.iter_mut() {
                type_tree_impl(env, e)?;
            }
            let ty = elems[0].t.clone().unwrap();
            for e in elems.iter_mut() {
                assert_type_eq(&e.t, ty.clone())?;
            }
            expr.t = Some(Type::Array(ty.into(), elems.len()));
        }

        Var(var_name) => {
            let ty = env
                .get(var_name)
                .ok_or_else(|| Error::UndefVar {
                    name: var_name.clone(),
                })?
                .clone();
            expr.t = Some(ty);
        }

        AddrOf(location) => {
            location.c = Some(Category::Location);
            type_tree_impl(env, location)?;
            let inner_ty = location.t.clone().unwrap();
            expr.t = Some(Type::Ptr(inner_ty.into()));
        }

        PtrDeref(ptr) => {
            type_tree_impl(env, ptr)?;
            let ty = ptr.t.clone().unwrap();
            if let Type::Ptr(inner) = ty {
                expr.t = Some(*inner);
            } else {
                todo!("dereference of non-pointer type: {:?}", ty);
            }
        }

        ArrayAccess { ptr, idx } => {
            type_tree_impl(env, ptr)?;
            type_tree_impl(env, idx)?;
            assert_type_eq(&idx.t, Type::U64)?;

            let ty = ptr.t.as_ref().unwrap();
            if let Type::Array(elem, _) = ty {
                expr.t = Some(*elem.clone());
            } else if let Type::Ptr(inner) = ty {
                expr.t = Some(*inner.clone());
            } else {
                todo!("index access for non-array type: {:?}", ty);
            }
        }

        Add(lhs, rhs) | Sub(lhs, rhs) | Mul(lhs, rhs) | Div(lhs, rhs) => {
            type_tree_impl(env, lhs)?;
            type_tree_impl(env, rhs)?;
            assert_type_eq(&lhs.t, rhs.t.clone().unwrap())?;
            assert_type_eq(&lhs.t, Type::U64)?;
            expr.t = lhs.t.clone();
        }

        Eq(lhs, rhs)
        | Neq(lhs, rhs)
        | Lt(lhs, rhs)
        | Gt(lhs, rhs)
        | Leq(lhs, rhs)
        | Geq(lhs, rhs) => {
            type_tree_impl(env, lhs)?;
            type_tree_impl(env, rhs)?;
            assert_type_eq(&lhs.t, rhs.t.clone().unwrap())?;

            // TODO: check if the operands have a comparable type
            // assert_type_eq(&lhs.t, Type::U64)?;

            expr.t = Some(Type::Bool);
        }
        LAnd(lhs, rhs) | LOr(lhs, rhs) => {
            type_tree_impl(env, lhs)?;
            type_tree_impl(env, rhs)?;
            assert_type_eq(&lhs.t, Type::Bool)?;
            assert_type_eq(&rhs.t, Type::Bool)?;
            expr.t = Some(Type::Bool);
        }
        LNot(cond) => {
            type_tree_impl(env, cond)?;
            assert_type_eq(&cond.t, Type::Bool)?;
            expr.t = Some(Type::Bool);
        }

        Call { func, args } => {
            type_tree_impl(env, func)?;
            let func_ty = func.t.as_ref().unwrap();

            let mut arg_ty = Vec::new();
            for arg in args.iter_mut() {
                type_tree_impl(env, arg)?;
                arg_ty.push(arg.t.clone().unwrap());
            }

            match func_ty {
                Type::FuncPtr { params, ret_ty } => {
                    if params == &arg_ty {
                        expr.t = Some(*ret_ty.clone());
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
            type_tree_impl(env, cond)?;
            assert_type_eq(&cond.t, Type::Bool)?;

            type_tree_impl(env, then_expr)?;

            if let Some(else_expr) = else_expr {
                type_tree_impl(env, else_expr)?;
                assert_type_eq(&then_expr.t, else_expr.t.clone().unwrap())?;
                expr.t = Some(then_expr.t.clone().unwrap());
            } else {
                assert_type_eq(&then_expr.t, Type::Void)?;
                expr.t = Some(Type::Void);
            }
        }

        Loop { body } => {
            type_tree_impl(env, body)?;
            expr.t = Some(Type::Void);
        }

        Break => {
            expr.t = Some(Type::Void);
        }

        Let {
            name,
            value,
            expr: in_,
        } => {
            type_tree_impl(env, value)?;

            let mut ty = value.t.clone().unwrap();
            // Implicit conversion: [T; _] -> *T
            if let Type::Array(e, _) = ty {
                ty = Type::Ptr(e);
            }

            let mut env = env.clone();
            env.insert(name.clone(), ty);
            type_tree_impl(&mut env, in_)?;

            expr.t = in_.t.clone();
        }

        Assignment { location, value } => {
            location.c = Some(Category::Location);
            type_tree_impl(env, location)?;

            type_tree_impl(env, value)?;

            assert_type_eq(&location.t, value.t.clone().unwrap())?;
            expr.t = Some(Type::Void);
        }

        Block(exprs, is_void) => {
            let mut ty = Type::Void;
            for e in exprs {
                type_tree_impl(env, e)?;
                ty = e.t.clone().unwrap();
            }
            if *is_void {
                ty = Type::Void;
            }
            expr.t = Some(ty);
        }
    }

    // verify category
    match expr.e {
        Var(_) | PtrDeref(_) | ArrayAccess { .. } => {}
        _ => {
            if expr.c == Some(Category::Location) {
                return Err(Error::CategoryMismatch);
            }
        }
    }
    if expr.c.is_none() {
        expr.c = Some(Category::Regular);
    }

    Ok(())
}
