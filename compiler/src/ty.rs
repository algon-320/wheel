use crate::error::Error;
use crate::expr::{Expr, TypedExpr};
use crate::prog::Program;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Void,
    Bool,
    U64,
    FuncPtr {
        params: Vec<Type>,
        ret_ty: Box<Type>,
    },
}

impl Type {
    pub fn size_of(&self) -> usize {
        match self {
            Type::Void => 0,
            Type::Bool => 1,
            Type::U64 => 8,
            Type::FuncPtr { .. } => 8,
        }
    }
}

fn assert_type_eq(ty: &Option<Type>, expect: Type) -> Result<(), Error> {
    let ty = ty.as_ref().expect("not yet typed");
    if ty != &expect {
        Err(Error::TypeMismach {
            expect: Some(expect),
            actual: ty.clone(),
        })
    } else {
        Ok(())
    }
}

use std::collections::HashMap;
type TypeEnv = HashMap<String, Type>;

pub fn type_tree(prog: &mut Program) -> Result<(), Error> {
    let mut env = TypeEnv::new();
    for fun in prog.functions.iter_mut() {
        let ty = Type::FuncPtr {
            params: fun.params.iter().map(|p| p.ty.clone()).collect(),
            ret_ty: fun.ret_ty.clone().into(),
        };
        env.insert(fun.name.clone(), ty);

        let mut old_vars = Vec::new();
        for p in fun.params.iter() {
            let old = env.insert(p.name.clone(), p.ty.clone());
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
        Var(var_name) => {
            let ty = env.get(var_name).ok_or_else(|| Error::UndefVar {
                name: var_name.clone(),
            })?;
            expr.t = Some(ty.clone());
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
            type_tree_impl(env, else_expr)?;
            assert_type_eq(&then_expr.t, else_expr.t.clone().unwrap())?;
            expr.t = Some(then_expr.t.clone().unwrap());
        }

        Let {
            name,
            value,
            expr: in_,
        } => {
            type_tree_impl(env, value)?;

            let mut env = env.clone();
            env.insert(name.clone(), value.t.clone().unwrap());
            type_tree_impl(&mut env, in_)?;

            expr.t = in_.t.clone();
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
    Ok(())
}
