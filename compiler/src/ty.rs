use crate::ast::{DataDef, Def, Expr, ExprBound, Field, FuncDef, Program, StructDef};
use crate::error::Error;
use crate::parser::{ParsedExpr, ParsedType};

pub trait TypeBound: std::fmt::Debug + Clone + PartialEq {}

#[derive(Debug, Clone, PartialEq)]
pub enum Type<T: TypeBound> {
    Void,
    Bool,
    U64,
    Array(Box<T>, usize),
    Ptr(Box<T>),
    Slice(Box<T>),
    Func { params: Vec<T>, ret_ty: Box<T> },
    Struct { name: String, fields: Vec<T> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedType(pub Type<ResolvedType>);
impl TypeBound for ResolvedType {}

impl ResolvedType {
    pub fn size_of(&self) -> u64 {
        match &self.0 {
            Type::Void => 0,
            Type::Bool => 1,
            Type::U64 => 8,
            Type::Array(elem, len) => elem.size_of() * (*len as u64),
            Type::Ptr(_) => 8,
            Type::Slice(_) => 16, // ptr + size
            Type::Func { .. } => unimplemented!("function size"),
            Type::Struct { fields, .. } => fields.iter().fold(0_u64, |a, f| a + f.size_of()),
        }
    }

    pub fn is_array(&self) -> bool {
        matches!(self.0, Type::Array(_, _))
    }
}

impl From<Type<ResolvedType>> for ResolvedType {
    fn from(ty: Type<ResolvedType>) -> Self {
        ResolvedType(ty)
    }
}

fn assert_type_eq(ty: &ResolvedType, expect: &ResolvedType) -> Result<(), Error> {
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
pub struct TypedExpr {
    pub e: Expr<TypedExpr>,
    pub ty: ResolvedType,
    pub cat: Category,
}
impl ExprBound for TypedExpr {}

type BinCtor = fn(Box<TypedExpr>, Box<TypedExpr>) -> Expr<TypedExpr>;

use std::collections::HashMap;
struct TypeEnv {
    stack: Vec<HashMap<String, ResolvedType>>,
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

    pub fn insert(&mut self, name: String, ty: ResolvedType) {
        let dict = &mut self.stack.last_mut().unwrap();
        let old = dict.insert(name.clone(), ty);
        if old.is_some() {
            log::warn!("variable shadowed: {}", name);
        }
    }

    pub fn get(&self, var_name: &str) -> Option<&ResolvedType> {
        for scope in self.stack.iter().rev() {
            if let Some(val) = scope.get(var_name) {
                return Some(val);
            }
        }
        None
    }
}

struct TypeChecker {
    // variable --> ResolvedType
    env: TypeEnv,

    // type name --> ResolvedType
    type_map: HashMap<String, ResolvedType>,

    // struct name --> StructDef
    struct_def: HashMap<String, StructDef<ResolvedType>>,
}

impl TypeChecker {
    fn new() -> Self {
        Self {
            env: TypeEnv::new(),
            type_map: HashMap::new(),
            struct_def: HashMap::new(),
        }
    }

    fn resolve(&self, ty: ParsedType) -> Result<ResolvedType, Error> {
        match ty {
            ParsedType::Known(ty) => {
                let ty = match ty {
                    Type::Void => ResolvedType(Type::Void),
                    Type::Bool => ResolvedType(Type::Bool),
                    Type::U64 => ResolvedType(Type::U64),

                    Type::Array(elem_ty, len) => {
                        let elem_ty = self.resolve(*elem_ty)?;
                        ResolvedType(Type::Array(Box::new(elem_ty), len))
                    }

                    Type::Slice(elem_ty) => {
                        let elem_ty = self.resolve(*elem_ty)?;
                        ResolvedType(Type::Slice(Box::new(elem_ty)))
                    }

                    Type::Ptr(inner) => {
                        let inner = self.resolve(*inner)?;
                        ResolvedType(Type::Ptr(Box::new(inner)))
                    }

                    Type::Func { params, ret_ty } => {
                        let params = params
                            .into_iter()
                            .map(|ty| self.resolve(ty))
                            .collect::<Result<Vec<_>, _>>()?;
                        let ret_ty = self.resolve(*ret_ty)?.into();
                        ResolvedType(Type::Func { params, ret_ty })
                    }

                    Type::Struct { name, fields } => {
                        let fields = fields
                            .into_iter()
                            .map(|field| self.resolve(field))
                            .collect::<Result<Vec<_>, _>>()?;
                        ResolvedType(Type::Struct { name, fields })
                    }
                };
                Ok(ty)
            }

            ParsedType::UserDefined(name) => {
                if let Some(ty) = self.type_map.get(&name) {
                    Ok(ty.clone())
                } else {
                    Err(Error::UndefinedType { name: name.clone() })
                }
            }
        }
    }

    fn type_program(
        &mut self,
        prog: Program<ParsedExpr, ParsedType>,
    ) -> Result<Program<TypedExpr, ResolvedType>, Error> {
        let mut typed_prog = Program { defs: Vec::new() };
        self.env.create_new_scope();
        for def in prog.defs {
            let typed_def = match def {
                Def::Data(data) => Def::Data(self.type_data_def(data)?),
                Def::Func(func) => Def::Func(self.type_func_def(func)?),
                Def::Struct(struct_def) => {
                    let name = struct_def.name;

                    let mut types = Vec::new();
                    let mut typed_fields = Vec::new();
                    for f in struct_def.fields {
                        let ty = self.resolve(f.ty)?;
                        if ty.size_of() == 0 {
                            todo!("ZST at struct field is not yet supported.");
                        } else {
                            types.push(ty.clone());
                            let name = f.name.clone();
                            typed_fields.push(Field { name, ty });
                        }
                    }

                    let ty = Type::Struct {
                        name: name.clone(),
                        fields: types,
                    };
                    self.type_map.insert(name.clone(), ty.into());

                    let def = StructDef {
                        name: name.clone(),
                        fields: typed_fields,
                    };
                    self.struct_def.insert(name, def.clone());
                    Def::Struct(def)
                }
            };
            typed_prog.defs.push(typed_def);
        }
        Ok(typed_prog)
    }

    fn type_data_def(
        &mut self,
        data: DataDef<ParsedExpr, ParsedType>,
    ) -> Result<DataDef<TypedExpr, ResolvedType>, Error> {
        let DataDef {
            name,
            ty,
            initializer,
        } = data;
        let ty = self.resolve(ty)?;

        let initializer = self.type_expr(initializer, Category::Regular)?;
        assert_type_eq(&initializer.ty, &ty)?;

        self.env.insert(name.clone(), ty.clone());

        Ok(DataDef {
            name,
            ty,
            initializer,
        })
    }

    fn type_func_def(
        &mut self,
        func: FuncDef<ParsedExpr, ParsedType>,
    ) -> Result<FuncDef<TypedExpr, ResolvedType>, Error> {
        let FuncDef {
            name,
            params,
            ret_ty,
            body,
        } = func;

        let ret_ty = self.resolve(ret_ty)?;
        let params: Vec<_> = params
            .into_iter()
            .map(|f| {
                Ok(Field {
                    ty: self.resolve(f.ty)?,
                    name: f.name,
                })
            })
            .collect::<Result<_, Error>>()?;

        let ty = Type::Func {
            params: params.iter().map(|p| p.ty.clone()).collect(),
            ret_ty: ret_ty.clone().into(),
        };
        self.env.insert(name.clone(), ty.into());

        //------------------------------------------------------
        self.env.create_new_scope();

        for p in params.iter() {
            self.env.insert(p.name.clone(), p.ty.clone());
        }

        let body = self.type_expr(body, Category::Regular)?;
        assert_type_eq(&body.ty, &ret_ty)?;

        self.env.pop_scope();
        //------------------------------------------------------

        Ok(FuncDef {
            name,
            params,
            ret_ty,
            body,
        })
    }

    #[allow(clippy::boxed_local)]
    fn type_expr(&mut self, expr: Box<ParsedExpr>, cat: Category) -> Result<Box<TypedExpr>, Error> {
        // verify category
        match &expr.e {
            Var(_) | PtrDeref(_) | IndexAccess { .. } | MemberAccess { .. } => {}
            _ => {
                if cat == Category::Location {
                    return Err(Error::CategoryMismatch);
                }
            }
        }

        let wrap = |e: Expr<TypedExpr>, ty: ResolvedType| Box::new(TypedExpr { e, ty, cat });

        use Expr::*;
        let typed_expr = match expr.e {
            LiteralVoid => wrap(LiteralVoid, Type::Void.into()),
            LiteralBool(b) => wrap(LiteralBool(b), Type::Bool.into()),
            LiteralU64(val) => wrap(LiteralU64(val), Type::U64.into()),

            LiteralArray(elems) => {
                let mut typed_elems = Vec::new();
                for e in elems {
                    typed_elems.push(self.type_expr(e, Category::Regular)?);
                }

                let elem_ty = typed_elems.first().expect("empty array").ty.clone();
                for e in typed_elems.iter() {
                    assert_type_eq(&e.ty, &elem_ty)?;
                }

                let ty = Type::Array(elem_ty.into(), typed_elems.len());
                wrap(LiteralArray(typed_elems), ty.into())
            }

            LiteralSliceFromPtr { ptr, size } => {
                let ptr = self.type_expr(ptr, Category::Regular)?;
                let size = self.type_expr(size, Category::Regular)?;
                assert_type_eq(&size.ty, &ResolvedType(Type::U64))?;

                let ty = if let Type::Ptr(inner) = ptr.ty.clone().0 {
                    Type::Slice(inner)
                } else {
                    todo!("expected a pointer but {:?}", ptr.ty.0);
                };
                wrap(LiteralSliceFromPtr { ptr, size }, ty.into())
            }

            LiteralSliceFromArray { array, begin, end } => {
                let array = self.type_expr(array, Category::Location)?;
                let begin = self.type_expr(begin, Category::Regular)?;
                let end = self.type_expr(end, Category::Regular)?;
                assert_type_eq(&begin.ty, &ResolvedType(Type::U64))?;
                assert_type_eq(&end.ty, &ResolvedType(Type::U64))?;

                let ty = if let Type::Array(elem_ty, _) = array.ty.clone().0 {
                    Type::Slice(elem_ty)
                } else {
                    todo!("expected an array but {:?}", array.ty.0);
                };
                wrap(LiteralSliceFromArray { array, begin, end }, ty.into())
            }

            LiteralStruct { name, fields } => {
                let mut types = Vec::new();
                let mut typed_fields = Vec::new();
                for (name, value) in fields {
                    let value = self.type_expr(value, Category::Regular)?;
                    types.push(value.ty.clone());
                    typed_fields.push((name, value));
                }

                match self.type_map.get(&name) {
                    Some(ty) => {
                        if let Type::Struct {
                            name: name_def,
                            fields: fields_def,
                        } = &ty.0
                        {
                            assert_eq!(&name, name_def);
                            assert_eq!(&types, fields_def);
                        } else {
                            todo!("expect struct");
                        }
                    }
                    None => {
                        return Err(Error::UndefinedType { name: name.clone() });
                    }
                }

                let e = LiteralStruct {
                    name: name.clone(),
                    fields: typed_fields,
                };
                let ty = Type::Struct {
                    name,
                    fields: types,
                };
                wrap(e, ty.into())
            }

            LiteralString(bytes) => {
                let ty = Type::Slice(Box::new(Type::U64.into())); // FIXME: should be U08
                wrap(LiteralString(bytes), ty.into())
            }

            Var(var_name) => match self.env.get(&var_name) {
                Some(ty) => {
                    let ty = ty.clone();
                    let ty = match ty.0 {
                        // Implicit conversion to a function pointer
                        Type::Func { .. } => Type::Ptr(Box::new(ty)),
                        ty => ty,
                    };
                    wrap(Var(var_name), ty.into())
                }
                None => {
                    return Err(Error::UndefinedVar {
                        name: var_name.clone(),
                    })
                }
            },

            AddrOf(loc) => {
                let loc = self.type_expr(loc, Category::Location)?;
                let inner_ty = loc.ty.clone();
                let ty = Type::Ptr(inner_ty.into());
                wrap(AddrOf(loc), ty.into())
            }

            PtrDeref(ptr) => {
                let ptr = self.type_expr(ptr, Category::Regular)?;
                if let Type::Ptr(inner) = &ptr.ty.0 {
                    let ty = *inner.clone();
                    wrap(PtrDeref(ptr), ty)
                } else {
                    todo!("dereference of non-pointer type: {:?}", ptr.ty);
                }
            }

            IndexAccess { ptr, idx } => {
                let ptr = self.type_expr(ptr, cat)?;
                let idx = self.type_expr(idx, Category::Regular)?;
                assert_type_eq(&idx.ty, &ResolvedType(Type::U64))?;

                match &ptr.ty.0 {
                    Type::Array(elem_ty, _) | Type::Slice(elem_ty) => {
                        let ty = *elem_ty.clone();
                        wrap(IndexAccess { ptr, idx }, ty)
                    }
                    ty => {
                        todo!("index access for other than array or slice: {:?}", ty);
                    }
                }
            }

            MemberAccess { obj, field } => {
                let obj = self.type_expr(obj, cat)?;
                match &obj.ty.0 {
                    Type::Struct { name, .. } => {
                        let def = &self.struct_def[name];

                        let field_ty = def
                            .fields
                            .iter()
                            .find(|f| f.name == field)
                            .map(|f| f.ty.clone())
                            .ok_or_else(|| Error::UndefinedField {
                                struct_name: name.clone(),
                                field_name: field.clone(),
                            })?;

                        let field_ty = match field_ty.0 {
                            Type::Func { .. } => unreachable!(),
                            ty => ty,
                        };

                        wrap(MemberAccess { obj, field }, field_ty.into())
                    }

                    Type::Slice(elem_ty) => {
                        let field_ty = match field.as_str() {
                            "ptr" => Type::Ptr(elem_ty.clone()),
                            "len" => Type::U64,
                            _ => {
                                return Err(Error::UndefinedField {
                                    struct_name: "primitive.slice".to_owned(),
                                    field_name: field,
                                });
                            }
                        };
                        wrap(MemberAccess { obj, field }, field_ty.into())
                    }

                    _ => todo!("member access for non-struct value"),
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

                let lhs = self.type_expr(lhs, Category::Regular)?;
                let rhs = self.type_expr(rhs, Category::Regular)?;
                assert_type_eq(&lhs.ty, &rhs.ty)?;
                let ty = lhs.ty.clone();
                assert_type_eq(&ty, &Type::U64.into())?; // TODO: support other types
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

                let lhs = self.type_expr(lhs, Category::Regular)?;
                let rhs = self.type_expr(rhs, Category::Regular)?;
                assert_type_eq(&lhs.ty, &rhs.ty)?;
                wrap(ctor(lhs, rhs), Type::Bool.into())
            }

            LAnd(_, _) | LOr(_, _) => {
                let (ctor, lhs, rhs): (BinCtor, _, _) = match expr.e {
                    LAnd(l, r) => (LAnd, l, r),
                    LOr(l, r) => (LOr, l, r),
                    _ => unreachable!(),
                };
                let lhs = self.type_expr(lhs, Category::Regular)?;
                let rhs = self.type_expr(rhs, Category::Regular)?;
                assert_type_eq(&lhs.ty, &Type::Bool.into())?;
                assert_type_eq(&rhs.ty, &Type::Bool.into())?;
                wrap(ctor(lhs, rhs), Type::Bool.into())
            }
            LNot(cond) => {
                let cond = self.type_expr(cond, Category::Regular)?;
                assert_type_eq(&cond.ty, &Type::Bool.into())?;
                wrap(LNot(cond), Type::Bool.into())
            }

            Call { func, args } => {
                let func = self.type_expr(func, Category::Regular)?;

                let mut typed_args = Vec::new();
                for arg in args {
                    let arg = self.type_expr(arg, Category::Regular)?;
                    typed_args.push(arg);
                }
                let arg_ty: Vec<ResolvedType> = typed_args.iter().map(|e| e.ty.clone()).collect();

                match func.ty.clone().0 {
                    Type::Ptr(inner) => match inner.0 {
                        Type::Func { params, ret_ty } => {
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
                    },
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
                let cond = self.type_expr(cond, Category::Regular)?;
                assert_type_eq(&cond.ty, &Type::Bool.into())?;

                match else_expr {
                    Some(else_expr) => {
                        let then_expr = self.type_expr(then_expr, Category::Regular)?;
                        let else_expr = self.type_expr(else_expr, Category::Regular)?;
                        assert_type_eq(&then_expr.ty, &else_expr.ty)?;
                        let ty = then_expr.ty.clone();
                        let if_expr = If {
                            cond,
                            then_expr,
                            else_expr: Some(else_expr),
                        };
                        wrap(if_expr, ty)
                    }
                    None => {
                        let then_expr = self.type_expr(then_expr, Category::Regular)?;
                        assert_type_eq(&then_expr.ty, &Type::Void.into())?;
                        let if_expr = If {
                            cond,
                            then_expr,
                            else_expr: None,
                        };
                        wrap(if_expr, Type::Void.into())
                    }
                }
            }

            Loop { body } => {
                let body = self.type_expr(body, Category::Regular)?;
                assert_type_eq(&body.ty, &Type::Void.into())?;
                wrap(Loop { body }, Type::Void.into())
            }
            While { cond, body } => {
                let cond = self.type_expr(cond, Category::Regular)?;
                let body = self.type_expr(body, Category::Regular)?;
                assert_type_eq(&cond.ty, &Type::Bool.into())?;
                assert_type_eq(&body.ty, &Type::Void.into())?;
                wrap(While { cond, body }, Type::Void.into())
            }
            For {
                init,
                cond,
                update,
                body,
            } => {
                //------------------------------------------------------
                self.env.create_new_scope();

                let init = self.type_expr(init, Category::Regular)?;
                let cond = self.type_expr(cond, Category::Regular)?;
                let update = self.type_expr(update, Category::Regular)?;
                let body = self.type_expr(body, Category::Regular)?;

                self.env.pop_scope();
                //------------------------------------------------------

                assert_type_eq(&init.ty, &Type::Void.into())?;
                assert_type_eq(&cond.ty, &Type::Bool.into())?;
                assert_type_eq(&update.ty, &Type::Void.into())?;
                assert_type_eq(&body.ty, &Type::Void.into())?;

                wrap(
                    For {
                        init,
                        cond,
                        update,
                        body,
                    },
                    Type::Void.into(),
                )
            }

            Break => wrap(Break, Type::Void.into()),
            Continue => wrap(Continue, Type::Void.into()),

            Let { name, value } => {
                let value = self.type_expr(value, Category::Regular)?;
                self.env.insert(name.clone(), value.ty.clone());

                wrap(Let { name, value }, Type::Void.into())
            }

            Assignment { location, value } => {
                let location = self.type_expr(location, Category::Location)?;
                let value = self.type_expr(value, Category::Regular)?;
                assert_type_eq(&location.ty, &value.ty)?;
                wrap(Assignment { location, value }, Type::Void.into())
            }
            AssignAdd { location, value } => {
                let location = self.type_expr(location, Category::Location)?;
                let value = self.type_expr(value, Category::Regular)?;
                assert_type_eq(&location.ty, &value.ty)?;
                wrap(AssignAdd { location, value }, Type::Void.into())
            }
            AssignSub { location, value } => {
                let location = self.type_expr(location, Category::Location)?;
                let value = self.type_expr(value, Category::Regular)?;
                assert_type_eq(&location.ty, &value.ty)?;
                wrap(AssignSub { location, value }, Type::Void.into())
            }
            AssignMul { location, value } => {
                let location = self.type_expr(location, Category::Location)?;
                let value = self.type_expr(value, Category::Regular)?;
                assert_type_eq(&location.ty, &value.ty)?;
                wrap(AssignMul { location, value }, Type::Void.into())
            }
            AssignDiv { location, value } => {
                let location = self.type_expr(location, Category::Location)?;
                let value = self.type_expr(value, Category::Regular)?;
                assert_type_eq(&location.ty, &value.ty)?;
                wrap(AssignDiv { location, value }, Type::Void.into())
            }

            Block(exprs) => {
                //------------------------------------------------------
                self.env.create_new_scope();

                let mut typed_exprs = Vec::new();
                for e in exprs {
                    let e = self.type_expr(e, Category::Regular)?;
                    typed_exprs.push(e);
                }
                let ty = typed_exprs
                    .last()
                    .map(|e| e.ty.clone())
                    .unwrap_or(ResolvedType(Type::Void));

                self.env.pop_scope();
                //------------------------------------------------------

                wrap(Block(typed_exprs), ty)
            }
        };
        Ok(typed_expr)
    }
}

pub fn type_program(
    prog: Program<ParsedExpr, ParsedType>,
) -> Result<Program<TypedExpr, ResolvedType>, Error> {
    TypeChecker::new().type_program(prog)
}
