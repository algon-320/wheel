use crate::error::Error;
use crate::expr::{Expr, TypedExpr};
use crate::prog::{FuncDef, Parameter, Program};
use crate::ty::Type;

#[derive(Debug, Clone)]
pub enum Token {
    Fun,
    If,
    Else,
    Let,
    In,
    LParen,
    RParen,
    LBrace,
    RBrace,
    True,
    False,
    Arrow,
    Plus,
    Minus,
    Star,
    Slash,
    Colon,
    SemiColon,
    Comma,
    Equal,
    Lt,
    Gt,
    And,
    Pipe,
    Bang,
    Ident(String),
    Number(String),
}

#[derive(Debug, Clone)]
pub struct PosToken {
    pub t: Token,
    pub begin: usize,
    pub end: usize,
}

peg::parser! { grammar tokenizer() for str {
    pub rule tokenize() -> Vec<PosToken> = token()*

    rule ws()
        = quiet!{[' '|'\t'|'\n'|'\r']+}

    rule comment()
        = quiet!{ "//" [^'\n']* ['\n']}

    rule token() -> PosToken
        = (ws() / comment())*
          begin:position!() tok:(
            fun() / if_() / else_() / let_() / in_() / boolean() / paren() / arrow() /
            plus() / minus() / star() / slash() /
            colon() / semicolon() / comma() / equal() / lt() / gt() /
            and() / pipe() / bang() / ident() / number()
          ) end:position!()
          (ws() / comment())*
          { PosToken { t: tok, begin, end } }

    rule fun() -> Token = "fn" { Token::Fun }
    rule if_() -> Token = "if" { Token::If }
    rule else_() -> Token = "else" { Token::Else }
    rule let_() -> Token = "let" { Token::Let }
    rule in_() -> Token = "in" { Token::In }
    rule boolean() -> Token = "true" { Token::True } / "false" { Token::False }
    rule paren() -> Token
        = "(" { Token::LParen }
        / ")" { Token::RParen }
        / "{" { Token::LBrace }
        / "}" { Token::RBrace }
    rule arrow() -> Token = "->" { Token::Arrow }
    rule plus() -> Token = "+" { Token::Plus }
    rule minus() -> Token = "-" { Token::Minus }
    rule star() -> Token = "*" { Token::Star }
    rule slash() -> Token = "/" { Token::Slash }
    rule colon() -> Token = ":" { Token::Colon }
    rule semicolon() -> Token = ";" { Token::SemiColon }
    rule comma() -> Token = "," { Token::Comma }
    rule equal() -> Token = "=" { Token::Equal }
    rule lt() -> Token = "<" { Token::Lt }
    rule gt() -> Token = ">" { Token::Gt }
    rule and() -> Token = "&" { Token::And }
    rule pipe() -> Token = "|" { Token::Pipe }
    rule bang() -> Token = "!" { Token::Bang }

    rule ident() -> Token
        = ident: quiet!{$(['a'..='z'|'A'..='Z'|'_'] ['a'..='z'|'A'..='Z'|'_'|'0'..='9']*)}
        { Token::Ident(ident.to_string()) }
        / expected!("ident")

    rule number() -> Token
        = n: quiet!{$(['1'..='9']['0'..='9']* / ['0'])}
        { Token::Number(n.to_owned()) }
        / expected!("number")
} }

fn wrap(e: Expr) -> Box<TypedExpr> {
    Box::new(TypedExpr { e, t: None })
}

peg::parser! { pub grammar parser() for [Token] {
    use Token::*;

    // type

    rule ty() -> Type
        = obj_ty() / func_ptr_ty()

    rule obj_ty() -> Type
        = [LParen] [RParen] { Type::Void }
        / [Ident(ty)] {?
            match ty.as_str() {
                "bool" => Ok(Type::Bool),
                "u64" => Ok(Type::U64),
                _ => Err("invalid type"),
            }
        }

    rule func_ptr_ty() -> Type
        = [Fun] [LParen] params:(ty() ** [Comma]) [RParen] [Arrow] ret_ty:ty()
        { Type::FuncPtr { params, ret_ty: ret_ty.into() } }

    // expression

    pub rule expr() -> Box<TypedExpr>
        = precedence! {
            l:(@) [Pipe] [Pipe] r:@   { wrap(Expr::LOr(l, r)) }
            l:(@) [And] [And] r:@     { wrap(Expr::LAnd(l, r)) }
            --
            [Bang] e:@                { wrap(Expr::LNot(e)) }
            --
            l:(@) [Equal] [Equal] r:@ { wrap(Expr::Eq(l, r)) }
            l:(@) [Bang] [Equal]  r:@ { wrap(Expr::Neq(l, r)) }
            --
            l:(@) [Lt] [Equal] r:@    { wrap(Expr::Leq(l, r)) }
            l:(@) [Gt] [Equal] r:@    { wrap(Expr::Geq(l, r)) }
            l:(@) [Lt] r:@            { wrap(Expr::Lt(l, r)) }
            l:(@) [Gt] r:@            { wrap(Expr::Gt(l, r)) }
            --
            l:(@) [Plus]  r:@         { wrap(Expr::Add(l, r)) }
            l:(@) [Minus] r:@         { wrap(Expr::Sub(l, r)) }
            --
            l:(@) [Star]  r:@         { wrap(Expr::Mul(l, r)) }
            l:(@) [Slash] r:@         { wrap(Expr::Div(l, r)) }
            --

            e:block_expr() { e }
            e:literal_bool() { e }
            e:literal_void() { e }
            e:literal_u64() { e }
            e:variable() { e }
            e:variable_def() { e }
            e:if_expr() { e }

            func:@ [LParen] args:(expr() ** [Comma]) [RParen] {
                let args = args.into_iter().map(|bx| *bx).collect();
                wrap(Expr::Call { func, args })
            }

            [LParen] expr:expr() [RParen] { expr }
        }

    rule literal_void() -> Box<TypedExpr>
        = [LParen] [RParen]
        { TypedExpr { e: Expr::LiteralVoid, t: None }.into() }

    rule literal_bool() -> Box<TypedExpr>
        = [True]  { TypedExpr { e: Expr::LiteralBool(true),  t: None }.into() }
        / [False] { TypedExpr { e: Expr::LiteralBool(false), t: None }.into() }

    rule literal_u64() -> Box<TypedExpr>
        = [Number(n)]
        {?
            let n = n.parse().or(Err("u64 literal: integer too large"))?;
            Ok(TypedExpr { e: Expr::LiteralU64(n), t: None }.into())
        }

    rule variable() -> Box<TypedExpr>
        = [Ident(name)] { TypedExpr { e: Expr::Var(name), t: None }.into() }

    rule variable_def() -> Box<TypedExpr>
        = [Let] [Ident(name)] [Equal] e1:expr() [In] e2:expr()
        { TypedExpr { e: Expr::Let { name, value: e1, expr: e2 }, t: None }.into() }

    rule if_expr() -> Box<TypedExpr>
        = [If] cond:expr() [LBrace] then_expr:expr() [RBrace] [Else] [LBrace] else_expr:expr() [RBrace]
        { wrap(Expr::If { cond, then_expr, else_expr }) }

    rule block_expr() -> Box<TypedExpr>
        = [LBrace] exprs:(expr() ** [SemiColon]) is_void:([SemiColon]?) [RBrace]
        {
            let exprs = exprs.into_iter().map(|bx| *bx).collect();
            wrap(Expr::Block(exprs, is_void.is_some()))
        }

    // function

    rule param() -> Parameter
        = [Ident(name)] [Colon] ty:ty()
        { Parameter { name, ty } }

    rule function_def() -> FuncDef
        = [Fun] [Ident(name)]
            [LParen] ps:(param() ** [Comma]) [RParen]
            [Arrow] ret_ty:ty()
            [LBrace] body:expr() [RBrace]
        { FuncDef { name, params: ps, ret_ty, body } }

    // program

    pub rule program() -> Program
        = functions:(function_def())* { Program { functions } }
} }

pub fn parse_program(text: &str) -> Result<Program, Error> {
    let pos_tokens: Vec<PosToken> = tokenizer::tokenize(text).map_err(|err| {
        let line = err.location.line;
        let column = err.location.column;
        let msg = format!("invalid token");
        Error::SyntaxError { line, column, msg }
    })?;

    let (tokens, positions): (Vec<Token>, Vec<(usize, usize)>) = pos_tokens
        .into_iter()
        .map(|pt| (pt.t, (pt.begin, pt.end)))
        .unzip();

    parser::program(&tokens).map_err(|err| {
        let pos = positions[err.location].0;
        let before = &text[..pos];
        let line = before.as_bytes().iter().filter(|&&c| c == b'\n').count() + 1;
        let column = before.chars().rev().take_while(|&c| c != '\n').count() + 1;
        let msg = format!("unexpected token: {:?}", tokens[err.location]);
        Error::SyntaxError { line, column, msg }
    })
}
