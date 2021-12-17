use crate::error::Error;
use crate::expr::{Expr, TypedExpr};
use crate::prog::{DataDef, Def, FuncDef, Parameter, Program};
use crate::ty::Type;

#[derive(Debug, Clone)]
pub enum Token {
    Fun,
    If,
    Else,
    Loop,
    Break,
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
            fun() / if_() / else_() / loop_() / break_() / let_() / in_() /
            boolean() / paren() / arrow() /
            plus() / minus() / star() / slash() /
            colon() / semicolon() / comma() / equal() / lt() / gt() /
            and() / pipe() / bang() / ident() / number()
          ) end:position!()
          (ws() / comment())*
          { PosToken { t: tok, begin, end } }

    rule fun() -> Token = "fn" !alnum_() { Token::Fun }
    rule if_() -> Token = "if" !alnum_() { Token::If }
    rule else_() -> Token = "else" !alnum_() { Token::Else }
    rule loop_() -> Token = "loop" !alnum_() { Token::Loop }
    rule break_() -> Token = "break" !alnum_() { Token::Break }
    rule let_() -> Token = "let" !alnum_() { Token::Let }
    rule in_() -> Token = "in" !alnum_() { Token::In }
    rule boolean() -> Token
        = "true" !alnum_() { Token::True } / "false" !alnum_() { Token::False }
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

    rule alnum_() = quiet!{['a'..='z'|'A'..='Z'|'0'..='9'|'_']}

    rule ident() -> Token
        = ident: quiet!{$(['a'..='z'|'A'..='Z'|'_'] alnum_()*)}
        { Token::Ident(ident.to_string()) }
        / expected!("ident")

    rule number() -> Token
        = n: quiet!{$(['1'..='9']['0'..='9']* / ['0'])}
        { Token::Number(n.to_owned()) }
        / expected!("number")
} }

fn wrap(e: Expr) -> Box<TypedExpr> {
    Box::new(TypedExpr {
        e,
        t: None,
        c: None,
    })
}

peg::parser! { pub grammar parser() for [Token] {
    use Token::*;

    // type

    rule ty() -> Type
        = data_ty() / func_ptr_ty()

    rule data_ty() -> Type
        = [LParen] [RParen] { Type::Void }
        / [Ident(ty)] {?
            match ty.as_str() {
                "bool" => Ok(Type::Bool),
                "u64" => Ok(Type::U64),
                _ => Err("invalid type"),
            }
        }
        / [Star] ty:data_ty() { Type::Ptr(Box::new(ty)) }

    rule func_ptr_ty() -> Type
        = [Fun] [LParen] params:(ty() ** [Comma]) [RParen] [Arrow] ret_ty:ty()
        { Type::FuncPtr { params, ret_ty: ret_ty.into() } }

    // expression

    pub rule expr() -> Box<TypedExpr>
        = precedence! {
            location:(@) [Equal] value:@ { wrap(Expr::Assignment { location, value }) }
            --
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
            [Star] e:@                { wrap(Expr::PtrDeref(e)) }
            [And]  e:@                { wrap(Expr::AddrOf(e)) }

            e:block_expr() { e }
            e:variable_def() { e }
            e:if_expr() { e }
            e:loop_expr() { e }
            e:break_expr() { e }

            func:@ [LParen] args:(expr() ** [Comma]) [RParen] {
                let args = args.into_iter().map(|bx| *bx).collect();
                wrap(Expr::Call { func, args })
            }

            e:literal_bool() { e }
            e:literal_void() { e }
            e:literal_u64() { e }
            e:variable() { e }

            [LParen] expr:expr() [RParen] { expr }
        }

    rule literal_void() -> Box<TypedExpr>
        = [LParen] [RParen]
        { wrap(Expr::LiteralVoid) }

    rule literal_bool() -> Box<TypedExpr>
        = [True]  { wrap(Expr::LiteralBool(true)) }
        / [False] { wrap(Expr::LiteralBool(false)) }

    rule literal_u64() -> Box<TypedExpr>
        = [Number(n)]
        {?
            let n = n.parse().or(Err("u64 literal: integer too large"))?;
            Ok(wrap(Expr::LiteralU64(n)))
        }

    rule variable() -> Box<TypedExpr>
        = [Ident(name)] { wrap(Expr::Var(name)) }

    rule variable_def() -> Box<TypedExpr>
        = [Let] [Ident(name)] [Equal] e1:expr() [In] e2:expr()
        { wrap(Expr::Let { name, value: e1, expr: e2 }) }

    rule if_expr() -> Box<TypedExpr>
        = [If] cond:expr() then_expr:block_expr() [Else] else_expr:block_expr()
        { wrap(Expr::If { cond, then_expr, else_expr }) }

    rule loop_expr() -> Box<TypedExpr>
        = [Loop] body:block_expr()
        { wrap(Expr::Loop { body }) }

    rule break_expr() -> Box<TypedExpr>
        = [Break] { wrap(Expr::Break) }

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

    rule function_def() -> Def
        = [Fun] [Ident(name)]
            [LParen] ps:(param() ** [Comma]) [RParen]
            [Arrow] ret_ty:ty() body:block_expr()
        { Def::Func(FuncDef { name, params: ps, ret_ty, body }) }

    // data

    rule static_data() -> Def
        = [Let] [Ident(name)] [Colon] ty:ty() [Eq] initializer:expr() [SemiColon]
        { Def::Data(DataDef { name, ty, initializer }) }

    // program

    pub rule program() -> Program
        = defs:(function_def() / static_data())* { Program { defs } }
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
