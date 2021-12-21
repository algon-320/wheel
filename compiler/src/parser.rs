#![allow(clippy::redundant_closure_call)]

use crate::error::Error;
use crate::expr::{Expr, ExprTag, E};
use crate::prog::{DataDef, Def, FuncDef, Parameter, Program};
use crate::ty::Type;

#[derive(Debug, Clone)]
pub enum Token {
    Fun,
    If,
    Else,
    Loop,
    While,
    For,
    Break,
    Continue,
    Let,
    In,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LSquareBracket,
    RSquareBracket,
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
            fun() / if_() / else_() / loop_() / while_() / for_() /
            break_() / continue_() /
            let_() / in_() / boolean() / paren() / arrow() /
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
    rule while_() -> Token = "while" !alnum_() { Token::While }
    rule for_() -> Token = "for" !alnum_() { Token::For }
    rule break_() -> Token = "break" !alnum_() { Token::Break }
    rule continue_() -> Token = "continue" !alnum_() { Token::Continue }
    rule let_() -> Token = "let" !alnum_() { Token::Let }
    rule in_() -> Token = "in" !alnum_() { Token::In }
    rule boolean() -> Token
        = "true" !alnum_() { Token::True } / "false" !alnum_() { Token::False }
    rule paren() -> Token
        = "(" { Token::LParen }
        / ")" { Token::RParen }
        / "{" { Token::LBrace }
        / "}" { Token::RBrace }
        / "[" { Token::LSquareBracket }
        / "]" { Token::RSquareBracket }
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

#[derive(Debug, Clone, PartialEq)]
pub struct Parsed;
impl ExprTag for Parsed {}

fn wrap(e: E<Parsed>) -> Box<Expr<Parsed>> {
    Box::new(Expr::<Parsed> { e, tag: Parsed })
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
        / [Star] ty:ty() { Type::Ptr(Box::new(ty)) }
        / [LSquareBracket] ty:ty() [SemiColon] [Number(len)] [RSquareBracket]
        {?
            let len: usize = len.parse().or(Err("integer too large"))?;
            Ok(Type::Array(Box::new(ty), len))
        }

    rule func_ptr_ty() -> Type
        = [Fun] [LParen] params:(ty() ** [Comma]) [RParen] [Arrow] ret_ty:ty()
        { Type::FuncPtr { params, ret_ty: ret_ty.into() } }

    // expression

    pub rule expr() -> Box<Expr<Parsed>>
        = precedence! {
            location:(@) [Equal] value:@
                { wrap(E::Assignment { location, value }) }
            location:(@) [Plus] [Equal] value:@
                { wrap(E::AssignAdd { location, value }) }
            location:(@) [Minus] [Equal] value:@
                { wrap(E::AssignSub { location, value }) }
            location:(@) [Star] [Equal] value:@
                { wrap(E::AssignMul { location, value }) }
            location:(@) [Slash] [Equal] value:@
                { wrap(E::AssignDiv { location, value }) }
            --
            l:(@) [Pipe] [Pipe] r:@   { wrap(E::LOr(l, r)) }
            l:(@) [And] [And] r:@     { wrap(E::LAnd(l, r)) }
            --
            [Bang] e:@                { wrap(E::LNot(e)) }
            --
            l:(@) [Equal] [Equal] r:@ { wrap(E::Eq(l, r)) }
            l:(@) [Bang] [Equal]  r:@ { wrap(E::Neq(l, r)) }
            --
            l:(@) [Lt] [Equal] r:@    { wrap(E::Leq(l, r)) }
            l:(@) [Gt] [Equal] r:@    { wrap(E::Geq(l, r)) }
            l:(@) [Lt] r:@            { wrap(E::Lt(l, r)) }
            l:(@) [Gt] r:@            { wrap(E::Gt(l, r)) }
            --
            l:(@) [Plus]  r:@         { wrap(E::Add(l, r)) }
            l:(@) [Minus] r:@         { wrap(E::Sub(l, r)) }
            --
            l:(@) [Star]  r:@         { wrap(E::Mul(l, r)) }
            l:(@) [Slash] r:@         { wrap(E::Div(l, r)) }
            --
            [Star] e:@ { wrap(E::PtrDeref(e)) }
            [And]  e:@ { wrap(E::AddrOf(e)) }
            --
            ptr:@ [LSquareBracket] idx:expr() [RSquareBracket]
                { wrap(E::ArrayAccess{ ptr, idx }) }
            --

            e:block_expr() { e }
            e:variable_def() { e }
            e:if_expr() { e }
            e:if_no_else_expr() { e }
            e:loop_expr() { e }
            e:while_expr() { e }
            e:for_expr() { e }
            e:break_expr() { e }
            e:continue_expr() { e }

            func:@ [LParen] args:(expr() ** [Comma]) [RParen] {
                wrap(E::Call { func, args })
            }

            e:literal_bool() { e }
            e:literal_void() { e }
            e:literal_u64() { e }
            e:literal_array() { e }
            e:variable() { e }

            [LParen] expr:expr() [RParen] { expr }
        }

    rule literal_void() -> Box<Expr<Parsed>>
        = [LParen] [RParen]
        { wrap(E::LiteralVoid) }

    rule literal_bool() -> Box<Expr<Parsed>>
        = [True]  { wrap(E::LiteralBool(true)) }
        / [False] { wrap(E::LiteralBool(false)) }

    rule literal_u64() -> Box<Expr<Parsed>>
        = [Number(n)]
        {?
            let n = n.parse().or(Err("u64 literal: integer too large"))?;
            Ok(wrap(E::LiteralU64(n)))
        }

    rule literal_array() -> Box<Expr<Parsed>>
        = [LSquareBracket] elems:(expr() ++ [Comma]) [RSquareBracket]
        {
            wrap(E::LiteralArray(elems))
        }

    rule variable() -> Box<Expr<Parsed>>
        = [Ident(name)] { wrap(E::Var(name)) }

    rule variable_def() -> Box<Expr<Parsed>>
        = [Let] [Ident(name)] [Equal] e1:expr()
        { wrap(E::Let { name, value: e1 }) }

    rule if_expr() -> Box<Expr<Parsed>>
        = [If] cond:expr() then_expr:block_expr() [Else] else_expr:block_expr()
        { wrap(E::If { cond, then_expr, else_expr: Some(else_expr) }) }

    rule if_no_else_expr() -> Box<Expr<Parsed>>
        = [If] cond:expr() then_expr:block_expr()
        { wrap(E::If { cond, then_expr, else_expr: None }) }

    rule loop_expr() -> Box<Expr<Parsed>>
        = [Loop] body:block_expr()
        { wrap(E::Loop { body }) }

    rule while_expr() -> Box<Expr<Parsed>>
        = [While] cond:expr() body:block_expr()
        { wrap(E::While { cond, body }) }

    rule for_expr() -> Box<Expr<Parsed>>
        = [For] init:expr() [SemiColon] cond:expr() [SemiColon] update:expr() body:block_expr()
        { wrap(E::For { init, cond, update, body }) }

    rule break_expr() -> Box<Expr<Parsed>>
        = [Break] { wrap(E::Break) }

    rule continue_expr() -> Box<Expr<Parsed>>
        = [Continue] { wrap(E::Continue) }

    rule block_expr() -> Box<Expr<Parsed>>
        = [LBrace] [RBrace] { wrap(E::Block(vec![])) }
        / [LBrace] exprs:(block_element()+) [RBrace]
        {
            let is_void = exprs.last().expect("+").1;
            let mut exprs: Vec<_> = exprs.into_iter().map(|(e, _)| e).collect();
            if is_void {
                exprs.push(wrap(E::LiteralVoid));
            }
            wrap(E::Block(exprs))
        }
        / [LBrace] exprs:(block_element()*) last: expr_without_block() [RBrace]
        {
            let mut exprs: Vec<_> = exprs.into_iter().map(|(e, _)| e).collect();
            exprs.push(last);
            wrap(E::Block(exprs))
        }

    rule block_element() -> (Box<Expr<Parsed>>, bool)
        = e:expr_without_block() [SemiColon] { (e, true) }
        / e:expr_with_block() semi:([SemiColon]?) { (e, semi.is_some()) }

    rule expr_with_block() -> Box<Expr<Parsed>>
        = block_expr()
        / if_expr()
        / if_no_else_expr()
        / loop_expr()
        / while_expr()
        / for_expr()

    rule expr_without_block() -> Box<Expr<Parsed>>
        = !expr_with_block() e:expr() { e }

    // function

    rule param() -> Parameter
        = [Ident(name)] [Colon] ty:ty()
        { Parameter { name, ty } }

    rule function_def() -> Def<Parsed>
        = [Fun] [Ident(name)]
            [LParen] ps:(param() ** [Comma]) [RParen]
            [Arrow] ret_ty:ty() body:block_expr()
        { Def::Func(FuncDef { name, params: ps, ret_ty, body }) }

    // data

    rule static_data() -> Def<Parsed>
        = [Let] [Ident(name)] [Colon] ty:ty() [Eq] initializer:expr() [SemiColon]
        { Def::Data(DataDef { name, ty, initializer }) }

    // program

    pub rule program() -> Program<Parsed>
        = defs:(function_def() / static_data())* { Program { defs } }
} }

pub fn parse_program(text: &str) -> Result<Program<Parsed>, Error> {
    let pos_tokens: Vec<PosToken> = tokenizer::tokenize(text).map_err(|err| {
        let line = err.location.line;
        let column = err.location.column;
        let msg = "invalid token".to_owned();
        Error::Syntax { line, column, msg }
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
        Error::Syntax { line, column, msg }
    })
}
