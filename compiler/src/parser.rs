#![allow(clippy::redundant_closure_call)]

use crate::ast::{DataDef, Def, Expr, ExprBound, Field, FuncDef, Program, StructDef};
use crate::error::Error;
use crate::ty::{Type, TypeBound};

#[derive(Debug, Clone, Copy)]
enum Base {
    Hex,
    Decimal,
}
impl Base {
    fn radix(&self) -> u32 {
        match self {
            Base::Decimal => 10,
            Base::Hex => 16,
        }
    }
}

#[derive(Debug, Clone)]
enum Token {
    Fun,
    Struct,
    If,
    Else,
    Loop,
    While,
    For,
    Break,
    Continue,
    Return,
    Let,
    As,
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
    At,
    Dot,
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
    U08(String, Base),
    U16(String, Base),
    U32(String, Base),
    U64(String, Base),
    Str(String),
    Char(char),
}

#[derive(Debug, Clone)]
struct PosToken {
    t: Token,
    begin: usize,
    end: usize,
}

peg::parser! { grammar tokenizer() for str {
    pub(super) rule tokenize() -> Vec<PosToken> = token()*

    rule ws()
        = quiet!{[' '|'\t'|'\n'|'\r']+}

    rule comment()
        = quiet!{ "//" [^'\n']* ['\n']}

    rule token() -> PosToken
        = (ws() / comment())*
          begin:position!() tok:(
            fun() / struct_() / if_() / else_() / loop_() / while_() / for_() /
            break_() / continue_() / return_() /
            let_() / as_() / boolean() / paren() / arrow() /
            plus() / minus() / star() / slash() /
            at() / dot() / colon() / semicolon() / comma() / equal() / lt() / gt() /
            and() / pipe() / bang() / ident() / integer() / utf8_string() / ascii_char()
          ) end:position!()
          (ws() / comment())*
          { PosToken { t: tok, begin, end } }

    rule fun() -> Token = "fn" !alnum_() { Token::Fun }
    rule struct_() -> Token = "struct" !alnum_() { Token::Struct }
    rule if_() -> Token = "if" !alnum_() { Token::If }
    rule else_() -> Token = "else" !alnum_() { Token::Else }
    rule loop_() -> Token = "loop" !alnum_() { Token::Loop }
    rule while_() -> Token = "while" !alnum_() { Token::While }
    rule for_() -> Token = "for" !alnum_() { Token::For }
    rule break_() -> Token = "break" !alnum_() { Token::Break }
    rule continue_() -> Token = "continue" !alnum_() { Token::Continue }
    rule return_() -> Token = "return" !alnum_() { Token::Return }
    rule let_() -> Token = "let" !alnum_() { Token::Let }
    rule as_() -> Token = "as" !alnum_() { Token::As }
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
    rule at() -> Token = "@" { Token::At }
    rule dot() -> Token = "." { Token::Dot }
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

    rule int_str() -> (String, Base)
        = quiet!{ !"0x" n:$(['1'..='9']['0'..='9']* / ['0'])  { (n.to_owned(), Base::Decimal) } }
        / quiet!{  "0x" n:$(['0'..='9'|'a'..='f'|'A'..='F']+) { (n.to_owned(), Base::Hex) } }
        / expected!("integer")

    rule integer() -> Token
        = n:int_str() ("_u8" / "_u08") { Token::U08(n.0, n.1) }
        / n:int_str() "_u16" { Token::U16(n.0, n.1) }
        / n:int_str() "_u32" { Token::U32(n.0, n.1) }
        / n:int_str() "_u64" { Token::U64(n.0, n.1) }
        / n:int_str()        { Token::U64(n.0, n.1) }

    rule utf8_string() -> Token
        = quiet!{"\"" s:(double_quoted_char()*) "\"" { Token::Str(s.into_iter().collect()) } }
        / expected!("UTF-8 string")

    rule ascii_char() -> Token
        = quiet!{ "'" c:single_quoted_char() "'" { Token::Char(c) } }
        / expected!("character")

    rule double_quoted_char() -> char
        = !("\"" / "\\") c:$([_]) { c.chars().next().unwrap() }
        / "\\\"" { '"' }
        / "\\\\" { '\\' }
        / "\\u{" value:$(['0'..='9' | 'a'..='f' | 'A'..='F']+) "}"
        {
            let val = u32::from_str_radix(value, 16).unwrap();
            char::from_u32(val).unwrap()
        }

    rule single_quoted_char() -> char
        = !("\\'" / "\\") c:$([_]) { c.chars().next().unwrap() }
        / "\\\'" { '\'' }
        / "\\\\" { '\\' }
        / "\\x" value:$(['0'..='9' | 'a'..='f' | 'A'..='F']*<2>)
        {
            let val = u8::from_str_radix(value, 16).unwrap();
            assert!(val < 128, "invalid ASCII character");
            char::from_u32(val as u32).unwrap()
        }
} }

#[derive(Debug, Clone, PartialEq)]
pub enum ParsedType {
    Known(Type<ParsedType>),
    UserDefined(String),
}
impl TypeBound for ParsedType {}

#[derive(Debug, Clone, PartialEq)]
pub struct ParsedExpr {
    pub e: Expr<ParsedExpr, ParsedType>,
}
impl ExprBound for ParsedExpr {}

fn wrap(e: Expr<ParsedExpr, ParsedType>) -> Box<ParsedExpr> {
    Box::new(ParsedExpr { e })
}

peg::parser! { pub grammar parser() for [Token] {
    use Token::*;

    // type

    rule ty() -> Box<ParsedType>
        = [LParen] [RParen] { ParsedType::Known(Type::Void).into() }
        / [Ident(ty)]
        {?
            match ty.as_str() {
                "bool" => Ok(ParsedType::Known(Type::Bool).into()),
                "u8" | "u08" => Ok(ParsedType::Known(Type::U08).into()),
                "u16" => Ok(ParsedType::Known(Type::U16).into()),
                "u32" => Ok(ParsedType::Known(Type::U32).into()),
                "u64" => Ok(ParsedType::Known(Type::U64).into()),
                name => Ok(ParsedType::UserDefined(ty).into()),
            }
        }
        / array_ty() / slice_ty() / ptr_ty() / func_ptr_ty()


    rule array_ty() -> Box<ParsedType>
        = [LSquareBracket] ty:ty() [SemiColon] [U64(len, base)] [RSquareBracket]
        {?
            let len: usize = len.parse().or(Err("integer too large"))?;
            Ok(ParsedType::Known(Type::Array(ty, len)).into())
        }

    rule slice_ty() -> Box<ParsedType>
        = [Star] [LSquareBracket] ty:ty() [RSquareBracket]
        { ParsedType::Known(Type::Slice(ty)).into() }

    rule ptr_ty() -> Box<ParsedType>
        = [Star] ty:ty() { ParsedType::Known(Type::Ptr(ty)).into() }

    rule func_ptr_ty() -> Box<ParsedType>
        = [Fun] [LParen] params:(ty() ** [Comma]) [RParen] [Arrow] ret_ty:ty()
        {
            let params = params.into_iter().map(|bx| *bx).collect();
            let func = ParsedType::Known(Type::Func { params, ret_ty });
            ParsedType::Known(Type::Ptr(func.into())).into()
        }

    // expression

    pub(super) rule expr() -> Box<ParsedExpr>
        = precedence! {
            location:(@) [Equal] value:@
                { wrap(Expr::Assignment { location, value }) }
            location:(@) [Plus] [Equal] value:@
                { wrap(Expr::AssignAdd { location, value }) }
            location:(@) [Minus] [Equal] value:@
                { wrap(Expr::AssignSub { location, value }) }
            location:(@) [Star] [Equal] value:@
                { wrap(Expr::AssignMul { location, value }) }
            location:(@) [Slash] [Equal] value:@
                { wrap(Expr::AssignDiv { location, value }) }
            --
            [Return] e:@              { wrap(Expr::Return(e)) }
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
            e:literal_slice_from_array() { e }
            --
            [Star] e:@ { wrap(Expr::PtrDeref(e)) }
            [And]  e:@ { wrap(Expr::AddrOf(e)) }
            --
            ptr:@ [LSquareBracket] idx:expr() [RSquareBracket]
                { wrap(Expr::IndexAccess{ ptr, idx }) }
            --
            obj:@ [Dot] [Ident(field)] { wrap(Expr::MemberAccess { obj, field }) }
            --

            e:block_expr() { e }
            e:literal_struct() { e }
            e:variable_def() { e }
            e:if_expr() { e }
            e:loop_expr() { e }
            e:while_expr() { e }
            e:for_expr() { e }
            e:break_expr() { e }
            e:continue_expr() { e }

            func:@ [LParen] args:(expr() ** [Comma]) [RParen] {
                wrap(Expr::Call { func, args })
            }

            e:literal_bool() { e }
            e:literal_void() { e }
            e:literal_u08() { e }
            e:literal_u16() { e }
            e:literal_u32() { e }
            e:literal_u64() { e }
            e:literal_array() { e }
            e:literal_slice_from_ptr() { e }
            e:literal_string() { e }
            e:variable() { e }

            e:@ [As] ty:ty() { wrap(Expr::Cast(e, ty)) }

            [LParen] expr:expr() [RParen] { expr }
        }

    rule literal_void() -> Box<ParsedExpr>
        = [LParen] [RParen]
        { wrap(Expr::LiteralVoid) }

    rule literal_bool() -> Box<ParsedExpr>
        = [True]  { wrap(Expr::LiteralBool(true)) }
        / [False] { wrap(Expr::LiteralBool(false)) }

    rule literal_u08() -> Box<ParsedExpr>
        = [U08(n, base)]
        {?
            let n = u8::from_str_radix(&n, base.radix()).map_err(|_| "u8: integer too large")?;
            Ok(wrap(Expr::LiteralU08(n)))
        }
        / [Char(c)]
        {?  Ok(wrap(Expr::LiteralU08(c as u8))) }

    rule literal_u16() -> Box<ParsedExpr>
        = [U16(n, base)]
        {?
            let n = u16::from_str_radix(&n, base.radix()).map_err(|_| "u16: integer too large")?;
            Ok(wrap(Expr::LiteralU16(n)))
        }
    rule literal_u32() -> Box<ParsedExpr>
        = [U32(n, base)]
        {?
            let n = u32::from_str_radix(&n, base.radix()).map_err(|_| "u32: integer too large")?;
            Ok(wrap(Expr::LiteralU32(n)))
        }
    rule literal_u64() -> Box<ParsedExpr>
        = [U64(n, base)]
        {?
            let n = u64::from_str_radix(&n, base.radix()).map_err(|_| "u64: integer too large")?;
            Ok(wrap(Expr::LiteralU64(n)))
        }

    rule literal_array() -> Box<ParsedExpr>
        = [LSquareBracket] elems:(expr() ++ [Comma]) [Comma]? [RSquareBracket]
        { wrap(Expr::LiteralArray(elems)) }

    rule literal_slice_from_array() -> Box<ParsedExpr>
        = [And] array:expr() [LSquareBracket] begin:expr() [Dot] [Dot] end:expr() [RSquareBracket]
        { wrap(Expr::LiteralSliceFromArray { array, begin, end }) }

    rule literal_slice_from_ptr() -> Box<ParsedExpr>
        = [LSquareBracket] [At] ptr:expr() [SemiColon] size:expr() [RSquareBracket]
        { wrap(Expr::LiteralSliceFromPtr { ptr, size }) }

    rule literal_string() -> Box<ParsedExpr>
        = [Str(s)] { wrap(Expr::LiteralString(s.into_bytes())) }

    rule literal_struct() -> Box<ParsedExpr>
        = [Ident(name)] [LBrace] fields:(struct_field() ** [Comma]) [Comma]? [RBrace]
        { wrap(Expr::LiteralStruct { name, fields }) }

    rule struct_field() -> (String, Box<ParsedExpr>)
        = [Ident(name)] [Colon] val:expr() { (name, val) }

    rule variable() -> Box<ParsedExpr>
        = [Ident(name)] { wrap(Expr::Var(name)) }

    rule variable_def() -> Box<ParsedExpr>
        = [Let] [Ident(name)] [Equal] e1:expr()
        { wrap(Expr::Let { name, value: e1 }) }

    rule if_expr() -> Box<ParsedExpr>
        = [If] then_cond:expr() then_block:block_expr()
            else_if:(([Else] [If] cond: expr() block:block_expr() { (cond, block) })*)
            else_block:([Else] b:block_expr() { b })?
        {
            let mut branches = vec![(then_cond, then_block)];
            branches.extend(else_if);
            wrap(Expr::If { branches, else_block })
        }

    rule loop_expr() -> Box<ParsedExpr>
        = [Loop] body:block_expr()
        { wrap(Expr::Loop { body }) }

    rule while_expr() -> Box<ParsedExpr>
        = [While] cond:expr() body:block_expr()
        { wrap(Expr::While { cond, body }) }

    rule for_expr() -> Box<ParsedExpr>
        = [For] init:expr() [SemiColon] cond:expr() [SemiColon] update:expr() body:block_expr()
        { wrap(Expr::For { init, cond, update, body }) }

    rule break_expr() -> Box<ParsedExpr>
        = [Break] { wrap(Expr::Break) }

    rule continue_expr() -> Box<ParsedExpr>
        = [Continue] { wrap(Expr::Continue) }

    rule block_expr() -> Box<ParsedExpr>
        = [LBrace] [RBrace] { wrap(Expr::Block(vec![])) }
        / [LBrace] exprs:(block_element()+) [RBrace]
        {
            let is_void = exprs.last().expect("+").1;
            let mut exprs: Vec<_> = exprs.into_iter().map(|(e, _)| e).collect();
            if is_void {
                exprs.push(wrap(Expr::LiteralVoid));
            }
            wrap(Expr::Block(exprs))
        }
        / [LBrace] exprs:(block_element()*) last: expr_without_block() [RBrace]
        {
            let mut exprs: Vec<_> = exprs.into_iter().map(|(e, _)| e).collect();
            exprs.push(last);
            wrap(Expr::Block(exprs))
        }

    rule block_element() -> (Box<ParsedExpr>, bool)
        = e:expr_without_block() [SemiColon] { (e, true) }
        / e:expr_with_block() semi:([SemiColon]?) { (e, semi.is_some()) }

    rule expr_with_block() -> Box<ParsedExpr>
        = block_expr()
        / if_expr()
        / loop_expr()
        / while_expr()
        / for_expr()

    rule expr_without_block() -> Box<ParsedExpr>
        = !expr_with_block() e:expr() { e }

    rule field() -> Field<ParsedType>
        = [Ident(name)] [Colon] ty:ty()
        { Field { name, ty: *ty } }

    rule function_def() -> Def<ParsedExpr, ParsedType>
        = [Fun] [Ident(name)]
            [LParen] params:(field() ** [Comma]) [RParen]
            [Arrow] ret_ty:ty() body:block_expr()
        { Def::Func(FuncDef { name, params, ret_ty: *ret_ty, body }) }

    rule static_data() -> Def<ParsedExpr, ParsedType>
        = [Let] [Ident(name)] [Colon] ty:ty() [Eq] initializer:expr() [SemiColon]
        { Def::Data(DataDef { name, ty: *ty, initializer }) }

    rule struct_def() -> Def<ParsedExpr, ParsedType>
        = [Struct] [Ident(name)] [LBrace] fields:(field() ** [Comma]) [Comma]? [RBrace]
        { Def::Struct(StructDef { name, fields }) }

    pub(super) rule program() -> Program<ParsedExpr, ParsedType>
        = defs:(function_def() / static_data() / struct_def())* { Program { defs } }
} }

pub fn parse_program(text: &str) -> Result<Program<ParsedExpr, ParsedType>, Error> {
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
