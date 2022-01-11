" Vim syntax file
" Language: Wheel
" Maintaner: algon-320 (algon.0320@gmail.com)
" Latest Revision: Jan. 11, 2022

if exists("b:current_syntax")
  finish
endif

let s:save_cpo = &cpo
set cpo&vim

syn keyword keyword fn
syn keyword keyword let
syn keyword struct struct
syn keyword execution break continue return asm
syn keyword loop loop while for
syn keyword cond if else
syn keyword boolean true false

syn keyword type u8 u08 u16 u32 u64 bool

syn match call display "\h\w*("he=e-1,me=e-1
syn match number display "\<\%(0x\x\+\|\d\+\)\%(_u8\|_u08\|_u16\|_u32\|_u64\)\?"

syn keyword todo contained TODO FIXME NOTE XXX HACK
syn region comment  start="//" end="$" contains=todo

syn region string start=/"/ end=/"/ skip=/\\\\\|\\"/
syn region char   start=/'/ end=/'/ skip=/\\\\\|\\'/

hi def link keyword         Keyword
hi def link cond            Conditional
hi def link loop            Repeat
hi def link execution       Special
hi def link struct          Structure
hi def link type            Type
hi def link number          Number
hi def link string          String
hi def link char            Character
hi def link boolean         Boolean
hi def link call            Function
hi def link comment         Comment
hi def link todo            Todo

let &cpo = s:save_cpo
let b:current_syntax = "wheel"
