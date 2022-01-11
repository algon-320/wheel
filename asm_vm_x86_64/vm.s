  .data
op_table: .fill 256, 8

  .text
  .globl vm_main

eval:
  movq  $0, %rax
  movb  (%r11), %al
  incq  %r11

  movq  $8, %rbx
  mulq  %rbx
  lea   op_table(%rip), %rbx
  addq  %rbx, %rax
  jmp   *(%rax)

nop:
  jmp   eval

lit08:
  movb  (%r11), %al
  incq  %r11
  decq  %rsp
  movb  %al, (%rsp)
  jmp   eval
lit16:
  movw  (%r11), %ax
  addq  $2, %r11
  pushw %ax
  jmp   eval
lit32:
  movl  (%r11), %eax
  addq  $4, %r11
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
lit64:
  movq  (%r11), %rax
  addq  $8, %r11
  pushq %rax
  jmp   eval

drop08:
  incq  %rsp
  jmp   eval
drop16:
  addq  $2, %rsp
  jmp   eval
drop32:
  addq  $4, %rsp
  jmp   eval
drop64:
  addq  $8, %rsp
  jmp   eval

add08:
  popw  %bx
  movw  %bx, %ax
  addb  %bl, %ah
  decq  %rsp
  movb  %ah, (%rsp)
  jmp   eval
add16:
  popw  %bx
  popw  %ax
  addw  %bx, %ax
  pushw %ax
  jmp   eval
add32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  addl  %ebx, %eax
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
add64:
  popq  %rbx
  popq  %rax
  addq  %rbx, %rax
  pushq %rax
  jmp   eval

sub08:
  popw  %bx
  movw  %bx, %ax
  subb  %bl, %ah
  decq  %rsp
  movb  %ah, (%rsp)
  jmp   eval
sub16:
  popw  %bx
  popw  %ax
  subw  %bx, %ax
  pushw %ax
  jmp   eval
sub32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  subl  %ebx, %eax
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
sub64:
  popq  %rbx
  popq  %rax
  subq  %rbx, %rax
  pushq %rax
  jmp   eval

mul08:
  popw  %bx
  movw  %bx, %ax
  shrw  $8,  %ax
  mulb  %bl
  decq  %rsp
  movb  %al, (%rsp)
  jmp   eval
mul16:
  popw  %bx
  popw  %ax
  mulw  %bx
  pushw %ax
  jmp   eval
mul32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  mull  %ebx
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
mul64:
  popq  %rbx
  popq  %rax
  mulq  %rbx
  pushq %rax
  jmp   eval

div08:
  popw  %bx
  movw  %bx, %ax
  shrw  $8,  %ax
  divb  %bl
  decq  %rsp
  movb  %al, (%rsp)
  jmp   eval
div16:
  popw  %bx
  popw  %ax
  movw  $0, %dx
  divw  %bx
  pushw %ax
  jmp   eval
div32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  movl  $0, %edx
  divl  %ebx
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
div64:
  popq  %rbx
  popq  %rax
  movq  $0, %rdx
  divq  %rbx
  pushq %rax
  jmp   eval

and08:
  popw  %bx
  movw  %bx, %ax
  andb  %bl, %ah
  decq  %rsp
  movb  %ah, (%rsp)
  jmp   eval
and16:
  popw  %bx
  popw  %ax
  andw  %bx, %ax
  pushw %ax
  jmp   eval
and32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  andl  %ebx, %eax
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
and64:
  popq  %rbx
  popq  %rax
  andq  %rbx, %rax
  pushq %rax
  jmp   eval

or08:
  popw  %bx
  movw  %bx, %ax
  orb  %bl, %ah
  decq  %rsp
  movb  %ah, (%rsp)
  jmp   eval
or16:
  popw  %bx
  popw  %ax
  orw  %bx, %ax
  pushw %ax
  jmp   eval
or32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  orl  %ebx, %eax
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
or64:
  popq  %rbx
  popq  %rax
  orq  %rbx, %rax
  pushq %rax
  jmp   eval

xor08:
  popw  %bx
  movw  %bx, %ax
  xorb  %bl, %ah
  decq  %rsp
  movb  %ah, (%rsp)
  jmp   eval
xor16:
  popw  %bx
  popw  %ax
  xorw  %bx, %ax
  pushw %ax
  jmp   eval
xor32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  xorl  %ebx, %eax
  subq  $4, %rsp
  movl  %eax, (%rsp)
  jmp   eval
xor64:
  popq  %rbx
  popq  %rax
  xorq  %rbx, %rax
  pushq %rax
  jmp   eval

not08:
  notb  (%rsp)
  jmp   eval
not16:
  notw  (%rsp)
  jmp   eval
not32:
  notl  (%rsp)
  jmp   eval
not64:
  notq  (%rsp)
  jmp   eval

eq08:
  popw  %bx
  movw  %bx, %ax
  cmpb  %bl, %ah
  je    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
eq16:
  popw  %bx
  popw  %ax
  cmpw  %bx, %ax
  je    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
eq32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  cmpl  %ebx, %eax
  je    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
eq64:
  popq  %rbx
  popq  %rax
  cmpq  %rbx, %rax
  je    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval

lt08:
  popw  %bx
  movw  %bx, %ax
  cmpb  %bl, %ah
  jl    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
lt16:
  popw  %bx
  popw  %ax
  cmpw  %bx, %ax
  jl    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
lt32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  cmpl  %ebx, %eax
  jl    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
lt64:
  popq  %rbx
  popq  %rax
  cmpq  %rbx, %rax
  jl    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval

gt08:
  popw  %bx
  movw  %bx, %ax
  cmpb  %bl, %ah
  jg    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
gt16:
  popw  %bx
  popw  %ax
  cmpw  %bx, %ax
  jg    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
gt32:
  popq  %rbx
  movq  %rbx, %rax
  shrq  $32,  %rax
  cmpl  %ebx, %eax
  jg    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval
gt64:
  popq  %rbx
  popq  %rax
  cmpq  %rbx, %rax
  jg    push_true
  decq  %rsp
  movb  $0, (%rsp)
  jmp   eval

push_true:
  decq %rsp
  movb $1, (%rsp)
  jmp  eval

load08:
  popq  %rax
  addq  %rdi, %rax
  movb  (%rax), %bl
  decq  %rsp
  movb  %bl, (%rsp)
  jmp   eval
load16:
  popq  %rax
  addq  %rdi, %rax
  movw  (%rax), %bx
  pushw %bx
  jmp   eval
load32:
  popq  %rax
  addq  %rdi, %rax
  movl  (%rax), %ebx
  subq  $4, %rsp
  movl  %ebx, (%rsp)
  jmp   eval
load64:
  popq  %rax
  addq  %rdi, %rax
  movq  (%rax), %rbx
  subq  $8, %rsp
  movq  %rbx, (%rsp)
  jmp   eval

store08:
  popq  %rax
  addq  %rdi, %rax
  movb  (%rsp), %bl
  incq  %rsp
  movb  %bl, (%rax)
  jmp   eval
store16:
  popq  %rax
  addq  %rdi, %rax
  popw  %bx
  movw  %bx, (%rax)
  jmp   eval
store32:
  popq  %rax
  addq  %rdi, %rax
  movl  (%rsp), %ebx
  addq  $4, %rsp
  movl  %ebx, (%rax)
  jmp   eval
store64:
  popq  %rax
  addq  %rdi, %rax
  popq  %rbx
  movq  %rbx, (%rax)
  jmp   eval

jump:
  popq  %r11
  addq  %rdi, %r11
  jmp   eval
jump_if:
  movb  (%rsp), %bl
  incq  %rsp
  popq  %rax
  andb  $1, %bl
  jz    jump_if_cont
  movq  %rax, %r11
  addq  %rdi, %r11
  jmp   eval
jump_if_cont:
  jmp   eval

get_ip:
  pushq %r11
  jmp   eval
set_bp:
  popq  %rbp
  addq  %rdi, %rbp
  jmp   eval
get_bp:
  movq  %rbp, %rax
  subq  %rdi, %rax
  pushq %rax
  jmp   eval
set_sp:
  popq  %rax
  addq  %rdi, %rax
  movq  %rax, %rsp
  jmp   eval
get_sp:
  movq  %rsp, %rax
  subq  %rdi, %rax
  pushq %rax
  jmp   eval

disable_intr:
  // TODO
  jmp   eval
enable_intr:
  // TODO
  jmp   eval

abort:
  jmp   exit

debug_comment:
  movq  $0, %rax
  movb  (%r11), %al
  incq  %r11
  addq  %rax, %r11
  jmp   eval

# void vm_main(void *text, void *stack)
#   text: %rdi
#  stack: %rsi
vm_main:
  # store callee save registers
  pushq %rbx
  pushq %r12
  pushq %r13
  pushq %r14
  pushq %r15

  movq  %rbp, %r8
  movq  %rsp, %r9

  # switch to the allocated stack
  movq  %rsi, %rbp
  movq  %rsi, %rsp

  # init op_table
  lea   op_table(%rip), %rax
  lea   nop(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lit08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lit16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lit32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lit64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   drop08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   drop16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   drop32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   drop64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   add08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   add16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   add32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   add64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   sub08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   sub16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   sub32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   sub64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   mul08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   mul16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   mul32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   mul64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   div08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   div16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   div32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   div64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   and08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   and16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   and32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   and64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   or08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   or16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   or32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   or64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   xor08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   xor16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   xor32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   xor64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   not08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   not16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   not32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   not64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   eq08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   eq16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   eq32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   eq64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lt08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lt16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lt32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   lt64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   gt08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   gt16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   gt32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   gt64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   load08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   load16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   load32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   load64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   store08(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   store16(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   store32(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   store64(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   jump(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   jump_if(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   get_ip(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   set_bp(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   get_bp(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   set_sp(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   get_sp(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   disable_intr(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   enable_intr(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax
  lea   abort(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax

  lea   op_table(%rip), %rax
  addq  $(0xF0 * 8), %rax
  lea   debug_comment(%rip), %rbx
  movq  %rbx, (%rax)
  addq  $8, %rax

  # start
  movq  %rdi, %r11
  jmp   eval

exit:
  # Return the result value (FIXME: not always 64-bit)
  movq  $0, %rax
  movq  (%rsp), %rax
  addq  $8, %rsp

  # switch-back to the original stack
  movq  %r9,  %rsp
  movq  %r8,  %rbp

  # restore callee save registers
  popq  %r15
  popq  %r14
  popq  %r13
  popq  %r12
  popq  %rbx
  ret

