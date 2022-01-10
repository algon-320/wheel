op_label = [
   "nop",
   "lit08",
   "lit16",
   "lit32",
   "lit64",
   "drop08",
   "drop16",
   "drop32",
   "drop64",
   "add08",
   "add16",
   "add32",
   "add64",
   "sub08",
   "sub16",
   "sub32",
   "sub64",
   "mul08",
   "mul16",
   "mul32",
   "mul64",
   "div08",
   "div16",
   "div32",
   "div64",
   "and08",
   "and16",
   "and32",
   "and64",
   "or08",
   "or16",
   "or32",
   "or64",
   "xor08",
   "xor16",
   "xor32",
   "xor64",
   "not08",
   "not16",
   "not32",
   "not64",
   "eq08",
   "eq16",
   "eq32",
   "eq64",
   "lt08",
   "lt16",
   "lt32",
   "lt64",
   "gt08",
   "gt16",
   "gt32",
   "gt64",
   "load08",
   "load16",
   "load32",
   "load64",
   "store08",
   "store16",
   "store32",
   "store64",
   "jump",
   "jump_if",
   "get_ip",
   "set_bp",
   "get_bp",
   "set_sp",
   "get_sp",
   "abort",
]

debug_op_label = [
    "debug_comment"
]

print("lea   op_table(%rip), %rax")
for name in op_label:
    print("lea   {}(%rip), %rbx".format(name))
    print("movq  %rbx, (%rax)")
    print("addq  $8, %rax")

# debug instruction origin: 0xF0
print("lea   op_table(%rip), %rax")
print("addq  $(0xF0 * 8), %rax")
for name in debug_op_label:
    print("lea   {}(%rip), %rbx".format(name))
    print("movq  %rbx, (%rax)")
    print("addq  $8, %rax")
