# Wheel

a minimalist stack machine,
accompanied by a bunch of tools
(compiler, disassembler, VM implementation).

## Architecture
- three 64-bit registers (`IP`, `SP`, and `BP`)
- `IP` points to the next instruction
- `SP` points to the top of the stack
- `BP` points to the bottom of the current stack frame
- all integer values are stored on memory in the little endian
### Initialization
- `IP` is set to 0
- `SP` and `BP` are set to the bottom of the memory
    (e.g. if the memory size is 4096 bytes, then SP=BP=4096)

### Instruction Set
Please refer to `spec/src/lib.rs`.
