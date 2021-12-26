#!/bin/bash
set -euf -o pipefail

options="-g"
files=$(find examples -name '*.wheel')

echo "Compile Options: $options"

echo "Running tests on Rust VM"
(cd .. && cargo build --release --bin vm)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1
    result=$(../target/release/vm out.bin)
    diff "$f.expected" <(echo $result) && echo "ok!"
done
echo ""

echo "Running tests on x86_64 asm VM"
(cd ../asm_vm_x86_64 && make)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1
    result=$(../asm_vm_x86_64/main)
    diff "$f.expected" <(echo $result) && echo "ok!"
done
