#!/bin/bash
set -euf -o pipefail

options="-g"
stack_size=4096
files=$(find examples -name '*.wheel')

echo "Compile Options: $options"

echo "Running tests on Rust VM"
(cd .. && cargo build --release --bin vm)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1

    file_size=$(stat --format '%s' $f)
    mem=$(($file_size + $stack_size))
    result=$(../target/release/vm -m "$mem" out.bin)

    diff "$f.expected" <(echo $result) && echo "ok!"
done
echo ""

echo "Running tests on x86_64 asm VM"
(cd ../asm_vm_x86_64 && make)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1

    file_size=$(stat --format '%s' $f)
    mem=$(($file_size + $stack_size))
    result=$(../asm_vm_x86_64/main -m "$mem")

    diff "$f.expected" <(echo $result) && echo "ok!"
done
