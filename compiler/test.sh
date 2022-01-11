#!/bin/bash
set -euf -o pipefail

options="-g"
stack_size=4096
files=$(find examples -name '*.wheel')

tmp_file=$(mktemp -t 'wheel-test-result.XXXXXXXXXX')
trap '{ rm -f "$tmp_file"; }' EXIT

echo "Compile Options: $options"

echo "Running tests on Rust VM"
(cd .. && cargo build --release --bin vm)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1

    file_size=$(stat --format '%s' $f)
    mem=$(($file_size + $stack_size))

    ../target/release/vm -m "$mem" out.bin 2>/dev/null > "$tmp_file"

    diff "$f.expected" "$tmp_file" && echo "ok!"
done
echo ""

# device IO and interruption is currently not supported by the asm VM
files=$(find examples -name '*.wheel' -not -path '*mmio_*' -not -path '*interrupt*')

echo "Running tests on x86_64 asm VM"
(cd ../asm_vm_x86_64 && make)
for f in $files; do
    echo -n "testing $f ..."
    cargo run -- $options "$f" >/dev/null 2>&1

    file_size=$(stat --format '%s' $f)
    mem=$(($file_size + $stack_size))
    ../asm_vm_x86_64/main -m "$mem" > "$tmp_file"

    diff "$f.expected" "$tmp_file" && echo "ok!"
done

rm "$tmp_file"
