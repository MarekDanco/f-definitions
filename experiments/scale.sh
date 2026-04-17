#!/usr/bin/env bash

set -e

if [ "$#" -ne 3 ]; then
  echo "Usage: $0 <input_dir> <output_dir> <multiplier>"
  exit 1
fi

INPUT_DIR="$1"
OUTPUT_DIR="$2"
MULTIPLIER="$3"

mkdir -p "$OUTPUT_DIR"

for file in "$INPUT_DIR"/*.smt2; do
  [ -e "$file" ] || continue

  base=$(basename "$file")

  perl -pe 's/0 x (\d+)/"0 x ".($1*'"$MULTIPLIER"')/ge' \
    "$file" > "$OUTPUT_DIR/$base"
done
