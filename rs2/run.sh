#!/bin/bash

cargo b --release

for ((i=2;i<=200;i++))
do
    input=$(sed -n "${i}p" evaluation.csv | cut -d "," -F 2)
    echo "=== line ${i}, input: '$input'"
    timeout 1s ./target/release/rs2 "$input"
done
