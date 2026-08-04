#!/bin/bash

cargo b --release

mkdir -p benchdata

for act in active passive
do
    echo "'$act' starts"
    for ((i=1;i<=5000;i++))
    do
        j=$(($i+1))
        input=$(sed -n "${j}p" evaluation.csv | cut -d "," -f 2)
        echo "=== line ${i}, input: '$input'"
        ACTIVE="$act" timeout 3s ./target/release/rs2 "$input"
    done
done
