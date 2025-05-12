#!/bin/bash

# types=("stable" "unstable" "synergistic")
types=("synergistic")

for type in "${types[@]}"
do
    TYPE=$type ./run_pattern_benches.sh
    TYPE=$type ./run_scaling_benches.sh
done
