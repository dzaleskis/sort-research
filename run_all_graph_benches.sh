#!/bin/bash

# types=("stable" "unstable")
types=("unstable")

for type in "${types[@]}"
do
    TYPE=$type ./run_pattern_benches.sh
    TYPE=$type ./run_scaling_benches.sh
done
