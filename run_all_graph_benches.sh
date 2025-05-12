#!/bin/bash

types=("stable")

for type in "${types[@]}"
do
    TYPE=$type ./run_pattern_benches.sh
    TYPE=$type ./run_scaling_benches.sh
done
