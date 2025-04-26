#!/bin/bash

types=("pivot" "partition" "unstable_smallsort" "merge_policy" "merge_routine" "stable_smallsort")

for type in "${types[@]}"
do
    TYPE=$type ./run_pattern_benches.sh
    TYPE=$type ./run_scaling_benches.sh
done
