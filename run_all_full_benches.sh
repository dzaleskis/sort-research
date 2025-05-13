#!/bin/bash

# types=("pivot" "partition" "unstable_smallsort" "merge_policy" "merge_routine" "stable_smallsort")
# types=("stable" "unstable" "synergistic")
types=("stable")

for type in "${types[@]}"
do
    TYPE=$type ./run_full_benches.sh
done
