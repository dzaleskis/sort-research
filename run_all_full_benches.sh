#!/bin/bash

types=("pivot" "partition" "unstable_smallsort" "merge_policy" "merge_routine" "stable_smallsort")

for type in "${types[@]}"
do
    TYPE=$type ./run_full_benches.sh
done
