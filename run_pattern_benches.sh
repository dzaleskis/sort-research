#!/bin/bash

# bench for patterns
BENCH_REGEX=".*_${TYPE}-hot-.*-.*-1000000$" python util/run_benchmarks.py "${TYPE}_patterns_firestorm"

# make graph
python3 util/graph_bench_result/graph_all.py "${TYPE}_patterns_firestorm.json"

echo "${TYPE} patterns graphs generated"
