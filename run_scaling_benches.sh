#!/bin/bash

# bench for scaling
BENCH_REGEX=".*_${TYPE}-hot-.*-random-.*" python util/run_benchmarks.py "${TYPE}_scaling_firestorm"

# make graph
python3 util/graph_bench_result/graph_all.py "${TYPE}_scaling_firestorm.json"

echo "${TYPE} scaling graphs generated"
