#!/bin/bash

# # bench for patterns
# RUST_BACKTRACE=full BENCH_REGEX=".*_${TYPE}-hot-.*-.*-.*$" python util/run_benchmarks.py "${TYPE}_full_firestorm"

# # make graph
python3 util/graph_bench_result/graph_all.py "${TYPE}_full_firestorm.json"

echo "${TYPE} full graphs generated"

# make table
python3 util/graph_bench_result/table_all.py "${TYPE}_full_firestorm.json" "${TYPE}"

echo "${TYPE} full tables generated"

# make combined graph
python3 util/graph_bench_result/combined.py "${TYPE}"

echo "${TYPE} combined graphs generated"
