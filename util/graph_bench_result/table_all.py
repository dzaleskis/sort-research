import json
import sys
import pandas as pd
import numpy as np
from util import (
    parse_bench_results,
    build_implementation_meta_info,
    base_name,
    plot_name_suffix,
)

args = sys.argv[1:]
filename = args[0]
prefix = args[1]
groups = parse_bench_results([filename])
results = []
mean_results = []
slowdown_results = []

for ty, val1 in groups.items():
    for prediction_state, val2 in val1.items():
        for size, val3 in val2.items():
            for pattern, val4 in val3.items():
                for algo, runtime in val4.items():
                    results.append([ty, size, pattern, algo, runtime / size])

all_df = pd.DataFrame(results, columns=['Type', 'Size', 'Pattern', 'Algorithm', 'Runtime'])
# all_df.to_csv('all_benchmark_results.csv', index=False)

types = set(all_df['Type'].values.tolist())

for ty in types:
    type_df = all_df[all_df['Type'] == ty]
    patterns = set(type_df['Pattern'].values.tolist())

    for pattern in patterns:
        pattern_df = type_df[type_df['Pattern'] == pattern]
        algos = set(pattern_df['Algorithm'].values.tolist())

        for algo in algos:
            algo_df = pattern_df[pattern_df['Algorithm'] == algo]
            algo_runtimes = algo_df['Runtime'].values
            mean_algo_runtime = np.mean(algo_runtimes)
            mean_results.append([ty, pattern, algo, mean_algo_runtime])

all_mean_df = pd.DataFrame(mean_results, columns=['Type', 'Pattern', 'Algorithm', 'Mean runtime'])
all_mean_df.to_csv(f"{prefix}_mean_benchmark_results.csv", index=False)

for ty in types:
    type_df = all_mean_df[all_mean_df['Type'] == ty]
    patterns = set(type_df['Pattern'].values.tolist())

    for pattern in patterns:
        pattern_df = type_df[type_df['Pattern'] == pattern]
        algos = set(pattern_df['Algorithm'].values.tolist())

        algo_runtimes = pattern_df['Mean runtime'].values
        best_algo_runtime = np.min(algo_runtimes)

        for algo in algos:
            algo_df = pattern_df[pattern_df['Algorithm'] == algo]
            algo_runtimes = algo_df['Mean runtime'].values
            print(algo_runtimes)
            assert(len(algo_runtimes) == 1)

            slowdown_algo_runtime = algo_runtimes[0] / best_algo_runtime
            slowdown_results.append([ty, pattern, algo, slowdown_algo_runtime])

all_slowdown_df = pd.DataFrame(slowdown_results, columns=['Type', 'Pattern', 'Algorithm', 'Average slowdown'])
all_slowdown_df.to_csv(f"{prefix}_slowdown_benchmark_results.csv", index=False)
