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
from operator import indexOf

args = sys.argv[1:]
filename = args[0]
prefix = args[1]
groups = parse_bench_results([filename])
results = []
mean_results = []
slowdown_results = []
type_slowdown_results = []
algo_slowdown_results = []

for ty, val1 in groups.items():
    for prediction_state, val2 in val1.items():
        for size, val3 in val2.items():
            for pattern, val4 in val3.items():
                for algo, runtime in val4.items():
                    results.append([ty, size, pattern, algo, runtime / size])

all_df = pd.DataFrame(results, columns=['Type', 'Size', 'Pattern', 'Algorithm', 'Runtime'])
# all_df.to_csv('all_benchmark_results.csv', index=False)

types = set(all_df['Type'].values.tolist())
algos = set(all_df['Algorithm'].values.tolist())

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
# all_mean_df.to_csv(f"{prefix}_mean_benchmark_results.csv", index=False)

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
            assert(len(algo_runtimes) == 1)

            slowdown_algo_runtime = algo_runtimes[0] / best_algo_runtime
            slowdown_results.append([ty, pattern, algo, slowdown_algo_runtime])

all_slowdown_df = pd.DataFrame(slowdown_results, columns=['Type', 'Pattern', 'Algorithm', 'Average slowdown'])
# all_slowdown_df.to_csv(f"{prefix}_slowdown_benchmark_results.csv", index=False)

# naudingiausia butu lentele, kur yra fiksuotas input type ir tada slowdownai kiekvieno algoritmo

for ty in types:
    type_df = all_slowdown_df[all_slowdown_df['Type'] == ty]
    algos = set(type_df['Algorithm'].values.tolist())

    for algo in algos:
        algo_df = type_df[type_df['Algorithm'] == algo]
        algo_slowdowns = algo_df['Average slowdown'].values
        algo_geom_mean_slowdown = np.exp(np.mean(np.log(algo_slowdowns)))
        type_slowdown_results.append([ty, algo, algo_geom_mean_slowdown])

type_slowdown_df = pd.DataFrame(type_slowdown_results, columns=['Type', 'Algorithm', 'Geometric average slowdown'])
type_slowdown_df_pivot = type_slowdown_df.pivot(index='Type', columns='Algorithm', values='Geometric average slowdown')
type_slowdown_df_pivot.insert(0, 'Type', type_slowdown_df_pivot.index)

types_order = ['u64', 'f128', '1k', 'string', 'general']
def order_fn(x):
    return types_order.index(x)

vectorized_order_fn = np.vectorize(order_fn)
result_df = type_slowdown_df_pivot.reset_index(drop=True)
result_df = result_df.sort_values(by='Type', key=vectorized_order_fn)

result_df.to_csv(f"tables/{prefix}_type_slowdown_benchmark_results.csv", float_format='%.2f', index=False)
