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


# Mapping to pretty names
pretty_algo_names = {
    "cpp_ips4o_unstable": "Ips4o",
    "cpp_pdqsort_unstable": "Pdqsort",
    "cpp_std_sys_unstable": "C++ Unstable",
    "rust_ipnsort_unstable": "Ipnsort",
    "rust_max_quicksort_unstable": "Max Quicksort",
    "rust_std_vendored_unstable": "Rust Unstable",

    "c_quadsort_stable": "Quadsort",
    "cpp_powersort_4way_stable": "Powersort 4-Way",
    "cpp_powersort_stable": "Powersort",
    "cpp_std_sys_stable": "C++ Stable",
    "cpp_timsort_stable": "Timsort",
    "rust_max_mergesort_stable": "Max Mergesort",
    "rust_std_vendored_stable": "Rust Stable",

    "c_crumsort_unstable_synergistic": "Crumsort",
    "c_fluxsort_stable_synergistic": "Fluxsort",
    "rust_driftsort_stable_synergistic": "Driftsort",
    "rust_glidesort_stable_synergistic": "Glidesort",
    "rust_max_stable_synergistic": "Max Synergistic Stable",
    "rust_max_unstable_synergistic": "Max Synergistic Unstable"
}

skipped_patterns = ['ascending', 'descending']

args = sys.argv[1:]
filename = args[0]
prefix = args[1]
groups = parse_bench_results([filename])
results = []
mean_results = []
slowdown_results = []
type_slowdown_results = []
pattern_slowdown_results = []
combined_slowdown_results = []

for ty, val1 in groups.items():
    for prediction_state, val2 in val1.items():
        for size, val3 in val2.items():
            for pattern, val4 in val3.items():
                for algo, runtime in val4.items():
                    algo_pretty = pretty_algo_names[algo]
                    if not pattern in skipped_patterns:
                        results.append([ty, size, pattern, algo_pretty, runtime / size])

all_df = pd.DataFrame(results, columns=['Type', 'Size', 'Pattern', 'Algorithm', 'Runtime'])

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

# pattern slowdowns

for pattern in patterns:
    pattern_df = all_slowdown_df[all_slowdown_df['Pattern'] == pattern]
    algos = set(pattern_df['Algorithm'].values.tolist())

    for algo in algos:
        algo_df = pattern_df[pattern_df['Algorithm'] == algo]
        algo_slowdowns = algo_df['Average slowdown'].values
        algo_geom_mean_slowdown = np.exp(np.mean(np.log(algo_slowdowns)))
        pattern_slowdown_results.append([pattern, algo, algo_geom_mean_slowdown])

pattern_slowdown_df = pd.DataFrame(pattern_slowdown_results, columns=['Pattern', 'Algorithm', 'Geometric average slowdown'])
pattern_slowdown_df_pivot = pattern_slowdown_df.pivot(index='Pattern', columns='Algorithm', values='Geometric average slowdown')
pattern_slowdown_df_pivot.insert(0, 'Pattern', pattern_slowdown_df_pivot.index)
pattern_slowdown_df = pattern_slowdown_df_pivot.reset_index(drop=True)

patterns_ordered = ['ascending', 'descending', 'random', 'random_d20', 'random_m50', 'random_p5', 'random_s95', 'random_z1', 'general']
def pattern_order_fn(x):
    try:
        return patterns_ordered.index(x)
    except ValueError:
        return 1000;

vectorized_pattern_order_fn = np.vectorize(pattern_order_fn)
pattern_slowdown_df = pattern_slowdown_df.sort_values(by='Pattern', key=vectorized_pattern_order_fn)
pattern_slowdown_df.to_csv(f"tables/{prefix}_pattern_slowdown_benchmark_results.csv", float_format='%.2f',  index=False)

# type slowdowns

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
type_slowdown_df = type_slowdown_df_pivot.reset_index(drop=True)

types_ordered = ['u64', 'f128', '1k', 'string', 'general']
def types_order_fn(x):
    try:
        return types_ordered.index(x)
    except ValueError:
        return 1000;

vectorized_types_order_fn = np.vectorize(types_order_fn)
type_slowdown_df = type_slowdown_df.sort_values(by='Type', key=vectorized_types_order_fn)
type_slowdown_df.to_csv(f"tables/{prefix}_type_slowdown_benchmark_results.csv", float_format='%.2f', index=False)

# combined slowdowns

for algo in algos:
    algo_df = all_slowdown_df[all_slowdown_df['Algorithm'] == algo]
    algo_slowdowns = algo_df['Average slowdown'].values
    algo_geom_mean_slowdown = np.exp(np.mean(np.log(algo_slowdowns)))
    combined_slowdown_results.append(['combined', algo, algo_geom_mean_slowdown])

combined_slowdown_df = pd.DataFrame(combined_slowdown_results, columns=['Type', 'Algorithm', 'Geometric average slowdown'])
combined_slowdown_df.to_csv(f"tables/{prefix}_combined_slowdown_benchmark_results.csv", float_format='%.2f',  index=False)

def format_row(row):
    row_template = ""
    filtered_list = [item for item in list(row) if not isinstance(item, str)]

    # TODO: highlight min values
    for j in range(0, len(row)):
        value = row[j]
        if str(value) != value:
            is_min = np.min(filtered_list) == value
            value = format(value, ".2f")
            if is_min:
                value = f"\\textbf{{{value}}}"
        else:
            value = value.replace("_", "\\_")
            value = value.replace(" ", " \\newline ")

        row_template += f" {value} "

        if j == len(row)-1:
            row_template += "\\\\ \\hline"
        else:
            row_template += "&"

    return row_template

def to_latex(df, category):
    columns = len(df.columns)
    rows = len(df)

    columns_template = ""

    for i in range(0, columns):
        if i == 0:
            columns_template += "l"
        else:
            columns_template += "|X"

    rows_template = ""
    rows_template += format_row(df.columns) + "\n"

    for i in range(0, rows):
        rows_template += format_row(df.iloc[i])

        if i != rows-1:
            rows_template += "\n"

    template=f"""
\\begin{{table}}[H]
\\centering
\\begin{{tabularx}}{{\\textwidth}}{{|{columns_template}|}}
\\hline
{rows_template}
\\end{{tabularx}}
\\caption{{Slowdown of {prefix} based on input data {category}}}
\\label{{tab:{prefix}_{category}s}}
\\end{{table}}
    """

    return template

print(to_latex(type_slowdown_df, "type"))

with open(f"latex_tables/{prefix}_type_slowdown_benchmark_results.latex", "w") as file:
    file.write(to_latex(type_slowdown_df, "type"))

with open(f"latex_tables/{prefix}_pattern_slowdown_benchmark_results.latex", "w") as file:
    file.write(to_latex(pattern_slowdown_df, "pattern"))
