import shutil

plot_types = ['scaling', 'single_size']
data_types = ['u64', 'f128', '1k', 'string']
bench_types = ["pivot", "partition", "unstable_smallsort", "merge_policy", "merge_routine", "stable_smallsort"]
target_size = '1000000'
target_pattern = 'random'


def scaling_select(root_path, out_path):
    scaling_dir_path = f"{root_path}/scaling"
    out_dir_path = f"{out_path}_scaling.png"
    target_path = f"{scaling_dir_path}/hot-u64-scaling-{target_pattern}.png"

    shutil.copy(target_path, out_dir_path)

    print(f"saved image to {out_dir_path}")

def single_size_select(root_path, out_path):
    scaling_dir_path = f"{root_path}/single_size"
    out_dir_path = f"{out_path}_single_size.png"
    target_path = f"{scaling_dir_path}/hot-u64-{target_size}.png"

    shutil.copy(target_path, out_dir_path)

    print(f"saved image to {out_dir_path}")

for bench_type in bench_types:
    path = f"analysis/{bench_type}_full_firestorm"
    out_path = f"selected_analysis/{bench_type}"

    scaling_select(path, out_path)
    single_size_select(path, out_path)
