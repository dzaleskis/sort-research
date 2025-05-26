from PIL import Image

plot_types = ['scaling', 'single_size']
data_types = ['u64', 'f128', '1k', 'string']
# bench_types = ["pivot", "partition", "unstable_smallsort", "merge_policy", "merge_routine", "stable_smallsort"]
bench_types = ["stable", "unstable", "synergistic"]
target_size = '1000000'
target_pattern = 'random'

def combine_generic(image1, image2, image3, image4):
    # Get the size of the images
    width1, height1 = image1.size
    width2, height2 = image2.size
    width3, height3 = image3.size
    width4, height4 = image4.size

    # Calculate the size of the combined image
    padding = 20
    total_width = width1*2+padding
    total_height = height1*2+padding

    # Create a new blank image with the calculated size
    combined_image = Image.new("RGBA", (total_width, total_height))

    # Paste the images into the combined image
    combined_image.paste(image1, (0, 0))
    combined_image.paste(image2, (width1+padding, 0))
    combined_image.paste(image3, (0, height1+padding))
    combined_image.paste(image4, (width1+padding, height1+padding))

    return combined_image


def scaling_combine(root_path, out_path):
    scaling_dir_path = f"{root_path}/scaling"
    out_dir_path = f"{out_path}_scaling"

    image1 = Image.open(f"{scaling_dir_path}/hot-u64-scaling-{target_pattern}.png")
    image2 = Image.open(f"{scaling_dir_path}/hot-f128-scaling-{target_pattern}.png")
    image3 = Image.open(f"{scaling_dir_path}/hot-1k-scaling-{target_pattern}.png")
    image4 = Image.open(f"{scaling_dir_path}/hot-string-scaling-{target_pattern}.png")

    combined_image = combine_generic(image1, image2, image3, image4)


    combined_image.save(f"{out_dir_path}_combined.png")
    print(f"saved image to {out_dir_path}")

def single_size_combine(root_path, out_path):
    scaling_dir_path = f"{root_path}/single_size"
    out_dir_path = f"{out_path}_single_size"

    image1 = Image.open(f"{scaling_dir_path}/hot-u64-{target_size}.png")
    image2 = Image.open(f"{scaling_dir_path}/hot-f128-{target_size}.png")
    image3 = Image.open(f"{scaling_dir_path}/hot-1k-{target_size}.png")
    image4 = Image.open(f"{scaling_dir_path}/hot-string-{target_size}.png")

    combined_image = combine_generic(image1, image2, image3, image4)

    combined_image.save(f"{out_dir_path}_combined.png")
    print(f"saved image to {out_dir_path}")

for bench_type in bench_types:
    path = f"analysis/{bench_type}_full_firestorm"
    out_path = f"combined_analysis/{bench_type}"

    scaling_combine(path, out_path)
    single_size_combine(path, out_path)
