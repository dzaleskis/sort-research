import matplotlib.pyplot as plt
import pandas as pd
import sys

args = sys.argv[1:]
prefix = args[0]

# Read the data from the CSV file
df = pd.read_csv(f"tables/{prefix}_combined_slowdown_benchmark_results.csv")

labels = df['Algorithm']
values = df['Geometric average slowdown']

# Plot the data
fig, ax = plt.subplots()
ax.bar(labels, values, color=['blue', 'green', 'red', 'purple', 'orange', 'yellow'])

# Set labels
ax.set_ylabel('Combined slowdown')
ax.tick_params(axis='x', labelrotation=90)
# ax.set_ylim(0.5, max(values) + 0.2)

# Draw a horizontal line at y=1
ax.axhline(y=1)


plt.tight_layout()

# Save the plot as an image file
plt.savefig(f"combined/{prefix}_combined.png", bbox_inches='tight')
