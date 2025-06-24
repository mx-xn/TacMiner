#!/usr/bin/env python3

import os
import sys
import csv
from collections import defaultdict

import matplotlib.pyplot as plt

def plot_averages(headers, avg_values, output_path):
    x = list(map(float, headers))
    y = avg_values

    plt.figure(figsize=(10, 5))
    plt.plot(x, y, marker='o', color='blue', linestyle='-', linewidth=2, markersize=5)
    plt.title("Average Compression Rate per Training Portion")
    plt.xlabel("Training Portion")
    plt.ylabel("Average Compression Rate")
    plt.grid(True)
    plt.xticks(x, rotation=45)
    plt.tight_layout()
    plt.savefig(output_path, dpi=300)
    plt.close()

def parse_file(filepath):
    with open(filepath, 'r') as f:
        reader = csv.reader(f)
        rows = list(reader)

    header = rows[0][1:]  # skip "ComprRate-per-TrainPortion"
    num_cols = len(header)

    round_values = []
    for row in rows[1:]:
        try:
            values = list(map(float, row[1:]))
            if len(values) != num_cols:
                continue  # Skip malformed row
            round_values.append(values)
        except ValueError:
            continue

    # Compute average across rounds, per column
    averaged = [round(sum(col) / len(col), 3) for col in zip(*round_values)]
    return header, averaged

def format_table(headers, data_dict):
    col_width = 7
    topic_col_width = max(len("topic \\ CR per train portion"), max(len(k) for k in data_dict))

    # Header
    header_label = "topic \\ CR per train portion"
    header_line = f"{header_label:<{topic_col_width}} |"

    for h in headers:
        header_line += f" {float(h):>{col_width}.2f}"
    print(header_line)

    # Extra separator after header
    print("-" * (topic_col_width + 3 + (col_width + 1) * len(headers)))

    # Data rows
    all_averages = []
    for topic, values in sorted(data_dict.items()):
        all_averages.append(values)
        row = f"{topic:<{topic_col_width}} |" + "".join(f" {v:>{col_width}.2f}" for v in values)
        print(row)

    # Separator before average
    print("-" * (topic_col_width + 3 + (col_width + 1) * len(headers)))

    # Average row
    if all_averages:
        avg_per_col = [sum(col) / len(col) for col in zip(*all_averages)]
        avg_row = f"{'average':<{topic_col_width}} |" + "".join(f" {v:>{col_width}.2f}" for v in avg_per_col)
        print(avg_row)

        output_path = os.path.dirname(os.path.abspath(__file__)) + "/../../results/RQ4-data-efficiency/summary_plot.png"
        plot_averages(headers, avg_per_col, output_path)


if __name__ == "__main__":
    work_dir = os.path.dirname(os.path.abspath(__file__)) + "/../../results/RQ4-data-efficiency/"
    summary_data = {}
    portion_header = None

    for filename in os.listdir(work_dir):
        if filename.endswith(".csv"):
            topic = os.path.splitext(filename)[0]
            filepath = os.path.join(work_dir, filename)
            try:
                headers, averaged = parse_file(filepath)
                summary_data[topic] = averaged
                portion_header = headers  # all files should have same headers
            except Exception as e:
                print(f"Failed to process {filename}: {e}")

    if not summary_data:
        print("No valid files found.")
    else:
        format_table(portion_header, summary_data)
