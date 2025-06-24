#!/usr/bin/env python3

import os
import csv
import sys

def collect_rates(folder_path):
    rates = {}
    for filename in os.listdir(folder_path):
        if filename.endswith(".csv"):
            topic = filename[:-4]
            file_path = os.path.join(folder_path, filename)
            with open(file_path, 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    try:
                        rate = float(row['compression_rate'])
                        rates[topic] = rate
                        break
                    except (ValueError, KeyError):
                        continue
    return rates

def print_comparison(rates1, rates2):
    header_topic = "topic"
    header_f1 = "CR-tacminer"
    header_f2 = "CR-baseline"

    col_topic = max(len(header_topic), max(len(t) for t in rates1))
    col_rate = max(len(header_f1), len(header_f2), 12)

    print(f"{header_topic:<{col_topic}} | {header_f1:>{col_rate}} | {header_f2:>{col_rate}}")
    print("-" * (col_topic + 3 + col_rate + 3 + col_rate))

    total1 = total2 = 0.0
    count = 0

    for topic in sorted(rates1):
        r1 = rates1[topic]
        r2 = rates2.get(topic, float('nan'))
        print(f"{topic:<{col_topic}} | {r1:>{col_rate}.2f} | {r2:>{col_rate}.2f}")
        total1 += r1
        total2 += r2
        count += 1

    if count > 0:
        avg1 = total1 / count
        avg2 = total2 / count
        print("-" * (col_topic + 3 + col_rate + 3 + col_rate))
        print(f"{'average':<{col_topic}} | {avg1:>{col_rate}.2f} | {avg2:>{col_rate}.2f}")
    else:
        print("No valid data to compute averages.")

if __name__ == "__main__":
    work_dir = os.path.dirname(os.path.abspath(__file__)) + "/../../results/RQ2-compression-rate/"
    folder1 = work_dir + "tacminer/"
    folder2 = work_dir + "baseline/"

    rates1 = collect_rates(folder1)
    rates2 = collect_rates(folder2)

    missing = set(rates1.keys()) ^ set(rates2.keys())
    if missing:
        print("⚠️ Warning: Some topics are missing in one of the folders:", missing)

    print_comparison(rates1, rates2)
