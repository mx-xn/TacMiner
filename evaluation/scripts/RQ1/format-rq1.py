import os
import csv
from collections import defaultdict

# ========== CONFIGURATION ==========

work_dir = os.path.dirname(os.path.abspath(__file__)) + "/../../results/RQ1-tactics-stats/"
tool1_name = "tacminer"
tool2_name = "baseline"
folder1 = work_dir + tool1_name + "/"
folder2 = work_dir + tool2_name + "/"
# output_file = "tactic_stats_summary.txt"

# Mapping topic name to domain name (customize as needed)
domain_map = {
    "IndPred": "CoqArt",
    "SearchTree": "CoqArt",
    "Reflection": "CoqArt",
    "Hoare": "Program Logics",
    "Separation": "Program Logics",
    "Seplog": "Program Logics",
    "CSL": "Program Logics",
    "RegAlloc": "CompCert",
    "LiveRange": "CompCert",
    "AbsDomain": "CompCert",
    "RTLSpec": "CompCert",
    "NMake": "BigNums",
    "ZMake": "BigNums",
    "QMake": "BigNums",
}

# ========== LOADING ==========

def read_stats(folder):
    stats = {}
    for fname in os.listdir(folder):
        if not fname.endswith(".csv"):
            continue
        topic = fname[:-4]
        with open(os.path.join(folder, fname)) as f:
            reader = csv.DictReader(f)
            row = next(reader)
            stats[topic] = {
                "tactics": int(row["tactics_learned"]),
                "avg_size": float(row["avg_tactic_size"]),
                "max_size": int(row["max_tactic_size"]),
                "usage": int(row["tactic_usage_count"]),
            }
    return stats

tool1_stats = read_stats(folder1)
tool2_stats = read_stats(folder2)

# ========== AGGREGATION ==========

grouped = defaultdict(list)
all_topics = sorted(tool1_stats.keys())

for topic in all_topics:
    domain = domain_map.get(topic, "Other")
    tool1 = tool1_stats[topic]
    tool2 = tool2_stats[topic]
    grouped[domain].append((topic, tool1, tool2))

# ========== FORMAT & WRITE ==========

def format_row(domain, topic, tool, stats, show_domain=False, show_topic=False):
    return f"{domain if show_domain else '':<14} | {topic if show_topic else '':<12} | {tool:<8} | {stats['tactics']:>8} | {stats['avg_size']:>7.1f} | {stats['max_size']:>8} | {stats['usage']:>11}"

print("Domain         | Topic       | Tool     | #Tactics | AvgSize | MaxSize | UsageCount")
print("-" * 86)

total_tool1 = {"tactics": 0, "avg_size": [], "max_size": 0, "usage": 0}
total_tool2 = {"tactics": 0, "avg_size": [], "max_size": 0, "usage": 0}

for domain in grouped:
    for topic, stats1, stats2 in grouped[domain]:
        print(format_row(domain, topic, tool1_name, stats1, show_domain=True, show_topic=True))
        print(format_row("", "", tool2_name, stats2))
        print("-" * 86)

        # Accumulate for overall
        total_tool1["tactics"] += stats1["tactics"]
        total_tool1["avg_size"].append(stats1["avg_size"])
        total_tool1["max_size"] = max(total_tool1["max_size"], stats1["max_size"])
        total_tool1["usage"] += stats1["usage"]

        total_tool2["tactics"] += stats2["tactics"]
        total_tool2["avg_size"].append(stats2["avg_size"])
        total_tool2["max_size"] = max(total_tool2["max_size"], stats2["max_size"])
        total_tool2["usage"] += stats2["usage"]

print("-" * 86)
print(format_row("Overall", "", tool1_name, {
    "tactics": total_tool1["tactics"],
    "avg_size": sum(total_tool1["avg_size"]) / len(total_tool1["avg_size"]),
    "max_size": total_tool1["max_size"],
    "usage": total_tool1["usage"]
}, show_domain=True))

print(format_row("", "", tool2_name, {
    "tactics": total_tool2["tactics"],
    "avg_size": sum(total_tool2["avg_size"]) / len(total_tool2["avg_size"]),
    "max_size": total_tool2["max_size"],
    "usage": total_tool2["usage"]
}))

# # ========== DONE ==========

# print(f"✅ Table written to: {output_file}")
