#!/usr/bin/env python3
import os, glob
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from itertools import accumulate

# 1. configuration
BASE_DIR = os.path.abspath(os.path.join(os.getcwd(), "evaluation/results/RQ5-ablation"))
TOOLS = {
    'tacminer':        'tacminer',
    'no_pruning':      'no-pruning-abl',
    'no_grammar':      'no-grammar-abl',
}
DOMAINS = ['coq-art', 'bignums', 'program-logics', 'comp-cert']

# output dirs
OUTPUT_DIR = os.path.dirname(os.path.abspath(__file__)) + "/../../results/RQ5-ablation/" 
data = {tk: {dom: [] for dom in DOMAINS} for tk in TOOLS}

for tk, folder in TOOLS.items():
    for dom in DOMAINS:
        # pattern = os.path.join(BASE_DIR, sub, dom, '*.csv')
        # files = glob.glob(pattern)
        dom_path = BASE_DIR + "/" + folder + "/" + dom
        if not os.path.isdir(dom_path):
            print("cannot find file: ", dom_path)
            continue
        for fn in os.listdir(dom_path):
            print("Processing file:", fn)
            if not fn.lower().endswith('.csv'):
                continue
            path = os.path.join(dom_path, fn)
            df = pd.read_csv(path)
            # compute unit_time (ms)
            df = df.sort_values('numTacs')
            df['unit_time_ms'] = df['Time'].diff().fillna(df['Time'])
            # collect
            data[tk][dom].extend(df['unit_time_ms'].astype(float).tolist())

# sort and convert to seconds
for tk in data:
    for dom in data[tk]:
        data[tk][dom] = sorted(data[tk][dom])
        # ms -> s
        data[tk][dom] = [x/1000.0 for x in data[tk][dom]]

# 3. for each domain, build combined table and plot
for dom in DOMAINS:
    # extract per-tool lists
    tm = data['tacminer'][dom]
    np_ = data['no_pruning'][dom]
    ng = data['no_grammar'][dom]
    # upperbound of tactics length. For ablation bug
    N = len(tm)
    if N == 0:
        print(f"→ skipping domain '{dom}' (no tacminer data)")
        continue

    if len(np_) > N:
        np_ = np_[:N]
    if len(ng) > N:
        ng = ng[:N]

    # 1) compute cumulative times (seconds)
    cum_tm = list(accumulate(tm))
    cum_np = list(accumulate(np_))
    cum_ng = list(accumulate(ng))

    # 2) pad & format for table output
    def pad_and_fmt(lst):
        s = [f"{v:.6g}" for v in lst]
        return s + ['']*(N - len(s))

    tm_c = pad_and_fmt(cum_tm)
    np_c = pad_and_fmt(cum_np)
    ng_c = pad_and_fmt(cum_ng)

    # 3) write the pipe‐table with accumulated times
    table_path = os.path.join(OUTPUT_DIR, f"{dom.replace(' ', '_')}.txt")
    with open(table_path, 'w') as fo:
        fo.write("| num_tacs_learned | time(s)_tacminer | time(s)_no_pruning | time(s)_no_grammar |\n")
        fo.write("|------------------|------------------|--------------------|--------------------|\n")
        for i in range(N):
            fo.write(f"| {i+1} | {tm_c[i]} | {np_c[i]} | {ng_c[i]} |\n")
    print("Wrote accumulated‐time table:", table_path)

    # 3b. plot log–log
    plt.figure(figsize=(6,4))
    x = np.arange(1, N+1)
    if tm_c:  plt.plot(x[:len(cum_tm)],  cum_tm,  marker='o', label='tacminer')
    if np_c: plt.plot(x[:len(cum_np)], cum_np, marker='s', label='no_pruning')
    if ng_c:  plt.plot(x[:len(cum_ng)],  cum_ng,  marker='^', label='no_grammar')

    # linear x-axis
    plt.xscale('linear')
    plt.xlim(left=0)

    # symlog y-axis to allow zero + log beyond 1e-3
    # force y-axis to start at zero
    plt.yscale('symlog', linthresh=1e-3)
    plt.ylim(bottom=0)

    # custom y-ticks
    yticks = [0, 1e-1, 1e1, 1e3]
    ylabels = ["0", r"$10^{-1}$", r"$10^{1}$", r"$10^{3}$"]
    plt.yticks(yticks, ylabels)


    plt.xlabel("num_tacs_learned")
    plt.ylabel("time (s)")
    plt.title(dom)
    plt.legend()
    plt.tight_layout()
    png_path = os.path.join(OUTPUT_DIR, f"{dom.replace(' ', '_')}.png")
    plt.savefig(png_path, dpi=150)
    plt.close()