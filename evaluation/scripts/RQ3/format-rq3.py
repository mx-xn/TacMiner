#!/usr/bin/env python3
import os
import json
from pathlib import Path
from collections import defaultdict
import shutil

# Domains and modes
domains = ["coq_art", "bignums", "comp_cert"]
# mode_key -> column label
modes = {
    "": "vanilla-copra",
    "peano": "copra + peano",
    "tacminer": "copra + tacminer",
}

# Collect results: results[domain][mode_key] = (found, total)
results = {d: {} for d in domains}

for d in domains:
    for mode_key in modes:
        # checkpoint subdir: domain[_mode]
        cp = f"{d}_{mode_key}" if mode_key else d
        ckpt_dir = Path("copra/.log/checkpoints") / cp / "n_60_dfs_gpt4_o_always_retrieve/coq_dfs_always_retrieve"
        ckpt_file = ckpt_dir / "checkpoint_info.json"
        if not ckpt_file.exists():
            raise FileNotFoundError(f"Missing checkpoint_info.json in {ckpt_dir}")
        ckpt = json.load(ckpt_file.open())
        # locate proof_results.json
        proof_dir = Path("copra/" + ckpt["proof_dump_dir"])
        proof_file = proof_dir / "proof_results.json"
        # --- COPY + RENAME ---
        out_dir = Path(f"./evaluation/results/RQ3-proof-automation/{mode_key or 'vanilla'}")
        out_dir.mkdir(exist_ok=True)
        shutil.copy(
            proof_file,
            out_dir/f"proof_results_{d}.json"
        )
        # -----------------------
        if not proof_file.exists():
            raise FileNotFoundError(f"Missing proof_results.json in {proof_dir}")
        proof = json.load(proof_file.open())
        tm = proof.get("theorem_map", {})
        found = total = 0
        # count lemmas
        for filemap in tm.values():
            for lemma_data in filemap.values():
                total += 1
                if lemma_data.get("proof_found"):
                    found += 1
        results[d][mode_key] = (found, total)

# Compute overall totals
# total proofs per domain should be same across modes; take from vanilla
domain_totals = {d: results[d][""][1] for d in domains}
overall_total = sum(domain_totals.values())
overall_found = {mode: sum(results[d][mode][0] for d in domains) for mode in modes}

# Prepare table
col_labels = [modes[k] for k in modes]
# compute column widths
domain_col = max(len(d.replace("_", "-")) for d in domains) + 2
col_widths = [max(len(lbl), 7) + 2 for lbl in col_labels]

# build header
header = f"{'':<{domain_col}}"
for lbl, w in zip(col_labels, col_widths):
    header += f"| {lbl:^{w-2}} "
header += "\n"

# separator
sep = "-" * len(header) + "\n"

# rows per domain
rows = ""
for d in domains:
    disp_d = d.replace("_", "-")
    row = f"{disp_d:<{domain_col}}"
    for i, mode_key in enumerate(modes):
        fnd, tot = results[d][mode_key]
        cell = f"{fnd}/{tot}"
        w = col_widths[i]
        row += f"| {cell:^{w-2}} "
    rows += row + "\n"

# total row
total_row = f"{'total':<{domain_col}}"
for i, mode_key in enumerate(modes):
    fnd = overall_found[mode_key]
    cell = f"{fnd}/{overall_total}"
    w = col_widths[i]
    total_row += f"| {cell:^{w-2}} "
total_row += "\n"

# compose table
table = "number of proofs found / total proofs\n\n"
table += header + sep + rows + sep + total_row

# write out
out_dir = Path("./evaluation/results/RQ3-proof-automation")
out_dir.mkdir(parents=True, exist_ok=True)
with open(out_dir / "summary.txt", "w") as f:
    f.write(table)

print(f"Summary written to {out_dir/'summary.txt'}")