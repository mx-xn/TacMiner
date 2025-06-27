#!/usr/bin/env python3

import json
import argparse
from collections import defaultdict


def load_json(file_path):
    with open(file_path, 'r') as f:
        return json.load(f)


def extract_tactic_usage_examples(tactic_index, trace_data):
    # Get all custom tactics from the tactic index
    custom_tactics = set()
    for file_tactics in tactic_index['custom_tactics'].values():
        for (tactic_name, theorem_tactics) in file_tactics.items():
            print(tactic_name, theorem_tactics)
            custom_tactics.add(tactic_name)
            # update(tactic['name'] for tactic in theorem_tactics['available_tactics'])

    # Initialize a dictionary to store usage examples for each custom tactic
    usage_examples = defaultdict(list)

    # Process the trace data
    for lemma in trace_data:
        lemma_name = lemma['lemma_name']
        for step in lemma['proof']:
            tactic_name = step['tactic_sig_no_out_arg'].split()[0]
            if tactic_name in custom_tactics:
                print("tactic_name:", tactic_name)
                usage_examples[tactic_name].append({
                    'lemma_name': lemma_name,
                    'tactic_sig': step['tactic_sig'],
                    'tactic_args': step['tactic_args'],
                    'tactic_res': step['tactic_res']
                })

    # Print how many examples were extracted for each custom tactic.
    for tactic_name, examples in usage_examples.items():
        print(f"Extracted {len(examples)} examples for {tactic_name}")

    return usage_examples


def main():
    parser = argparse.ArgumentParser(description="Extract tactic usage examples from trace data")
    parser.add_argument("tactic_index", help="Path to the tactic index JSON file")
    parser.add_argument("trace_file", help="Path to the trace JSON file")
    parser.add_argument("output_file", help="Path to the output JSON file")
    args = parser.parse_args()

    tactic_index = load_json(args.tactic_index)
    trace_data = load_json(args.trace_file)
    print(f"Type of tactic_index: {type(tactic_index)}")
    print(f"Type of trace_data: {type(trace_data)}")


    usage_examples = extract_tactic_usage_examples(tactic_index, trace_data)

    # Write the usage examples to the output file
    with open(args.output_file, 'w') as f:
        json.dump(usage_examples, f, indent=2)

    print(f"Tactic usage examples have been written to {args.output_file}")


if __name__ == "__main__":
    main()