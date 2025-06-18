#!/bin/bash

# Usage: ./run_dream_prover.sh <domain> <filename> [timeout] [train-portion]

# Check required arguments
if [ "$#" -lt 2 ]; then
    echo "Usage: $0 <domain> <filename> [timeout] [train-portion]"
    exit 1
fi

DOMAIN="$1"
FILENAME="$2"
TRAIN_PORTION="${3:-100}"   # Default train portion is 100
TIMEOUT="${4:-600}"         # Default timeout is 600 seconds

# Run the Java program
java -jar dream-prover.jar "$TIMEOUT" "$DOMAIN" "$FILENAME" "$TRAIN_PORTION"