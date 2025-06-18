#!/bin/bash

# Define the common part of the command
JAR_FILE="dream-prover.jar"
TIMEOUT=1800
MODE=2
#MODE=3 # change for different ablations
TRAIN=100
FLAG=False

# Define the list of arguments for each run
commands=(
    "CompCert Allocation"
    "CompCert NeedDomain"
    "CompCert RTLgenspec"
    "CompCert Debugvarproof"
    "bignums NMake"
    "bignums ZMake"
    "bignums QMake"
    "cdf Separation"
    "cdf Seplog"
    "cdf CSL"
    "cdf Hoare"
    "coq-art chap3"
    "coq-art chap8"
    "coq-art chap11"
    "coq-art chap16"
)

# Loop through the commands and execute them one by one
for cmd in "${commands[@]}"; do
    echo "Running: java -jar $JAR_FILE $TIMEOUT $MODE $cmd $TRAIN $FLAG"
    java -jar "$JAR_FILE" "$TIMEOUT" "$MODE" $cmd "$TRAIN" "$FLAG"
done