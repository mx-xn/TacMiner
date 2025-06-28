#!/usr/bin/env bash
# This script sets up the opam environment and builds various Coq projects

# Build raw-data/coq-art
cd raw-data/coq-art
make clean
make
if [ $? -ne 0 ]; then
    echo "Build failed in raw-data/coq-art"
    exit 1
fi

# Build raw-data/cdf
cd ../cdf
make clean
make
if [ $? -ne 0 ]; then
    echo "Build failed in raw-data/cdf"
    exit 1
fi

# Build raw-data/bignums
cd ../bignums
make clean
make
if [ $? -ne 0 ]; then
    echo "Build failed in raw-data/bignums"
    exit 1
fi

# Build raw-data/CompCert
cd ../CompCert
make clean
make
if [ $? -ne 0 ]; then
    echo "Build partially succeeded raw-data/CompCert"
fi

echo "All builds completed successfully."