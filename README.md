# Code Artifact for TacMiner
Automated Discovery of Tactic Libraries for Interactive Theorem Proving

# Code Artifact for TacMiner

## Overview

This repository contains the code artifact supporting the evaluation section of the paper **"Automated Discovery of Tactic Libraries for Interactive Theorem Proving."** This artifact enables reproducibility of key experimental claims, specifically:

1. **TacMiner** learns significantly more (~3×) tactics than the anti-unification-based baseline (e.g., Peano), enabling more concise proofs. (Section 8.2)
2. **TacMiner** achieves higher proof corpus compression, reducing proof size by 26% compared to 9% achieved by baselines. (Section 8.3)
3. Custom tactics discovered by TacMiner improve downstream proof automation, boosting success rates of automation tools like Copra by up to 172%. (Section 8.4)
4. **TacMiner** exhibits strong data efficiency, achieving significant compression with descreased size of training data. (Section 8.5)
5. Ablation studies validate the importance of grammar learning and pruning for tractable search and performance. (Section 8.6)

This artifact supports these claims by including the code, benchmarks, and running scripts for reproducing the results. 

## Getting Started Guide

This artifact may be run via a prebuilt Docker image (recommended) or from source.

### Building and Running the Docker Image

Docker setup is recommended for consistency and ease. Allocate at least 16GB RAM and 4 CPU cores. It takes around 20 min for it to complete building.

```bash 
docker build -t tacminer:v1 .
docker run --rm -it tacminer:v1 bash
```

### Set-up
Once in the docker container, we have a few more setup steps to do:

```bash
# activate conda
source /opt/conda/etc/profile.d/conda.sh
conda activate tacminer

# run the setup script
./src/scripts/setup.sh

# install dependencies
conda install conda-forge::matplotlib
conda install pandas
conda install -c conda-forge grpcio
```

## Step-by-Step Instructions

### Reproducing Claim #1 (Section 8.2): 

- **Run TacMiner (fast):**
   ```bash
   ./run.sh rq1 0

- **Run Peano baseline (slower)**:

   ```bash
    ./run.sh rq1 1
- Once both of the above finish running, format the results:

   ```bash
    ./run.sh rq1-format

See results/RQ1-tactics-stats/summary.txt for the statistics and data needed to reproduce the findings from Section 8.2.

# TODO
Note that <numbers are different>


### Reproducing Claim #2 (Section 8.3): 

- **Run TacMiner (fast):**
   ```bash
   ./run.sh rq2 0
- Run Peano baseline (slower):

   ```bash
    ./run.sh rq2 1
- Once both of the above finish running, format the results:

   ```bash
    ./run.sh rq2-format

See results/RQ2-compression-rate/summary.txt for the compression rate data for Section 8.2.

# TODO
Note that <numbers are different>


### Reproducing Claim #3 (Section 8.4)

#### OpenAI Setup (Optional)
This section uses Copra, a GPT-based proof automation tool.  
- **Recommended:** Use the provided cache for fast, stable results (since GPT outputs may vary across runs).
- **To run without cache:** Add your OpenAI key to `copra/.secrets/openai_key.json`. The entire run takes roughly <>.

#### Running the Experiments

This section evaluates:
1. Vanilla Copra
2. Copra + Peano (baseline)
3. Copra + TacMiner

Use the following commands:

```bash
# 1. Vanilla Copra
./run.sh rq3 0

# 2. Copra + Peano (baseline)
./run.sh rq3 1

# 3. Copra + TacMiner
./run.sh rq3 2
```

Format results after all runs:
./run.sh rq3-format

#### Results
See: `results/RQ3-proof-automation/summary.txt` for the summarized output.

### Reproducing Claim #4 (Section 8.5)
Section 8.5 examines how well TacMiner performs when less training data is available, reporting compression rates as training set size decreases.

#### How to Run

1. **Start the experiment:**
   ```bash
   ./run.sh rq4

2. **Format the results:**
   ```bash
   ./run.sh format-rq4 

#### Outputs

- Tabular/text summary:

`./evaluation/RQ4-data-efficiency/summary.txt`

- Plot of results:

` ./evaluation/RQ4-data-efficiency/summary.png`

### Reproducing Claim #5 (Section 8.6)

Section 8.6 evaluates the importance of both the pruning and grammar learning techniques used in TacMiner.  
We compare three settings:
- **Both pruning and grammar learning enabled (default)**
- **No pruning**
- **No grammar learning**

Experiments report the cumulative time to extract tactics in each configuration, broken down by domain.

#### Running the Experiments

To run each configuration:

```bash
# 1. Without pruning
./run.sh rq5 0

# 2. Without grammar learning
./run.sh rq5 1
```

After all runs complete, format the results:

```bash
./run.sh format-rq5
```

#### Viewing Results

For each domain (e.g., ProgramLogic, CompCert, CoqArt, etc.):

- Tabular/text summary: `./evaluation/RQ5-ablation/<domain>.txt`

- Plots: `./evaluation/RQ5-ablation/<domain>.png`

