if [ -z "$1" ]; then
  echo "Usage: $0 <input>"
  exit 1
fi
BENCHMARK=$1

echo "Running from: $(pwd)"

# Diagram 
nohup python src/main/eval_benchmark.py prompt_settings=coq_dfs_always_retrieve env_settings=bm25_retrieval eval_settings=n_60_dfs_gpt4_o_always_retrieve_no_ex benchmark=$BENCHMARK
