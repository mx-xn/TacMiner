#!/usr/bin/env bash
usage() {
  cat <<EOF
Usage: $0 <command> [mode]

Commands:
  rq1   <0|1>       Run Claim#1: 0 = TacMiner, 1 = Peano
  rq1-format       Format & summarize Claim#1 results

  rq2   <0|1>       Run Claim#2: 0 = TacMiner, 1 = Peano
  rq2-format       Format & summarize Claim#2 results

  rq3   <0|1|2>     Run Claim#3: 0 = Vanilla Copra, 1 = Copra+Peano, 2 = Copra+TacMiner
  rq3-format       Format & summarize Claim#3 results

  rq4               Run Claim#4 (data‐efficiency)
  format-rq4       Format & summarize Claim#4 results

  rq5   <0|1|2>     Run Claim#5: 0 = default, 1 = no pruning, 2 = no grammar
  format-rq5       Format & summarize Claim#5 results

Examples:
  $0 rq1 0
  $0 rq1-format
  $0 rq4
  $0 format-rq4
EOF
  exit 1
}

if [ $# -lt 1 ]; then
  usage
fi

cmd="$1"; shift

case "$cmd" in
  rq1)
    [ $# -eq 1 ] || usage
    mode="$1"
    if [ "$mode" = "0" ]; then
    bash ./evaluation/scripts/RQ1/tacminer-rq1.sh
    else
    bash ./evaluation/scripts/RQ1/baseline-rq1.sh
    fi
    ;;

  rq1-format)
    echo ">>> Formatting RQ1 results..."
    bash ./evaluation/scripts/RQ1/format-rq1.sh
    ;;

  rq2)
    [ $# -eq 1 ] || usage
    mode="$1"
    if [ "$mode" = "0" ]; then
    bash ./evaluation/scripts/RQ2/tacminer-rq2.sh
    else
    bash ./evaluation/scripts/RQ2/baseline-rq2.sh
    fi
    ;;

  rq2-format)
    echo ">>> Formatting RQ2 results..."
    bash ./evaluation/scripts/RQ2/format-rq2.sh
    ;;

  rq3)
    [ $# -eq 1 ] || usage
    mode="$1"
    if [ "$mode" = "0" ]; then
    bash ./evaluation/scripts/RQ3/copra-vanilla-rq3.sh
    elif [ "$mode" = "1" ]; then
    bash ./evaluation/scripts/RQ3/copra-peano-rq3.sh
    else
    bash ./evaluation/scripts/RQ3/copra-tacminer-rq3.sh
    fi

    ;;

  rq3-format)
    echo ">>> Formatting RQ3 results..."
    bash ./evaluation/scripts/RQ3/format-rq3.sh
    ;;

  rq4)
    bash ./evaluation/scripts/RQ4/tacminer-rq4.sh
    ;;

  format-rq4)
    echo ">>> Formatting RQ4 results..."
    bash ./evaluation/scripts/RQ4/format-rq4.sh
    ;;

  rq5)
    [ $# -eq 1 ] || usage
    mode="$1"
    if [ "$mode" = "0" ]; then
    bash ./evaluation/scripts/RQ5/no-pruning-rq5.sh
    else
    bash ./evaluation/scripts/RQ5/no-grammar-rq5.sh
    [ $# -eq 1 ] || usage
    fi
    ;;

  format-rq5)
    echo ">>> Formatting RQ5 results..."
    bash ./evaluation/scripts/RQ5/format-rq5.sh
    ;;

  *)
    usage
    ;;
esac

echo ">>> Done."