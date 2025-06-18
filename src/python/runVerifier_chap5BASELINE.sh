filename="chap5"
domain="coq-art"
echo "Filename: $filename"
echo "Domain: $domain"


source /Users/maxxin-admin/miniconda3/etc/profile.d/conda.sh
conda activate myenv
python3 proof_validity_check.py --filename $filename --domain $domain