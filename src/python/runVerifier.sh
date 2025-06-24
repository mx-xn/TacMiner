filename="{{filename}}"
domain="{{domain}}"
echo "Filename: $filename"
echo "Domain: $domain"


source /opt/homebrew/Caskroom/miniconda/base/etc/profile.d/conda.sh
conda activate tacminer
python3 proof_validity_check.py --filename $filename --domain $domain