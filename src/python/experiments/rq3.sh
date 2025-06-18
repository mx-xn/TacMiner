cd ../../../
pwd
for ((p=95; p<=95; p+=5))
do
  echo "training portion is: $p%"
  python3 src/python/exp.py --bm_domain CompCert --bm_topic NeedDomain --mode 0 --train_mode 1 --train_portion "$p"
#  python3 src/python/exp.py --bm_domain CompCert --bm_topic all --mode 0 --train_mode 1 --train_portion "$p"
done

