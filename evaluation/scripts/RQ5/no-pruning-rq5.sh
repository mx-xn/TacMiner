MAX_TIME=9000
echo "Starting coq-art experiment..."
if timeout ${MAX_TIME}s java -jar tacminer.jar 2 coq-art all 1800 100; then
echo "coq-art experiment finished successfully."
else
echo "coq-art experiment timed out. Killing it and moving on."
fi

echo "Starting program-logics experiment..."
if timeout ${MAX_TIME}s java -jar tacminer.jar 2 program-logics all 1800 100; then
echo "program-logics experiment finished successfully."
else
echo "program-logics experiment timed out. Killing it and moving on."
fi

echo "Starting bignums experiment..."
if timeout ${MAX_TIME}s java -jar tacminer.jar 2 bignums all 1800 100; then
echo "bignums experiment finished successfully."
else
echo "bignums experiment timed out. Killing it and moving on."
fi

echo "Starting comp-cert experiment..."
if timeout ${MAX_TIME}s java -jar tacminer.jar 2 comp-cert all 1800 100; then
echo "comp-cert experiment finished successfully."
else
echo "comp-cert experiment timed out. Killing it and moving to the next command."
fi
