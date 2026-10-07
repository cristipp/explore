#!/bin/bash
# usage: bench.sh file  (env passes through)
F=$1
s=$(python3 -c "import time;print(time.time())")
VERBOSE=1 ./target/release/factor --time-limit ${TL:-60} < $F 2>&1 | grep -E "done|answer" | tr '\n' ' '
e=$(python3 -c "import time;print(time.time())")
python3 -c "print('total %.1f'%($e-$s))"
