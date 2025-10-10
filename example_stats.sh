#!/bin/bash

LABEL=$1
OUTPUT=$2
DIR=$3

ALL_VOS=$(find $DIR -iname "*.v" | sed 's/$/o/')

if [ -f $DIR.v ]; then
    ALL_VOS="${ALL_VOS} ${DIR}.vo"
fi

# Compile all command arguments, outputting total time to time.out and saving
# the make output to make.out.
/usr/bin/time -o time.out -f "%e" make -f RocqMakefile -j8 $ALL_VOS | tee make.out

# Round time to nearest integer
TIME=$(cat time.out | awk '{print int($1 + 0.5)}')

# Extract all compiled Rocq files into the file deps.out
grep "ROCQ compile " make.out | sed -e 's/ROCQ compile //g' > deps.out

count() {
    xargs wc -l | tail -n 1 | awk '{print $1}'
}

# Compute implementation size
if grep -q "impl.v" deps.out; then
    IMPLLINES=$(grep impl deps.out | count)
else
    IMPLLINES="---"
fi

# Compute proof size
if grep -q "proofs.v" deps.out; then
    PROOFLINES=$(grep proofs deps.out | count)
else
    PROOFLINES="---"
fi

# Compute game size
if grep -q "game.v" deps.out; then
    GAMELINES=$(grep game deps.out | count)
else
    GAMELINES="---"
fi

# Compute total size
TOTALLINES=$(cat deps.out | count)

printf "%s & %s & %s & %s & %s & %s \\\\\\\\ \n" "$1" \
    $IMPLLINES $PROOFLINES $GAMELINES $TOTALLINES $TIME >> $2

rm -f time.out make.out deps.out
