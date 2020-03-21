#!/bin/bash

# Check the blockchain properties alone
LOG=modelcheck-blockchain.log
echo "" >$LOG

# 2 nodes + 3 blocks, then 4 nodes + 3 blocks
for n in 2 4; do
    for INV in NeverStuck NeverStuckFalse1 NeverStuckFalse2 NeverUltimateHeight; do
        sed "s/<invariant>/$INV/" <BC$n.cfg >BC$n-${INV}.cfg
        echo "Checking BC$n-$INV.cfg BC${n}nodes3blocks.tla"
        ../../auto/tlc-hauself BC$n-$INV.cfg BC${n}nodes3blocks.tla | tee -a $LOG
    done
done

echo "The properties that hold and violated:"
grep "is violated" "$LOG"

NVIOLATED=`grep "is violated." "$LOG" | wc -l`
NHOLD=`grep "No error has been found." "$LOG" | wc -l`

echo ""
echo "$NHOLD invariants hold, $NVIOLATED invariants violated"

