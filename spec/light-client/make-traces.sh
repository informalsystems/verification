#!/bin/bash
#
# Produce multiple counterexamples by running TLC

for INV in NeverFinishPositive NeverFinishNegative; do
    sed "s/<invariant>/$INV/" <MC1.cfg >MC1-${INV}.cfg
    timeout 60m ../../auto/tlc-hauself MC1-$INV.cfg MC4nodes3blocks.tla \
        -depth 20 -continue # simulation up to depth 20, produce all examples
done

