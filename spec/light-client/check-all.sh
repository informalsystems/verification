#!/bin/bash

# the small specs that have two nodes only
for INV in PrecisionInv NoDupsInv StoredHeadersAreSoundOrNotTrusted; do
    sed "s/<invariant>/$INV/" <MC3.cfg >MC3-${INV}.cfg
    ../../auto/tlc-hauself MC3-$INV.cfg MC2nodes3blocks.tla
done

for PROP in Termination Correctness; do
    sed "s/<property>/$PROP/" <MC4.cfg >MC4-${PROP}.cfg
    ../../auto/tlc-hauself MC4-$PROP.cfg MC2nodes3blocks.tla
done

# MWE specs that have four nodes
for INV in PrecisionInv NoDupsInv StoredHeadersAreSoundOrNotTrusted; do
    sed "s/<invariant>/$INV/" <MC1.cfg >MC1-${INV}.cfg
    ../../auto/tlc-hauself MC1-$INV.cfg MC4nodes3blocks.tla
done

for PROP in Termination Correctness; do
    sed "s/<property>/$PROP/" <MC2.cfg >MC2-${PROP}.cfg
    ../../auto/tlc-hauself MC2-$PROP.cfg MC4nodes3blocks.tla
done

