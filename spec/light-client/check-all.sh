#!/bin/bash

for INV in PrecisionInv NoDupsInv StoredHeadersAreSoundOrNotTrusted; do
    sed "s/<invariant>/$INV/" <MC1.cfg >MC1-${INV}.cfg
    ../../auto/tlc-hauself MC1-$INV.cfg MC4nodes3blocks.tla
done

for PROP in Termination Correctness; do
    sed "s/<property>/$PROP/" <MC2.cfg >MC2-${PROP}.cfg
    ../../auto/tlc-hauself MC2-$PROP.cfg MC4nodes3blocks.tla
done

