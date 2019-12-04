#!/bin/bash

# MWE specs that have four nodes
for INV in PrecisionInv NoDupsInv StoredHeadersAreSoundOrNotTrusted; do
    sed "s/<invariant>/$INV/" <MC1.cfg >MC1-${INV}.cfg
    ../../auto/tlc-hauself MC1-$INV.cfg MC4nodes3blocks.tla
done

