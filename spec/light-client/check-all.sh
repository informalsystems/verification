#!/bin/bash

for INV in PrecisionInv NoDupsInv StoredHeadersAreSoundOrNonTrusted; do
    sed "s/<invariant>/$INV/" <MC1.cfg >MC1-${INV}.cfg
done

for file in MC1-PrecisionInv MC1-NoDupsInv MC1-StoredHeadersAreSoundOrNonTrusted; do
  ../../auto/tlc-hauself $file.cfg MC1.tla
done

