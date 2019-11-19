#!/bin/bash

for file in MC1 MC2 MC3 MC4; do
  ../../auto/tlc-hauself $file.cfg $file.tla
done

