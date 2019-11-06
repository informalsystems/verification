#!/bin/bash

wget -nc https://github.com/tlaplus/tlaplus/releases/download/v1.6.0/tla2tools.jar

java -cp ./tla2tools.jar tlc2.TLC -config MC1.cfg MC1.tla >FinishPositive.out
java -cp ./tla2tools.jar tlc2.TLC -config MC2.cfg MC2.tla >FinishNegative.out
java -cp ./tla2tools.jar tlc2.TLC -config MC3.cfg MC3.tla >Correctness.out
java -cp ./tla2tools.jar tlc2.TLC -config MC4.cfg MC4.tla >Precision.out

