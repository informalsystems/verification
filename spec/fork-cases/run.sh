#!/bin/sh
#
# The script to run all experiments at once

SCRIPTS_DIR=~/devl/apalache-tests/scripts \
    BUILDS="unstable card" \
    BENCHMARK=001indinv-apalache \
    make -e -f ~/devl/apalache-tests/Makefile.common
