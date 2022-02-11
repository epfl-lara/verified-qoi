#!/bin/bash

stainless-dotty --config-file=stainless.conf \
    common.scala decoder.scala encoder.scala \
    --genc \
    -J-Xms10G -J-Xss20M "$@"
mv stainless.c genc/stainless.c
mv stainless.h genc/stainless.h

cd genc
gcc -O3 -Wall genc-qoibench.c stainless.c genc-bridge.c -o genc-qoibench