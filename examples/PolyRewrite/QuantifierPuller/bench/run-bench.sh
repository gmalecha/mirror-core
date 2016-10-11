#!/bin/bash

FLAGS="-noglob -I ../../../../src -Q ../../../coq-ext-lib/theories ExtLib -Q ../../.. McExamples -Q ../../../../theories MirrorCore"

for i in 3 4 5 6 7 8 9 10 11 12 13 14
do
    echo $i

    sed "s/NNN/$i/g" BenchLtac.v > BenchLtac$i.v
    sed "s/NNN/$i/g" BenchRtac.v > BenchRtac$i.v

    # was originally 25
    for t in `seq 1 5`
    do
	coqc  -q  $FLAGS BenchLtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > ltac.$i.$t.raw
	coqc  -q  $FLAGS BenchRtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > rtac.$i.$t.raw
    done

    rm Bench{L,R}tac$i.v

    paste ltac.$i.*.raw > ltac.$i.raw
    paste rtac.$i.*.raw > rtac.$i.raw
    rm {r,l}tac.$i.*.raw
done

cat ltac.{3,4,5,6,7,8,9,10,11,12,13,14}.raw > ltac.raw
cat rtac.{3,4,5,6,7,8,9,10,11,12,13,14}.raw > rtac.raw
