#!/bin/bash

for i in 3 5 10 20 50 75 100
do
    echo $i

    sed "s/NNN/$i/g" BenchLtac.v > BenchLtac$i.v
    sed "s/NNN/$i/g" BenchRtac.v > BenchRtac$i.v

    for t in `seq 1 25`
    do
	coqc  -q  -I ../../../src -R ../../../coq-ext-lib/theories ExtLib -R ../../. McExamples -R ../../../theories MirrorCore BenchLtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > ltac.$i.$t.raw
	coqc  -q  -I ../../../src -R ../../../coq-ext-lib/theories ExtLib -R ../../. McExamples -R ../../../theories MirrorCore BenchRtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > rtac.$i.$t.raw
    done

    rm Bench{L,R}tac$i.v

    paste ltac.$i.*.raw > ltac.$i.raw
    paste rtac.$i.*.raw > rtac.$i.raw
    rm {r,l}tac.$i.*.raw
done

cat ltac.{3,5,10,20,50,75,100}.raw > ltac.tbl
cat rtac.{3,5,10,20,50,75,100}.raw > rtac.tbl
