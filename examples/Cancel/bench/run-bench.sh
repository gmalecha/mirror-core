#!/bin/bash

for i in 3 5 10 20 50 75 100
do
    echo $i

    sed "s/NNN/$i/g" BenchLtac.v > BenchLtac$i.v
    sed "s/NNN/$i/g" BenchRtac.v > BenchRtac$i.v
    sed "s/NNN/$i/g" BenchRtacSimple.v > BenchRtacSimple$i.v

    for t in `seq 1 25`
    do
	coqc  -q  -I ../../../src -R ../../../coq-ext-lib/theories ExtLib -R ../../. McExamples -R ../../../theories MirrorCore BenchLtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > ltac.$i.$t.raw
	coqc  -q  -I ../../../src -R ../../../coq-ext-lib/theories ExtLib -R ../../. McExamples -R ../../../theories MirrorCore BenchRtac$i | sed -e 's/.*(\(.*\)u,.*/\1/' > rtac.$i.$t.raw
	coqc  -q  -I ../../../src -R ../../../coq-ext-lib/theories ExtLib -R ../../. McExamples -R ../../../theories MirrorCore BenchRtacSimple$i | sed -e 's/.*(\(.*\)u,.*/\1/' > rtac-simple.$i.$t.raw
    done

    rm Bench{L,R}tac$i.v
    rm BenchRtacSiple$i.v

    paste ltac.$i.*.raw > ltac.$i.raw
    paste rtac.$i.*.raw > rtac.$i.raw
    paste rtac-simple.$i.*.raw > rtac-simple.$i.raw
    rm {r,l}tac.$i.*.raw rtac-simple.$i.*.raw
done

cat ltac.{3,5,10,20,50,75,100}.raw > ltac.raw
cat rtac.{3,5,10,20,50,75,100}.raw > rtac.raw
cat rtac-simple.{3,5,10,20,50,75,100}.raw > rtac-simple.raw
