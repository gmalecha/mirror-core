#!/usr/bin/python
import os, sys
import re

EXCLUDE=[]

def keep(x):
    global EXCLUDE
    for p in EXCLUDE:
        if p.match(x):
            return False
    return True

def get_name(n):
    n = n.strip()
    if n.startswith('./'):
        n = n[2:]
    if n.endswith('.vo'):
        n = n[:-3]
    return n

def get_ident(n):
    n = get_name(n)
    return n.replace('/','_').replace('.','').replace('-','_')

def gather_deps(files):
    result = {}
    for f in files:
        name = f[:-4] # ends in ".v.d"

        l = open(f).readlines()
        assert len(l) == 1
        (_, d) = l[0].split(':')
        deps = [ get_name(x) for x in d.split(' ')
                 if x.strip().endswith('.vo') and keep(x.strip())]

        result[name] = deps

    return result

def print_dot(deps):
    print('digraph dependencies {')
    for k in deps.keys():
        print('\t%s [label="%s"] ;' % (get_ident(k), k))
        for d in deps[k]:
            print('\t%s -> %s ;' % (get_ident(k), get_ident(d)))
    print('}')

if __name__ == '__main__':
    args = sys.argv[1:]
    EXCLUDE = []
    try:
        ex = args.index('--exclude')
        EXCLUDE = EXCLUDE + [re.compile('^%s$' % args[ex+1])]
        args = args[:ex] + args[ex+2:]
    except ValueError:
        pass

    deps = gather_deps(sys.argv[1:])
    print_dot(deps)
