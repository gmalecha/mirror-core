#!/usr/bin/python
##
## Program to determine unnecessary Requires in Coq modules.
##
## Usage
##   opt-import.py [extra-arguments-to-coqc] <module_name>.v
##
## module_name is the file name out the trailing .v
##
## Example
##
## To find extra requires in foo.v which is usually compiled by:
##
##   coqc -R . Foo foo
##
## run the following:
##
##   opt-import.py -R . Foo foo.v
##
import sys
import re
import subprocess
import tempfile
import os
import os.path

REQUIRE_IMPORT = re.compile(r'Require\s+(Import|Export)?\s+(.+)\.')

def get_imports(lines):
    return [n
            for (x,n) in zip(lines, range(0, len(lines)))
            for mtch in [REQUIRE_IMPORT.match(x)]
            if not mtch is None]

def try_compile(options):
    def run(lines):
        f = tempfile.NamedTemporaryFile('w', suffix='.v', delete=False)
        for x in lines:
            f.write(x)
        f.close()

        result = subprocess.Popen(['coqc'] + options + [f.name[:-2]],
                                  stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE)
        result.wait()
        os.unlink(f.name)
        try:
            os.unlink(f.name[:-1]+'glob')
        except:
            pass

        if os.path.exists(f.name + 'o'):
            os.unlink(f.name + 'o')
            return True
        else:
            return False
    return run

def optimize(f, try_compile):
    lines = open(f, 'r').readlines()
    options = get_imports(lines)
    remove = set()

    # Check from the end
    options.reverse()

    for i in options:
        sys.stdout.write(' ')
    sys.stdout.write('|\r')
    sys.stdout.flush()

    for i in options:
        # try removing line i
        if try_compile([x for (x,n) in zip(lines, range(len(lines)))
                        if not (n == i or n in remove)]):
            remove.add(i)
            sys.stdout.write('-')
            sys.stdout.flush()
        else:
            sys.stdout.write('+')
            sys.stdout.flush()

    sys.stdout.write('|')

    return [(x, lines[x]) for x in remove]


if __name__ == '__main__':
    fn = sys.argv[-1]
    args = sys.argv[1:-1]

    print ("Optimizing '%s'..." % fn)

    remove = optimize(fn, try_compile(args))
    remove.sort()

    if len(remove) == 0:
        print (" ok")
    else:
        print (" %d extra imports" % len(remove))
        for (n,x) in remove:
            print ("%2d: %s" % (n,x.strip()))
