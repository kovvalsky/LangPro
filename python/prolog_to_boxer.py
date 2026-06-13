#!/usr/bin/env python3
import sys
import re

cat_sym = r'\\/:\w\)\('

print(":- op(601, xfx, (/)).")
print(":- op(601, xfx, (\\)).")
print(":- discontiguous ccg/2, w/8.\n")

text = sys.stdin.read()

trees = re.findall(r'ccg\(.+?w\(.+?\)\.\n\n', text, re.S)

for tr in trees:
    # replace [features] by :features
    tr = re.sub(r'\[([a-zA-Z]+)\]', r':\1', tr)
    # o 'clock -> '\clock
    tr = re.sub(r", *''", r",'\\\\'", tr)
    # 'CAT'). -> lowercase(CAT)).
    tr = re.sub(r"'([" + cat_sym + r"]+)'([).,]+)\n",
                 lambda m: m.group(1).lower() + m.group(2) + "\n", tr)
    # lex('CAT' -> lx(lowercase(cat)
    tr = re.sub(r"lex\('([" + cat_sym + r"]+)'",
                 lambda m: "lx(" + m.group(1).lower(), tr)
    tr = tr.replace(':x', ':_')
    tr = re.sub(r"''s'", r"'\\\\'s'", tr)
    sys.stdout.write(tr)