#!/usr/bin/env python3
import sys
import re

cat_sym = r'\\/:\w\)\('

print(":- op(601, xfx, (/)).")
print(":- op(601, xfx, (\\)).")
print(":- discontiguous ccg/2, w/8.\n")

f = open(sys.argv[1], encoding="utf-8") if len(sys.argv) > 1 else sys.stdin
text = f.read()

trees = re.findall(r'ccg\(.+?w\(.+?\)\.\n\n', text, re.S)

for tr in trees:
    # replace [features] by :features
    tr = re.sub(r'\[([a-zA-Z]+)\]', r':\1', tr)

    # 'CAT'). -> lowercase(CAT)).
    pattern = rf"'([{cat_sym}]+)'([).,]+)\n"
    tr = re.sub( pattern, lambda m: f"{m.group(1).lower()}{m.group(2)}\n", tr)

    # lex('CAT' -> lx(lowercase(cat)
    pattern = rf"lex\('([{cat_sym}]+)'"
    tr = re.sub(pattern, lambda m: "lx(" + m.group(1).lower(), tr)

    # escape single quotes in tokens: 
    # [space]'o'clock',[space] -> [space]'o\\'clock'[space]
    tr = re.sub(r"(\s)'(.*?)',(?=\s)",
                lambda m: m.group(1) + "'" + m.group(2).replace("'", "\\'") + "',",
                tr
    )
    # pattern = "( ')'(', )"
    # tr = re.sub(r"([^\s,'])'([^\s,'])", r"\1\\'\2", tr)
    # certain contractions need to be escaped in Prolog
    # tr = re.sub(r"''s'", r"'\\'s'", tr)
    # tr = re.sub(r"'n't'", r"'n\\'t'", tr)

    # variable features are replaced with prolog anonymous variable '_'  
    tr = tr.replace(':x', ':_')

    # patching some weird and extremely rare cases
    tr = tr.replace(r"\', ", r"\\', ") # for trailing \ after words

    sys.stdout.write(tr)
