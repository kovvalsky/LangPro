#!/usr/bin/env python3
# -*- coding: utf8 -*-

import re, sys



def cat_str2pl(cat):
    cat = cat.lower().strip("'")
    cat = cat.replace('[X]', '')
    cat = re.sub('\[([^\[\]]+)\]', r':\1', cat)
    return cat

def cat_str2pl_match(m):
    return cat_str2pl(m.group())

preambule = '''
:- discontiguous w/8, ccg/2.
:- op(601, xfx, (/)).
:- op(601, xfx, (\)).
'''

sys.stdout.write(preambule + '\n')


for line in sys.stdin:
    # |N is confused in an escape char
    #line = line.replace("\N", r"\\N")

    if re.match('\s*w\(\d+,', line):
    # dealing with lexical pred w()
        m = re.match("(\s*w\(\d+,\s*\d+,\s*)'(.+)',\s*'(.+)',\s*'(.+)',\s*'(.+)',\s*'(.+)',\s*'(.+)'\)\.", line)
        prefix, tok, lem, pos, chk, ner, cat = m.groups()
        tok = re.sub(r"([^\\])'", r"\1\\'", tok)
        lem = re.sub(r"([^\\])'", r"\1\\'", lem)
        #tok = tok.replace("'", r"\'")
        #lem = lem.replace("'", r"\'")
        cat = cat_str2pl(cat)
        sys.stdout.write(f"{prefix}'{tok}', '{lem}', '{pos}', '{chk}', '{ner}', {cat}).\n")
    elif re.search(r"'[A-Za-z\\/\[\]\)\(]+'", line):
    # dealing with CCG tree if there is a category
        line = re.sub(r"'[A-Za-z\\/\[\]\(\)]+'", cat_str2pl_match, line)
        sys.stdout.write(re.sub("lex\(", "lx(", line))
    else:
        sys.stdout.write(re.sub("lex\(", "lx(", line))
