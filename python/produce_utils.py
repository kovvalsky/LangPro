#!/usr/bin/env python3
# -*- coding: utf8 -*-

import re, os, sys
from os import path as op

ABBR2TOOL = {'D':'depccg', 'E':'easyccg', 'C':'cc2016.st', 'S':'spacy'}
ABBR2MODEL = {'D':'depccg.trihf.sep', 'E':'easyccg', 'C':'cc2016.st'}

def abbr2tool(a):
    return ABBR2TOOL[a]

def abbr2model(a):
    return ABBR2MODEL[a]

def flags2annos(a):
    annos = re.split('[\.,]', a)
    order = 'ccg l ppos ner'.split()
    k_sys = [ f"{k}-'{abbr2tool(sys)}'" for k, sys in zip(order, annos) ]
    return ', '.join(k_sys)

def flags2ccgfile(a):
    parser = re.split('[\.,]', a)[0]
    return ABBR2MODEL[parser]

def flag2par(flag):
    '''Interpret acronyms of parameters.
       cN - core number, rN - rule application number,
       pMN - patterns with M terms and N terms.
    '''
    # lookup table abbreviation to LangPro parameter
    mapping = {'al': 'aall',
               'ch': 'constchk',
               'w3': 'wn',
               'hk': 'hk',
               '-w': 'no_wn',
               'cN': 'ccg_norm',
               '-N': '',
               'lN': 'llf_norm',
               'N': 'ccg_norm, llf_norm',
               'ai': 'allInt',
               'common': 'aall, allInt, constchk, wn, llf_norm, ccg_norm',
               # induction parameters
               'ab': 'align-both',
               'an': 'align-no_align',
               'aa': 'align-align',
               'ch': 'constchk',
               'cKB': 'constKB',
               'cT': 'compTerms'
               # pNM
              }
    if flag in mapping:
        return mapping[flag]
    # cores or rule limit
    m = re.match('[rcpv](\d+)$', flag)
    if m:
        n = int(m.group(1))
        if flag[0] == 'r':
            return f"ral({n})"
        # used for injecting version for file,
        # it has no affect for proving
        elif flag[0] == 'v':
            return f"v{n}"
        elif flag[0] == 'c':
            if n == 1:
                return 'true'
            return f"parallel({n if n else '_'})"
        else: # induction parameter
            return f"patterns-({expand_patterns(str(n))})"
    raise ValueError(f'Unknown flag: {flag}')

def flags2pars(flags):
    return ', '.join([ flag2par(f) for f in re.split('[\.,]', flags) ])

def expand_patterns(pat):
    mappings = {'1': '_',
                '2': '_@_',
                '3': '(_@_)@_, _@(_@_)',
                '4': '_@(_@(_@_)), _@((_@_)@_), (_@_)@(_@_), ((_@_)@_)@_, (_@(_@_))@_'
                }
    patterns = ','.join([ mappings[p] for p in pat ])
    return f"[{patterns}]"

def get_part(p):
    d = {'T': 'train', 'D': 'trial', 'E': 'test' }
    if p in d:
        return d[p]
    else:
        return '_'.join([ d[c] for c in p ])
