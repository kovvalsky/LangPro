#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''
Convert decppcg derivations in json format into prolog ccg derivations
'''

import os, sys, argparse, re, json
from collections import Counter, defaultdict


#################################
def parse_arguments():
    '''Read arguments from a command line'''
    parser = argparse.ArgumentParser(description='Convert depccg derivation into prolog')
    parser.add_argument(
    'der', metavar='PATH',
        help='Json file containing depccg derivations')
    parser.add_argument(
    'output', metavar='PATH',
        help='File for writing prolog derivations')
    parser.add_argument(
    '--anno', metavar='PATH',
        help='Annotation file including token|pos|ner tags')
    parser.add_argument(
    '--lemma', metavar='PATH',
        help='File with lemmatized tokens')
    parser.add_argument(
    '--tok-off', metavar='PATH',
        help='File with token offsets')
    parser.add_argument(
    '--ids', metavar='ID LIST', nargs='+', type=int,
        help='Process only the specific entries')
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, action='count',
        help='Verbosity level of reporting')
    args = parser.parse_args()
    return args


def check_der_anno(der, anno, delim, v=0):
    '''Check that derivation and annotations are for the same token list.
       delim provides a hint how to unfoild annotation
    '''
    toks = re.findall('"word": "([^"]+)"', json.dumps(der))
    if len(toks) != len(anno):
        raise ValueError("{} =\= {}".format(len(toks), len(anno)))
    for t, a in zip(toks, anno):
        w = a["t"] if delim=='dict' else a.split(delim, 1)[0]
        if w != t:
            raise ValueError("{} =\= {} in {}".format(w, t, anno))


#################################
def derdict_anno2pl(der, anno, lemma, offset, v=0):
    '''Combine derivation and annotations and convert into prolog ccg format.
       For more flexibility, anno & lemma are optional
    '''
    if anno: check_der_anno(der, anno, '|', v=v)
    if offset: check_der_anno(der, offset, 'dict', v=v)
    _, pl, a_rest, l_rest, o_rest = der_anno_to_pl(der, anno, lemma, offset, lvl=1)
    if a_rest or l_rest or o_rest:
        raise ValueError("{} is not empaty".format(a_rest + l_rest + o_rest))
    return pl

#################################
def cat2pl(cat, v=0):
    '''Convert category into prolog syntax
    '''
    cat = cat.lower().replace('\\\\', '\\')
    cat = re.sub('\[([^]]+)\]', r':\1', cat)
    return cat

#################################
def der_anno_to_pl(der, anno, lemma, offset, lvl=0):
    '''Recursively reads a tree encoded as dict and aligns it with annotations
    '''
    # format the category for prolog
    cat = cat2pl(der['cat'])
    cat_pl = cat # category that is printed in ccg prolog,
                 # it can be augmented with child category for lex and conj combinators
    if 'children' in der:
        assert 3 > len(der['children']) > 0, "Inconsistent number of children {}".format(der)
        children_pl = ''
        children_cats = []
        for ch in der['children']:
            ch_cat, pl, anno, lemma, offset = der_anno_to_pl(ch, anno, lemma, offset, lvl=lvl+1)
            children_pl += ',\n' + pl
            children_cats.append(ch_cat)
        if der['type'] in ('lex', 'conj'):
            der['type'] = 'lx' if der['type'] == 'lex' else der['type']
            children_cats.reverse()
            main_child_cat = next( c for c in children_cats if c != 'conj' )
            # There is a bug in depccg for cases like conj(np\np, np\np)
            # which is produced by depccg in json format
            # if cat_pl == main_child_cat and der['type'] == 'conj':
            #     cat_pl = r"({})\({})".format(cat_pl, cat_pl)
            cat_pl += ', ' + main_child_cat
        pl = "{}{}({}{})".format(lvl*' ', der['type'], cat_pl, children_pl)
        return cat, pl, anno, lemma, offset
    else:
        if anno:
            token, pos, ner = anno[0].split('|')
            assert der['word'] == token, "{} =\= {}".format(der['word'], token)
        ind = lvl * ' '
        tok = der['word'].replace("'", r"\'")
        lem = lemma[0].replace("'", r"\'").lower() if lemma else ''
        c_lem = f", '{lem}'" if lem else ''
        pos = pos.replace("'", r"\'") if anno else ''
        c_pos = f", '{pos}'" if pos else ''
        ner = ner.replace("'", r"\'") if anno else ''
        c_ner = f", '{ner}'" if pos else ''
        off = re.match('(\d+)[^\d](\d+)', offset[0]['o']).groups() if offset else ''
        c_off = f", {off[0]}-{off[1]}" if off else ''

        pl = f"{ind}t({cat}, '{tok}'{c_lem}{c_pos}{c_ner}{c_off})"
        return cat, pl, anno[1:] if anno else None, lemma[1:] if lemma else None, offset[1:] if offset else None


def read_anno_file(fn, fmt, length=None):
    if fn:
        with open(fn) as F:
            if fmt=='space-sep-tok':
                anno_list = [ a.strip().split() for a in F ]
            elif fmt=='json':
                d = json.load(F)
                d.pop('meta')
                anno_list = [ d[sid] for sid in sorted(d, key=int) ]
        if length:
                assert length == len(anno_list), f"{length} =\= {len(anno_list)}"
        return anno_list






################################################################################
###################################### MAIN ####################################
################################################################################
if __name__ == '__main__':
    args = parse_arguments()
    # read derivations and annotations from files
    with open(args.der) as F:
        der_list = [ json.loads(j) for j in F ]
    l = len(der_list)
    # read if annotations, e.g., pos and ner, are provided
    anno_list = read_anno_file(args.anno, 'space-sep-tok', length=l)
    # read if lemmatization is provided
    lemma_list = read_anno_file(args.lemma, 'space-sep-tok', length=l)
    # read if token offsets are provided
    tokoff_list = read_anno_file(args.tok_off, 'json', length=l)

    # combine into prolog derivation
    ccg_pl = ("% this file was generated by the following command(s):"
              "\n% {}\n\n"
              ":- op(601, xfx, (/)).\n"
              ":- op(601, xfx, (\)).\n"
              ":- multifile ccg/2, id/2.\n"
              ":- discontiguous ccg/2, id/2.\n\n").format(' '.join(sys.argv))
    for i, d in enumerate(der_list, start=1):
        if args.ids and i not in args.ids: continue
        a = anno_list[i-1] if anno_list else None
        l = lemma_list[i-1] if lemma_list else None
        o = tokoff_list[i-1] if tokoff_list else None
        pl = derdict_anno2pl(d, a, l, o, v=args.v)
        ccg_pl += "ccg({},\n{}).\n\n".format(i, pl)
    with open(args.output, 'w') as O:
        O.write(ccg_pl)
