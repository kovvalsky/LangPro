#!/usr/bin/env python3
# -*- coding: utf8 -*-

''' Extract lexical annotations from CCG trees in prolog format
Usage:
    python3 python/lex_anno_from_ccg.py --ccg %{reccg_pl} --nli %{sen_pl} --tok %{spl} --json %{target}
'''

#################################
import argparse, sys
from utils import read_nli_sen_pl, read_ccg_pl, write_json
from collections import OrderedDict
from generic import first_diff


def parse_arguments():
    parser = argparse.ArgumentParser(description='Extract lexical annotations')

    # Arguments covering directories and files
    parser.add_argument(
    '--ccg', metavar="FILE_PATH", required=True,
        help="A file with ccg derivations in prolog format")
    parser.add_argument(
    '--tok', metavar="FILE_PATH",
        help="A file with a tokenized sentence per line")
    parser.add_argument(
    '--sys', metavar="STR", required=True,
        help="System name that produced the annotations")
    parser.add_argument(
    '--json', metavar="FILE_PATH", required=True,
        help="A json output file with annotations")
    parser.add_argument(
    '--nli', metavar="FILE_PATH",
        help="A file with NLI problems in a prolog format with sen_id predicates")

    return parser.parse_args()


# for the control purposes
def ccg_toks_vs_sen_toks(lex_anno, sen):
    anno_tok = ' '.join(t['t'] for t in lex_anno)
    sen_tok = sen.replace("\\'", "'")
    assert anno_tok == sen_tok, f"{anno_tok} =/= {sen_tok}"
    return anno_tok

def tokens_equal(t1, t2):
    s = set([t1, t2])
    if len(s) == 1: return True
    if s <= set(["not", "n't"]): return True


def sort_sen_anno_following_pid(ccg, nli_path):
    ''' Sort token level annotations from ccgs according to
        the sentence occurences in nli problems
    '''
    nli = read_nli_sen_pl(nli_path)
    nli = { int(k):v for k,v in nli.items() }
    # written annotations follow the order of sentences that follows the order of
    # nli problems. No sentence annotation is repeated
    scanned_sens = set()
    annos = []
    i = 0
    for _, prob in sorted(nli.items()):
        for ph in "ph":
            if prob[ph] in scanned_sens:
                pass
            else:
                i += 1
                scanned_sens.add(prob[ph])
                sid = prob[(ph,'sid')]
                # if the sentence has a parse add its annotations
                if sid in ccg:
                    anno_tok = ccg_toks_vs_sen_toks(ccg[sid], prob[ph])
                    #print(i, anno_tok)
                    annos.append((i, ccg[sid]))
    return OrderedDict(annos)

def anno_token_compatible_with_spl(annos, spl):
    # verify that the CCG tokenization follows the required tokenization
    with open(spl) as F:
        sen_tokens = [ line.split() for line in F ]
    for i, tokens in enumerate(sen_tokens, start=1):
        if i not in annos: continue
        toks = [ t['t'] for t in annos[i] ]
        if len(tokens) != len(toks):
            raise RuntimeError(f"{i}: mismatch between --tok and --ccg ({first_diff(tokens, toks)})")
            #print(f"{i}: mismatch between --tok and --ccg ({first_diff(tokens, toks)})")
        for t1, t2 in zip(tokens, toks):
            if not tokens_equal(t1, t2):
                raise RuntimeError(f"{i}: {t1} =/= {t2['t']}")
                #print(f"{i}: {t1} =/= {t2['t']}")

####################################
if __name__ == '__main__':
    args = parse_arguments()

    ccg = read_ccg_pl(args.ccg)

    if args.nli:
        annos = sort_sen_anno_following_pid(ccg, args.nli)
    else:
        annos = OrderedDict([ (k, v) for k, v in sorted(ccg.items()) ])

    if args.tok:
        anno_token_compatible_with_spl(annos, args.tok)

    meta = OrderedDict([('sys', args.sys), ('command', ' '.join(sys.argv))])
    write_json(args.json, annos, meta=meta)
