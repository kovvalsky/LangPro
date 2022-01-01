#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Merge compatible annotations or apply new annotations to the existing one
'''

#################################
import argparse, sys, json, re
from collections import OrderedDict
from utils import write_json


def parse_arguments():
    parser = argparse.ArgumentParser(description='Combine/apply annotations')

    # Arguments covering directories and files
    parser.add_argument(
    '--tok-sen', metavar="FILE_PATH",
        help="A file with a tokenized sentence per line")
    parser.add_argument(
    '--ann-sen', metavar="FILE_PATH",
        help="Annotation that needs to be applied")
    parser.add_argument(
    '--ann-key', metavar="STR", choices=['l', 'ppos', 'upos', 'wn'],
        help="JSON key for the annotation")
    parser.add_argument(
    '--sys', metavar="STR",
        help="Name of the system that produced the annotations")
    parser.add_argument(
    '--json', metavar="FILE_PATH", required=True,
        help="A json output file with annotations")
    parser.add_argument(
    '--ids', nargs='*', type=int, metavar="LIST OF IDS",
        help="A list of sentence IDs, i.e. line numbers, to be processed (starts from 1)")
    parser.add_argument(
    '-v', dest='v', action='count', default=0,
        help="Verbosity level")

    # pre-processing arguments
    args = parser.parse_args()
    return args


##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()
    meta = OrderedDict([('sys', args.sys)])
    if args.tok_sen and args.ann_sen and args.ann_key:
        sen_anno = OrderedDict()
        with open(args.tok_sen) as TOK, open(args.ann_sen) as ANN:
            tok_sen = [ l.strip().split() for l in TOK ]
            ann_sen = [ l.strip().split() for l in ANN ]
            assert len(tok_sen) == len(ann_sen), "Mismatch in line numbers"
        for i, (toks, anns) in enumerate(zip(tok_sen, ann_sen), start=1):
            if args.ids and i not in args.ids: continue
            assert len(toks) == len(anns), f"Mismatch in token numbers for line {i}"
            tok_ann = [ OrderedDict([('t',t), (args.ann_key,a)]) for t, a in zip(toks, anns) ]
            sen_anno[i] = tok_ann

    # write annotations in a json format
    meta['command'] = ' '.join(sys.argv)
    write_json(args.json, sen_anno, meta=meta)
