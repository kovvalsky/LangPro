#!/usr/bin/env python3
# -*- coding: utf8 -*-

import argparse
from depccg.parser import EnglishCCGParser
from pathlib import Path
import sys
import json

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(description="Parse with depccg")
    parser.add_argument(
    'model', metavar='MODEL',
        help='path to the model directory')
    parser.add_argument(
    'input', metavar='FILE PATH',
        help='path to the file containing tokenized input sentences')
    parser.add_argument(
    '--output', metavar='FILE PATH',
        help='path to the file where output will be written')
    parser.add_argument(
    '-v', '--verbose', dest='v', action='count',
        help='verbosity level of reporting')
    parser.add_argument(
    '--gpu', action='store_true',
        help='Whether to use gpu')
    parser.add_argument(
    '--one', action='store_true',
        help='One by one parsing of sentences')
    args = parser.parse_args()
    return args

#################################
def parse_sents(parser, sents):
    '''Parse a list of sentences with the parser
    '''
    results = parser.parse_doc(sents)
    ders = []
    for nbests in results:
        for tree, log_prob in nbests:
            ders.append(tree.json())
    return ders

#################################
if __name__ == '__main__':
    args = parse_arguments()
    # Available keyword arguments in initializing a CCG parser
    kwargs = dict(
        # A list of binary rules
        # By default: depccg.combinator.en_default_binary_rules
        binary_rules=None,
        # Penalize an application of a unary rule by adding this value (negative log probability)
        unary_penalty=0.1,
        # Prune supertags with low probabilities using this value
        beta=0.00001,
        # Set False if not prune
        use_beta=True,
        # Use category dictionary
        use_category_dict=True,
        # Use seen rules
        use_seen_rules=True,
        # This also used to prune supertags
        pruning_size=50,
        # Nbest outputs
        nbest=1,
        # Limit categories that can appear at the root of a CCG tree
        # By default: S[dcl], S[wq], S[q], S[qem], NP.
        possible_root_cats=None,
        # Give up parsing long sentences
        max_length=250,
        # Give up parsing if it runs too many steps
        max_steps=100000,
        # You can specify a GPU
        gpu= 1 if args.gpu else -1
    )

    # Initialize a parser from a model directory
    model = args.model
    parser = EnglishCCGParser.from_dir(
        model,
        load_tagger=True, # Load supertagging model
        **kwargs)

    # model = Path("../../models_depccg/tri_headfirst")
    # parser = EnglishCCGParser.from_files(
    #     unary_rules=model / 'unary_rules.txt',
    #     category_dict=model / 'cat_dict.txt',
    #     seen_rules=model / 'seen_rules.txt',
    #     tagger_model=model / 'tagger_model',
    #     **kwargs)

    # If you don't like to keep separate files,
    # wget http://cl.naist.jp/~masashi-y/resources/depccg/config.json
    # model = Path("/path/to/model/directory")
    # parser = EnglishCCGParser.from_json(
    #     model / 'config.json',
    #     tagger_model=model / 'tagger_model',
    #     **kwargs)

    # decide to write to file or stdout
    if args.output:
        OUT = open(args.output, 'w')
    else:
        OUT = sys.stdout

    # read all lines of the input files
    sents = []
    with open(args.input) as F:
        for line in F:
            if line.strip():
                sents.append(line.strip())
    print("{} sentences read".format(len(sents)))

    if args.one:
        for s in sents:
            OUT.write(json.dumps(parse_sents(parser, [s])[0]) + '\n')
    else:
        ders = parse_sents(parser, sents)
        for d in ders:
            OUT.write(json.dumps(d) + '\n')

    if args.output: OUT.close()
