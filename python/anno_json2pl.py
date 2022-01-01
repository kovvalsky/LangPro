#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Convert token-level annotations from json to prolog format
'''

#################################
import argparse, sys, json, re

def parse_arguments():
    parser = argparse.ArgumentParser(description='Convert json annotations to prolog')

    # Arguments covering directories and files
    parser.add_argument(
    'json-ann', metavar="JSON FILE",
        help="File in json format encoding token level annotatiosn for sentences")
    parser.add_argument(
    '--shared-keys', metavar="OUTPUT FILE",
        help="Output file. If not specified the output is written to stdout")
    parser.add_argument(
    '--ids', nargs='*', metavar="LIST OF IDS",
        help="A list of sentence IDs, i.e. line numbers, to be processed (starts from 1)")

    # pre-processing arguments
    args = parser.parse_args()
    return args


##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()

    with open(args.json_ann) as F:
        d = json.load(F)
    # write all prolog clauses in a variable and write it in file at the end
    pl = ''
    d['meta']
