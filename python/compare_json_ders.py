#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Compare two derivations encoded as json
'''

#################################
import argparse
import json
import itertools as it
import re

def parse_arguments():
    parser = argparse.ArgumentParser(description='Compare two lists of MRPs')

    # Arguments covering directories and files
    parser.add_argument(
    'jsonfile1', metavar="FILE_PATH",
        help="The file containing a list of MRPs")
    parser.add_argument(
    'jsonfile2', metavar="FILE_PATH",
        help="The file containing a list of MRPs")
    parser.add_argument(
    '-ik', '--include-keys', dest='ik', nargs='+', metavar="LIST OF KEYS",
        #default=['nodes', 'edges', 'input', 'tops'],
        help="The list of keys to be included in comparison")
    parser.add_argument(
    '-ek', '--exclude-keys', dest='ek', nargs='+', metavar="LIST OF KEYS",
        #default=['nodes', 'edges', 'input', 'tops'],
        help="The list of keys to be excluded in comparison")
    parser.add_argument(
    '--ids', nargs='*', type=int, metavar="LIST OF IDS",
        help="The list of ids of the json that will be compared")
    parser.add_argument(
    '--spl', metavar="FILE PATH",
        help="The file that contains tokenized sentences per line")
    parser.add_argument(
    '-v', dest='v', action='count', default=0,
        help="Verbosity level")

    # pre-processing arguments
    args = parser.parse_args()
    return args

########################################
def read_json_file(filepath):
    jlist = []
    with open(filepath) as F:
        for l in F:
            j = json.loads(l)
            if j: jlist.append(j)
    return jlist

##########################################
def compare_two_json_lists(list1, list2, ids=[], ik=None, ek=None, v=0):
    diff_ids = dict()
    for i, (j1, j2) in enumerate(it.zip_longest(list1, list2), start=1):
        if ids and i not in ids: continue
        diff = compare_two_json([], j1, j2, ik=ik, ek=ek)
        if diff:
            diff_ids[i] = diff
        if v > 1: print("{}\t{}".format(i, diff if diff else 'same'))
    return diff_ids

##########################################
def compare_two_json(path, j1, j2, ik=None, ek=None):
    # different types
    if type(j1) != type(j2):
        return path, 'type'
    # dealing with lists
    if isinstance(j1, list):
        if len(j1) != len(j2):
            return path, 'length'
        # compare lists element-wise
        for i, (x, y) in enumerate(zip(j1, j2)):
            diff = compare_two_json(path + [i], x, y, ik=ik, ek=ek)
            if diff: return diff
    # dealing with dictionaries
    elif isinstance(j1, dict):
        diff_set = set(j1.keys()) ^ set(j2.keys())
        if [ k for k in diff_set if relevant_key(k, ik, ek) ]:
            return path, diff_set
        for k in j1:
            if not relevant_key(k, ik, ek): continue
            diff = compare_two_json(path + [k], j1[k], j2[k], ik=ik, ek=ek)
            if diff: return diff
    else:
        assert isinstance(j1, str), "{} is not string".format(j1)
        if j1 == j2: return False
        return path, '{} vs {}'.format(j1, j2)

#############################################
def relevant_key(k, ik, ek):
    '''Check if key is a permitted one
    '''
    if ik is not None and k not in ik:
        return False
    if ek is not None and k in ek:
        return False
    return True


##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()
    # read spl file if provided
    if args.spl:
        with open(args.spl) as F:
            sents = [ l.strip() for l in F if l.strip() ]
    # read files as a list of dictionaries
    jlist1 = read_json_file(args.jsonfile1)
    jlist2 = read_json_file(args.jsonfile2)
    assert len(jlist1) == len(jlist2) and (not args.spl or len(jlist2) == len(sents)),\
        "Length difference: {}, {}, {}".format(len(jlist1), len(jlist), len(sents))
    diff_ids = compare_two_json_lists(jlist1, jlist2, ids=args.ids, ik=args.ik, ek=args.ek, v=args.v)
    if args.v > 0:
        for k, v in sorted(diff_ids.items()):
            print("{0:>5}\t{2}{1}".format(k, v,\
                "{}\n\t\t".format(sents[k-1]) if args.spl else ''))
    print("{} differences".format(len(diff_ids)))
