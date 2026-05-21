#!/usr/bin/env python
# -*- coding: utf8 -*-
"""
Compare two evaluation logs from LangPro, and report the differences in predictions.

Usage example:
    python3 python/compare_logs.py --log1 sys1.log --log2 sys2.log
"""

import argparse
import re, sys
from collections import Counter, defaultdict
from os import path as op

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
    '--log1', required=True, metavar='FILE',
        help='The first log file')
    parser.add_argument(
    '--log2', required=True, metavar='FILE',
        help="The second log file")
    parser.add_argument(
    '--hybrid', action='store_true',
        help="NOT IMPLEMENTED")
    # meta parameters
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, type=int, metavar='N',
        help='verbosity level of reporting')
    args = parser.parse_args()
    return args

#################################
def read_log(filepath):
    '''Read per problem ID, a gold label, prediction, and optional problem text
    '''
    regex = r'\s*(\d+):\s*\[(\w+)\],?\s*(\w+),?\s*([^\n]+)'
    id_gpdp = {} # gold, prediction, problem
    with open(filepath) as F:
        prob = []
        for line in F:
            if line.strip() == '': continue
            if m := re.match(regex, line):
                if prob: # has read a problem for previous problem
                    id_gpdp[pid][3] = prob
                    prob = []
                pid, gold, pred, details = m.groups()
                id_gpdp[pid] = [gold, pred, details, None]
            elif re.match(r'\s{3,}', line) and '[' not in line and ']' not in line:
                prob.append(line.strip())
            else:
                pass
    return id_gpdp

#################################
def compare_logs(log1, log2, print_out=False):
    '''Compare logs'''
    id_diff = []
    lab_score = defaultdict(lambda: [0, 0])
    if len(log1) != len(log2):
        print(f"The mismatch between logs: {len(log1)} vs {len(log2)}")
        only_in_log1 = [ pid for pid in log1 if pid not in log2 ]
        only_in_log2 = [ pid for pid in log2 if pid not in log1 ]
        if only_in_log1: print(f"Only in log1: {only_in_log1}")
        if only_in_log2: print(f"Only in log2: {only_in_log2}")
    for pid, (g1, pred1, d1, prob1) in sorted(log1.items(), key=lambda x: int(x[0])):
        if pid not in log2:
            print(f"{pid} is not in log2; ignoring")
            continue
        g2, pred2, d2, prob2 = log2[pid]
        assert g1 == g2, f"gold labels for {pid} differ: {g1} vs {g2}"
        # solved problem has None for <p,h>
        prob = prob1 if prob1 is not None else prob2
        if pred1 != pred2:
            if pred1 == g1: lab_score[g1][0] += 1
            if pred2 == g1: lab_score[g1][1] += 1
            id_diff.append((pid, g1, (pred1, d1), (pred2, d2), prob))
    corr1 = sum([ v[0] for v in lab_score.values() ])
    corr2 = sum([ v[1] for v in lab_score.values() ])
    if print_out:
        print(f"How many times only one is correct: First ({corr1}) vs Second ({corr2})")
        print("Correct per label: First (yes:{}; no:{}; unknown:{}) vs Second (yes:{}; no:{}; unknown:{})".format(\
            lab_score["yes"][0], lab_score["no"][0], lab_score["unknown"][0],\
            lab_score["yes"][1], lab_score["no"][1], lab_score["unknown"][1]))

        for pid, g, pred_d1, pred_d2, prob in id_diff:
            prob = '\n\t\t'.join(prob) if prob is not None else 'No problem'
            print(f"{pid}\t[{g}]\n\t\t{prob}")
            print(f"\tsys1:\t{pred_d1[0]}\t{pred_d1[1]}")
            print(f"\tsys2:\t{pred_d2[0]}\t{pred_d2[1]}")
    return corr1, corr2, id_diff

#################################
if __name__ == '__main__':
    args = parse_arguments()
    log1 = read_log(args.log1)
    log2 = read_log(args.log2)
    compare_logs(log1, log2, print_out=True)