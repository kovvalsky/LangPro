#!/usr/bin/env python
# -*- coding: utf8 -*-
# usage: python3 python/evaluate.py train_aall_wnads_allInt.txt SICK_dataset/SICK_train.txt
import argparse
import re
from collections import Counter

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(description="Evaluate predictions against gold labels.")
    parser.add_argument(
    'sys', metavar='FILE', help='File with problem ID, white space and label per line')
    parser.add_argument(
    'gld', metavar='FILE', help="File with gold label. The format might vary")
    # meta parameters
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, type=int, metavar='N', help='verbosity level of reporting')
    args = parser.parse_args()
    return args

#################################
def read_id_labels(filepath, pattern="(\d+)\s+(NEUTRAL|CONTRADICTION|ENTAILMENT)"):
    '''Read a list of (ID, label) pairs from the file'''
    id_labels = dict()
    with open(filepath) as f:
        for line in f:
            m = re.search(pattern, line)
            if m: id_labels[m.group(1)] = m.group(2)
    return id_labels

#################################
def draw_conf_matrix(counter, labs=['ENTAILMENT', 'CONTRADICTION', 'NEUTRAL']):
    '''Draw a confusion matrix for labels from two sources'''
    print(f"{63*'-'}\n{'':15} {labs[0]:>15} {labs[1]:>15} {labs[2]:>15}\n{63*'-'}")
    for gld in labs:
        print(f"{gld:>15}", end=' ')
        for sys in labs:
            print(f"{counter[(sys, gld)]:>15}", end=' ')
        print()
    print(63*'-')

#################################
def calc_measures(counter, labs=['ENTAILMENT', 'CONTRADICTION', 'NEUTRAL']):
    '''Calculate various measures'''
    m = dict()
    diag = sum([ counter[(l,l)] for l in labs ])
    total = sum(counter.values())
    m['accuracy'] = 100.0*diag / total
    # precision and recall as C & E positives
    diagEC = sum([ counter[(l,l)] for l in labs[:2] ])
    sys_neut = sum([ counter[(labs[2],l)] for l in labs ])
    gld_neut = sum([ counter[(l,labs[2])] for l in labs ])
    m['precision'] = 100.0*diagEC / (total - sys_neut)
    m['recall'] = 100.0*diagEC / (total - gld_neut)
    return m

#################################
if __name__ == '__main__':
    args = parse_arguments()
    sys_ans = read_id_labels(args.sys)
    gld_ans = read_id_labels(args.gld, pattern="^(\d+)\s+.+(NEUTRAL|CONTRADICTION|ENTAILMENT)$")
    assert len(sys_ans) == len(gld_ans),\
        f"The sources contain different number of problems ({len(sys_ans)} vs {len(gld_ans)})"
    lab_pairs = [ (sys_ans[k], gld_ans[k]) for k in sys_ans ]
    counter = Counter(lab_pairs)
    draw_conf_matrix(counter)
    m = calc_measures(counter)
    for name in sorted(m.keys()):
        print(f"{name:<12}: {m[name]:4.2f}%")
