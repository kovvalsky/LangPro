#!/usr/bin/env python
# -*- coding: utf8 -*-
# usage: python3 python/evaluate.py train_aall_wnads_allInt.txt SICK_dataset/SICK_train.txt
#        python3 ~/Natural\ Tableau/LangPro/python/evaluate.py ~/Natural\ Tableau/LangPro/mine/amrfol/T_no_kqw_al_chk_int_100.ans temp/sick/SICK_train.txt
import argparse
import re
from collections import Counter
from collections import defaultdict
from os import path as op

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(description="Evaluate predictions against gold labels.")
    parser.add_argument(
    '--sys', required=True, nargs='+', metavar='FILES',
        help='File with problem ID, white space and label per line')
    parser.add_argument(
    '--gld', required=True, metavar='FILE',
        help="File with gold label. The format might vary")
    parser.add_argument(
    '--hybrid', action='store_true',
        help="Print result of hybrid or all")
    # meta parameters
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, type=int, metavar='N',
        help='verbosity level of reporting')
    args = parser.parse_args()
    return args

#################################
def detect_prediction_format(line):
    '''The predictiosn can be written in different formats.
       Detect the format automatically
    '''
    pat = {}
    # 211	Two dogs are playing by a tree	Two dogs are playing by a plant	4.6	ENTAILMENT
    pat['sick_semeval'] = '(\d+)\s+.+(NEUTRAL|CONTRADICTION|ENTAILMENT)$'
    # 67: ENTAILMENT
    pat['default'] = '(\d+)\s+(NEUTRAL|CONTRADICTION|ENTAILMENT)$'
    #  56: [unknown], unknown,    open, Ter,70
    pat['langpro'] = '\s*(\d+):\s*\[\w+\],?\s*(\w+),?\s*[a-zA-Z,0-9 ]+\s*$'
    #     630: [contradiction]   contradiction (bliksem)
    pat['amrfol'] = '\s*(\d+):\s*\[\w+\]\s*(\w+)\s*[()a-zA-Z,0-9 ]+\s*$'
    # check which pattern matches
    for k, v in pat.items():
        if re.match(v, line):
            return v
    return None

#################################
def canonical_label(label):
    '''Map entailment label to the canonical label
    '''
    mapping = {'unknown':'NEUTRAL', 'yes':'ENTAILMENT', 'no':'CONTRADICTION'}
    return mapping.get(label, label)

#################################
def read_id_labels(filepath):
    '''Read a list of (ID, label) pairs from the file.
       Rename labels with the canonical names
    '''
    id_labels = {}
    with open(filepath) as f:
        pattern = None # yet unknown
        reading_finished = False # true if all predictions were read
        for line in f:
            line = line.strip()
            if not pattern: pattern = detect_prediction_format(line)
            if pattern:
                m = re.match(pattern, line)
                if m:
                    if reading_finished: RuntimeError("Discontinuous prediction block")
                    id_labels[m.group(1)] = canonical_label(m.group(2))
                else:
                    reading_finished = True
    if not id_labels:
        raise RuntimeError("No predictions retrieved")
    return id_labels

#################################
def read_systems_id_labels(filepaths):
    '''Read a list of (ID, label) pairs from the files'''
    sys_id_label = dict()
    for sysfile in filepaths:
        sys_id_label[sysfile] = read_id_labels(sysfile)
    # all should have the same size of predictions
    if len(set(len(d) for d in sys_id_label.values())) != 1:
        raise RuntimeError('The number of predictions is varying: {}'.format(\
            [ s, v in sys_id_label.items() ]))
    return sys_id_label

# #################################
def aggregate_answers(sys_id_label):
    '''Combine the answers of the systems in one'''
    prob_ids = next(iter(sys_id_label.values())).keys()
    id_labels = defaultdict(list)
    for k, v in sys_id_label.items():
        for p, pred in v.items():
            id_labels[p].append(pred)
    # aggregate
    id_ans = dict()
    for p, l in id_labels.items():
        s = set(l)
        if len(s) == 1:
            id_ans[p] = s.pop()
        elif len(s) == 2:
            if 'NEUTRAL' in s:
                s.remove('NEUTRAL')
                id_ans[p] = s.pop()
            else:
                id_ans[p] = 'NEUTRAL'
        else:
            id_ans[p] = 'NEUTRAL'
    return id_ans, id_labels

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
    sys_id_label = read_systems_id_labels(args.sys)
    print(f"{len(sys_id_label)} systems' output read")
    # compare problem num to the gold labels
    first_sys_ans = next(iter(sys_id_label.values()))
    gld_ans = read_id_labels(args.gld)
    assert len(first_sys_ans) == len(gld_ans),\
        f"The sources contain different number of problems ({len(first_sys_ans)} vs {len(gld_ans)})"
    # draw matrix
    systems_id_pred = { 'Hybrid': aggregate_answers(sys_id_label)[0] } if args.hybrid else sys_id_label
    for name, sys_ans in systems_id_pred.items():
        print("{:*^50}".format(name))
        lab_pairs = [ (sys_ans[k], gld_ans[k]) for k in sys_ans ]
        counter = Counter(lab_pairs)
        draw_conf_matrix(counter)
        m = calc_measures(counter)
        for name in sorted(m.keys()):
            print(f"{name:<12}: {m[name]:4.2f}%")
