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
    parser.add_argument(
    '-fp', '--first-primary', action='store_true',
        help="First system is primary and its Ent/Cont has priority")
    parser.add_argument(
    '-onc', '--only-Nth-correct', type=int,
        help="Show samples for which only the Nth (starting from 1) system's prediction is correct")
    parser.add_argument(
    '--write-hybrid', metavar='FILE',
        help="Write hybrid predictions in a file for later use")
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
    # 56: [unknown], unknown,    open, Ter,70
    pat['langpro'] = '\s*(\d+):\s*\[\w+\],?\s*(\w+),?\s*'
    # 630: [contradiction]   contradiction (bliksem)
    pat['amrfol'] = '\s*(\d+):\s*\[\w+\]\s*(\w+)\s*[()a-zA-Z,0-9 ]+\s*$'
    # sen_id(177, 281, 'p', 'TEST', 'unknown', 'Een jongen staat in het water').
    pat['sen.pl'] = "sen_id\(\d+,\s*(\d+),.+'(yes|no|unknown)',"
    # 17	1	1 # neural network baselines
    # where 0 is *contradiction*, 1 is *neutral* and 2 is *entailment*
    pat['nn_baselines'] = "(\d+)\t(\d)\t"
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
    n2lab = {'1':'NEUTRAL', '2':'ENTAILMENT', '0':'CONTRADICTION'}
    if label in mapping:
        return mapping[label]
    if label in n2lab:
        return n2lab[label]
    return label

#################################
def read_id_labels(filepath):
    '''Read a list of (ID, label) pairs from the file.
       Rename labels with the canonical names
    '''
    id_labels = {}
    with open(filepath) as f:
        pattern = None # yet unknown
        for line in f:
            line = line.strip()
            if not pattern: pattern = detect_prediction_format(line)
            if pattern:
                m = re.match(pattern, line)
                if m:
                    pid, pred = m.group(1), canonical_label(m.group(2))
                    if pid in id_labels:
                        assert pred == id_labels[pid], f"two diff predictions for {pid}"
                    else:
                        id_labels[pid] = pred
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
def aggregate_answers(sys_id_label, primary=None, out=None):
    '''Combine the answers of the systems in one'''
    prob_ids = next(iter(sys_id_label.values())).keys()
    id_labels = defaultdict(list)
    for k, v in sys_id_label.items():
        for p, pred in v.items():
            id_labels[p].append(pred)
    # aggregate
    id_ans = dict()
    for p, l in id_labels.items():
        # if there is a prmary system, then adopt its ent/cont answers
        if primary and \
            sys_id_label[primary][p] in ('ENTAILMENT','CONTRADICTION'):
            id_ans[p] = sys_id_label[primary][p]
            continue
        # there is no promaty system or primary says NEUTRAL
        s = set(l)
        if len(s) == 1:
            id_ans[p] = s.pop()
        elif len(s) == 2:
            if 'NEUTRAL' in s:
                s.remove('NEUTRAL')
                id_ans[p] = s.pop()
            else:
                id_ans[p] = 'NEUTRAL'
                print(f"Disagreement: {l}")
        else:
            id_ans[p] = 'NEUTRAL'
    # write aggregated answers in a file if requested
    if out:
        with open(out, 'w') as F:
            for i, ans in id_ans.items():
                F.write(f"{i}\t{ans}\n")
    return id_ans, id_labels

#################################
def contrast_predictions(corr_sys, sys_id_label, gld_ans):
    '''Select those samples for which only corr_sys is correct'''
    selected = []
    others = [ s for s in sys_id_label if s != corr_sys ]
    for i, l in sys_id_label[corr_sys].items():
        if gld_ans[i] != l: continue
        others_l = [ sys_id_label[s][i] for s in others ]
        if l not in others_l: selected.append((i, l, others_l))
    selected = sorted(selected, key=lambda x: int(x[0]))
    return selected


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
def calc_measures(c, labs=['ENTAILMENT', 'CONTRADICTION', 'NEUTRAL']):
    '''Calculate various measures'''
    m = dict()
    diag = sum([ c[(l,l)] for l in labs ])
    total = sum(c.values())
    m['Accuracy'] = 100.0*diag / total
    # precision and recall as C & E positives
    diagEC = sum([ c[(l,l)] for l in labs[:2] ])
    sys_neut = sum([ c[(labs[2],l)] for l in labs ])
    gld_neut = sum([ c[(l,labs[2])] for l in labs ])
    gld_enta = sum([ c[(l,labs[0])] for l in labs ])
    gld_cont = sum([ c[(l,labs[1])] for l in labs ])
    m['Precision'] = 100.0*diagEC / (total - sys_neut)
    m['Recall'] = 100.0*diagEC / (total - gld_neut)
    m['acc-Enta'] = 100.0*c[(labs[0],labs[0])] / gld_enta
    m['acc-Cont'] = 100.0*c[(labs[1],labs[1])] / gld_cont
    m['acc-Neut'] = 100.0*c[(labs[2],labs[2])] / gld_neut
    return m

#################################
if __name__ == '__main__':
    args = parse_arguments()
    sys_id_label = read_systems_id_labels(args.sys)
    # select the primary run
    if args.first_primary:
        p = args.sys[0]
    elif args.only_Nth_correct:
        p = p = args.sys[args.only_Nth_correct - 1]
    else:
        p = None
    print(f"{len(sys_id_label)} systems' output read")
    # compare problem num to the gold labels
    first_sys_ans = next(iter(sys_id_label.values()))
    gld_ans = read_id_labels(args.gld)
    assert len(first_sys_ans) <= len(gld_ans),\
        f"There are more predictions than referecne labels ({len(first_sys_ans)} vs {len(gld_ans)})"
    # mode selction
    if args.only_Nth_correct:
    # print those samples for which only the first system is correct
        selected = contrast_predictions(p, sys_id_label, gld_ans)
        for i, g, labs in selected:
            print(f"{i:>5}: {g[0]} {[ l[0] for l in labs ]}")
        print(Counter([ g for (_, g, _) in selected ]))
    else:
        #draw matrix
        systems_id_pred = { 'Hybrid': \
            aggregate_answers(sys_id_label, primary=p, out=args.write_hybrid)[0] }\
            if args.hybrid else sys_id_label
        for name, sys_ans in systems_id_pred.items():
            print("{:*^50}".format(name))
            lab_pairs = [ (sys_ans[k], gld_ans[k]) for k in sys_ans if k in gld_ans ]
            counter = Counter(lab_pairs)
            draw_conf_matrix(counter)
            m = calc_measures(counter)
            for name in sorted(m.keys()):
                print(f"{name:<12}: {m[name]:4.2f}%")
            print(f"All samples : {len(lab_pairs)}")
