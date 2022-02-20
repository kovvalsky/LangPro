#!/usr/bin/env python
# -*- coding: utf8 -*-

import argparse
import re
from evaluate import read_nli_sen_pl, read_systems_id_labels, read_id_labels
from collections import defaultdict, Counter
from os import path as op

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(description="Compare logs of CV")
    parser.add_argument(
    '--sys', required=True, nargs='+', metavar='FILES',
        help='System logs. Format might vary')
    parser.add_argument(
    '--gld', metavar='FILE',
        help="File with gold label. The format might vary")
    args = parser.parse_args()
    return args


#################################
def read_cv_log(file_log, eval_sep="Accuracy \(pure\)"):
    phase_id_labels = {}
    with open(file_log) as F:
        txt = F.read()
    # chop into cv parts
    for f, fold in enumerate(re.split("End of fold \d+", txt)[:-1], start=1):
        fold_chunks = re.split(eval_sep, fold)[:-1]
        for i, run in enumerate(fold_chunks, start=1):
            id_lab = read_id_labels(run)
            # t for training and e for evaluation
            m = 't' if i < len(fold_chunks) else 'e'
            for pid, l in id_lab.items():
                # fN-[et]N:NNNN
                phase_id_labels[f"f{f}:{m}{i}:{pid}"] = l
    return phase_id_labels


def compare_predictions(sys_phase_id_label, ordered_sys=None, gld_nli=None):
    sys_names = ordered_sys if ordered_sys else list(sys_phase_id_label.keys())
    phase_id = sorted(sys_phase_id_label[sys_names[0]].keys())
    sys_solved = defaultdict(set)
    for pid in phase_id:
        # fold number, train|eval, loopNum, prob_id
        f, m, n, i = re.match('f(\d+):([et])(\d+):(.+)', pid).groups()
        labels = [ sys_phase_id_label[s][pid] for s in sys_names ]
        if len(set(labels)) > 1:
            if gld_nli:
                # give a point to each sys for a correct prediction
                for s in sys_names:
                    if sys_phase_id_label[s][pid] == gld_nli[i]['l']:
                        sys_solved[s].add(f"{f}:{m}{n}:{i}")
                p = gld_nli[i]
                prob = f"\n{p['l']}\n{p['p']}\n{p['h']}"
            else:
                prob = ''
            print(f"{pid}\t{labels}\t{prob}")
    # print sys and its solved probs
    for s in sys_names:
        print(f"{s}: ({len(sys_solved[s])}):")
        print(f"\t{sorted([i for i in sys_solved[s] if ':t' in i])}")
        print(f"\t{sorted([i for i in sys_solved[s] if ':e' in i])}")


#################################
if __name__ == '__main__':
    args = parse_arguments()
    sys_phase_id_label = read_systems_id_labels(args.sys, read_fun=read_cv_log)
    gld_nli = read_nli_sen_pl(args.gld) if args.gld else None
    compare_predictions(sys_phase_id_label, ordered_sys=args.sys, gld_nli=gld_nli)
