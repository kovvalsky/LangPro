#!/usr/bin/env python
# -*- coding: utf8 -*-

import argparse
import re
from collections import defaultdict

#################################
def parse_arguments():
    parser = argparse.ArgumentParser(description="Read tableau branches")
    parser.add_argument(
    '--br', required=True, metavar='FILE',
        help='File containing branches')
    parser.add_argument(
    '--sick', metavar='DIR',
        help="SICK data directory")
    # meta parameters
    parser.add_argument(
    '-v', action='count', default=0,
        help="Verbosity level")
    args = parser.parse_args()
    return args

#################################
class Dict2Obj:
    '''Convert dictionary into an object'''
    def __init__(self, **entries):
        self.__dict__.update(entries)
    def __repr__(self):
        return self.__dict__.__repr__()

#################################
# printing functions
#################################
def print_branch(b):
    print(f"  {'':*^10} {b.i.i}{b.i.p} align({b.i.a}) {b.i.t} label:{b.i.l} {'':*^10}")
    print(f"\t{b.t}")
    print('\t', ', '.join([ f"{s}:{t}" for (s, t) in b.s ]), sep='')
    print('\t', '\n\t'.join([ f"{r.n}:{r.a}-->{r.c}" for r in b.r ]), sep='')
    print('\t', '\n\t'.join([ f"{n.i:>3} {n.t}  {n.m} : {n.h.t} : {n.a}" for n in b.n ]), sep='')

def print_problem(p):
    print(f"{'':=^80}")
    print_branch(p['p'][True])
    print_branch(p['p'][False])
    print_branch(p['h'][True])
    print_branch(p['h'][False])

#################################
# Auxiliary functions for reading
#################################
def read_term(term, sig, align=False):
    constant = ('@' not in term and '(' not in term and not align)
    return Dict2Obj(**{'c': constant, 't': term})

def read_rule_app(rapp):
    m = re.match('h\((\w+),.+?\[([\d,]+).+?\[([\d,]+)', rapp.strip())
    name, ant, con = m.groups()
    ant = [ int(n) for n in ant.split(',') ]
    con = [ int(n) for n in con.split(',') ]
    return Dict2Obj(**{'n': name, 'a': ant, 'c':con})

def read_node(node, sig=[]):
    i, tf, mods, head, args = re.split('\s*:\s*', node.strip())
    tf = True if tf == 'true' else False
    mods = [ m for m in mods.strip('[]').split(',') if m ]
    args = [ a for a in args.strip('[]').split(',') if a ]
    head = read_term(head, sig)
    return Dict2Obj(**{'i': int(i), 't':tf, 'm':mods, 'h':head, 'a':args})

def read_info(info):
    label, i, pos, align, tf = info.strip().split(',')
    # map short inferecne labels to standard NLI labels
    label_map = {'no':'contradiction', 'yes':'entailment', 'unknown':'neural'}
    label = label_map.get(label, label)
    tf = True if tf == 'true' else False
    align = True if align == 'align' else False
    return Dict2Obj(**{'i': int(i), 'p':pos, 'a':align, 't':tf, 'l':label})

#################################
# Other auxiliary functions
#################################

def remove_ids_from_nodes(nodes, ids):
    return [ n for n in nodes if n.i not in ids ]

#################################
def read_branch_file(filename, align=False, refine=False):
    with open(filename) as F:
        txt = F.read()
    # problem_id -> premise/hypothesis -> true/false -> branch
    id_ph_tf = defaultdict(lambda: defaultdict(dict))
    for b in re.split('branches:\s*', txt):
        if not b.strip(): continue
        m = re.match('\[(\S+)\]\nsentence:\s*(.+?)\n\s*\[\s*\n\s*\[(\S*)\](.+?)(\d+:.+)', b, re.DOTALL)
        info, text, sig, rapps, nodes = m.groups()
        info = read_info(info)
        # skip the rest if doesn't satisfy specified alignment
        if info.a != align: continue
        sig = [ tuple(c_t.split(',')) for c_t in re.findall('\w+,\w+', sig) ]
        rapps = [ read_rule_app(h) for h in re.findall('h\(.+\)\n', rapps) ]
        nodes = [ read_node(n, sig) for n in re.findall('\d+:.+\n', nodes) ]
        br = Dict2Obj(**{'n': nodes, 'r': rapps, 's': sig, 'i':info, 'l':len(nodes), 't':text})
        if refine:
            br = refine_node_list(br)
        id_ph_tf[info.i][info.p][info.t] = br
    return id_ph_tf

def refine_node_list(branch):
    '''Some nodes on the branch are redundant. While removing such nodes
       applied rules are taken in into account
    '''
    rule_del_ant = { 'push_arg':True,
                     'pull_arg':False,
                     'tr_a':True,
                     'mods_vp':False,
                     'push_mode':True,
                     'aux_verb':True,
                     'tr_conj_and':True,
                     'int_mod_tr':True
                   }
    for r in branch.r:
        if r.n in rule_del_ant:
            if rule_del_ant[r.n]:
                branch.n = remove_ids_from_nodes(branch.n, r.a)
            else:
                branch.n = remove_ids_from_nodes(branch.n, r.c)
    return branch


#################################
if __name__ == '__main__':
    args = parse_arguments()
    id_ph_tf = read_branch_file(args.br)
    ref_id_ph_tf = read_branch_file(args.br, refine=True)
    print(f"{len(id_ph_tf)} problems are read")
    for id, prob in ref_id_ph_tf.items():
        print(print_problem(prob))
    #print_problem(id_ph_tf[4])
    #print_problem(ref_id_ph_tf[4])
