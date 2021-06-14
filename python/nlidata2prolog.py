#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''
Convert SICK into the sen.pl and sentence-per-line formats
'''

import os
import sys
import codecs
import argparse
import re
from collections import Counter, defaultdict
import xml.etree.ElementTree as ET
import json
import nltk
from nltk.tokenize import word_tokenize
import spacy


#################################
def parse_arguments():
    '''Read arguments from a command line'''
    parser = argparse.ArgumentParser(description='Extract sentences per line for parsing')
    parser.add_argument(
    'file', metavar='PATH',
        help='File containing NLI data')
    parser.add_argument(
    'output', metavar='PATH prefix',
        help='File for writing output')
    parser.add_argument(
    '--fmt', required=True, choices=['spl', 'sen.pl'],
        help='Format of the output file')
    parser.add_argument(
    '--corpus', required=True, choices=['sick_semeval', 'snlijson'],
        help='Corpus to be converted')
    parser.add_argument(
    '--tokenize', default='nltk', choices=['raw', 'nltk', 'spacy', 'native'],
        help='How to tokenize the text. "native" works for snli.jsonl files \
             which comes with parsed trees.')
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, action='count',
        help='verbosity level of reporting')
    args = parser.parse_args()
    return args

#################################
def report(message, priority, verbosity):
    if priority <= verbosity:
        print(message)

def write_nli_dict(nli_dict, out, fmt, tok='raw', v=0):
    if fmt == 'spl':
        cnt = nli_spl(nli_dict, out, tok, v=v)
        report('{} sentences written for parsing'.format(cnt), 1, v)
    elif fmt == 'sen.pl':
        cnt = nli_prolog(nli_dict, out, cen_labs=False)
        report('{} NLI sentences written'.format(cnt), 1, v)
    else:
        raise RuntimeError("Unknown format /{}/".format(fmt))


def sick_semeval2nli(file_stream, out, fmt, tok='raw', v=0):
    '''Convert stream into prolog or spl data and write it into file
    '''
    nli_dict = defaultdict(dict)
    i = 1
    for p in file_stream:
        # ignore the non-problem lines, i.e. not starting with ID
        if not re.match('\d+\t', p):
            continue
        # parse the problem
        (pid, pre, hyp, sco, lab) = p.strip().split('\t')
        nli_dict[i] = {'pid':pid, 'p':pre, 'h':hyp, 'r':sco, 'g':lab.lower()}
        i += 1
    report("{} problems read".format(len(nli_dict)), 0, v)
    write_nli_dict(nli_dict, out, fmt, tok=tok, v=v)


############################
def nli_spl(nli_dict, out, tok, v=0):
    '''Write sentences of NLI problems in sentence-per-line format
    '''
    count = 0
    report("Using {} tokenizer".format(tok), 1, v)
    if tok == 'nltk':
        tokenizer = word_tokenize
    elif tok == 'spacy':
        tokenizer = spacy.load("en_core_web_sm")
    else:
        pass
    with open(out, 'w') as f:
        for _, d in sorted(nli_dict.items()):
            for k in 'ph':
                if tok == 'spacy':
                    wr = " ".join([ t.text.strip() for t in tokenizer(d[k]) ])
                elif tok == 'nltk':
                    wr = " ".join(tokenizer(d[k]))
                elif tok == 'native' and f"{k}_btree" in d:
                    binary_tree = d[f"{k}_btree"]
                    wr = " ".join(binaryTree2tokens(binary_tree))
                else:
                    wr = d[k]
                f.write(wr + '\n')
                count += 1
    return count

############################
def nli_prolog(nli_dict, out, cen_labs=True):
    '''Write NLI problems in prolog format
    '''
    count = 0
    cen2ynu = {'entailment': 'yes',
               'contradiction': 'no',
               'neutral': 'unknown'
              }
    with open(out, 'w') as f:
        for i, d in sorted(nli_dict.items()):
            kw = {'p': d['p'].replace("'", r"\'"),
                  'h': d['h'].replace("'", r"\'"),
                  'p_id': 2*i-1,
                  'h_id': 2*i,
                  'g':d['g'] if cen_labs else cen2ynu[d['g']],
                  'pid': d['pid'].replace("'", r"\'"),
                 }
            f.write("% problem id = {pid}\n"
                    "sen_id({p_id}, '{pid}', 'p', '{g}', '{p}').\n"
                    "sen_id({h_id}, '{pid}', 'h', '{g}', '{h}').\n".format(**kw))
            count += 2
    return count

################################################################################
################################################################################
def snlijson2nli(file_stream, out, fmt, tok='native', v=0):
    # FIXME: adapt to the global changes
    '''
    '''
    nli_dict = defaultdict(dict)
    i = 1
    possible_labels = ['entailment', 'contradiction', 'neutral']
    for json_prob in file_stream:
        p = json.loads(json_prob)
        if p['gold_label'] in possible_labels:
            nli_dict[i] = {'pid':p['pairID'],
                           'p':p['sentence1'], 'h':p['sentence2'],
                           'g':p['gold_label'],
                           'p_btree': p['sentence1_binary_parse'],
                           'h_btree': p['sentence2_binary_parse']
                          }
            i += 1
    report("{} problems read".format(len(nli_dict)), 0, v)
    write_nli_dict(nli_dict, out, fmt, tok=tok, v=v)

#################################
def binaryTree2tokens(binary_tree):
    '''Convert a binary tree into a list tokens'''
    toks = re.split('[() ]+', binary_tree)
    clean = {'-LRB-':'(', '-RRB-':')'}
    return [ clean.get(t, t) for t in toks if t ]

#################################
def report_about_sen(sen):
    '''Report is something interesting is in the sentence'''
    if sen.find('(') > -1 or sen.find(')') > -1:
        print("PARENTHESIS: {}".format(sen))

#################################
def write_sen_id(sen_list, filepath):
    '''Write the sen_id/5 predicates in the prolog file
       sen_list elements should be a dictionary with keys:
       sen:raw_sentence, sid:int_sentence_id, pid:int_problem_id, ph:p or h,
       gold:gold_label (yes, no, unknown), comment:anything as a prolog comment
    '''
    with open(filepath, 'w') as f:
        for s in sen_list:
            s['sen'] = s['sen'].replace("'", "\'")
            f.write("% {comment}\nsen_id({sid}, {pid}, '{ph}', '{gold}', '{sen}').\n".format(**sen))

#################################
def write_sen_spl(tokenized_sen_list, splfile):
    '''Write tokenized sentecnes per line in a file'''
    with open(splfile, 'w') as f:
        for tok_sen in tokenized_sen_list:
            f.write(' '.join(tok_sen) + '\n')

################################################################################
###################################### MAIN ####################################
################################################################################
if __name__ == '__main__':
    args = parse_arguments()
    # read docs from the file
    dataset2nli = globals()[args.corpus + '2nli']
    # get tokenizer
    with open(args.file, 'r', encoding='UTF-8') as f:
        dataset2nli(f, args.output, args.fmt, tok=args.tokenize, v=args.v)
    # Some stats
    #print_docs(docs)
    # print in files inside a directory
    # write_docs(docs, args.dir)
