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
        help='How to tokenize the text')
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, action='count',
        help='verbosity level of reporting')
    args = parser.parse_args()
    return args

#################################
def report(message, priority, verbosity):
    if priority <= verbosity:
        print(message)

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
    if fmt == 'spl':
        cnt = nli_spl(nli_dict, out, tok, v=v)
        report('{} sentences written for parsing'.format(cnt), 1, v)
    elif fmt == 'sen.pl':
        cnt = nli_prolog(nli_dict, out, cen_labs=False)
        report('{} NLI sentences written'.format(cnt), 1, v)
    else:
        raise RuntimeError("Unknown format /{}/".format(fmt))


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
                  'g':d['g'] if cen_labs else cen2ynu[d['g']]
                 }
            kw = {**d, **kw}
            f.write("% problem id = {pid}\n"
                    "sen_id({p_id}, {pid}, 'p', '{g}', '{p}').\n"
                    "sen_id({h_id}, {pid}, 'h', '{g}', '{h}').\n".format(**kw))
            count += 2
    return count

################################################################################
################################################################################
def snlijson2nli(file_stream, probpl, splfile, v=0):
    # FIXME: adapt to the global changes
    '''From the stream of the file of NLI problems create sen.pl, .spl, and info.pl files
    '''
    #sens = []
    nli_probs = []
    for pid, json_prob in enumerate(file_stream, start=1):
        p = json.loads(json_prob)
        # prem = {'sid':len(sns)+1, 'pid':pid, 'ph':'p',
        #         'gold':p['gold_label'], 'sen':p['sentence1'],
        #         'comment':"captionID={}; pairID={}".format(p['captionID'], p['pairID']),
        #         'btree':p['sentence1_binary_parse']
        #        }
        # hypo = {'sid':len(sns)+2, 'pid':pid, 'ph':'h',
        #         'gold':p['gold_label'], 'sen':p['sentence2'],
        #         'comment':"pairID={}".format(p['pairID']),
        #         'btree':p['sentence2_binary_parse']
        #        }
        # problem dictionary
        poss_labs = ['entailment', 'contradiction', 'neutral']
        labels = [ l for l in p['annotator_labels'] if l in poss_labs ]
        assert len(p['annotator_labels']) == len(labels), "Ill formed labels"
        prob = {'pid':pid,
                'pairID':p['pairID'],
                'labels':labels,
                'captionID':p['captionID'],
                'gold':p['gold_label'],
                'p':p['sentence1'],
                'h':p['sentence2'],
                'p_id':2*pid-1,
                'h_id':2*pid,
                'p_btree':p['sentence1_binary_parse'],
                'h_btree':p['sentence2_binary_parse']
               }
        # sanity check
        report_about_sen(prob['p'])
        report_about_sen(prob['h'])
        #
        nli_probs.append(prob)
        #sens += [prem, hypo]
    #report("{} sentences read".format(len(sens)), 0, v)
    report("{} problems read".format(len(nli_probs)), 0, v)
    write_snli_probs(nli_probs, probpl)
    write_sen_spl([ binaryTree2tokens(tree) for p in nli_probs for tree in [p['p_btree'], p['h_btree']] ], splfile)

############################
def write_snli_probs(snli_probs, prolog):
    '''Write the snli problem in the prolog file
    '''
    lab_ord = ['entailment', 'contradiction', 'neutral']
    with open(prolog, 'w') as f:
        for i, p in enumerate(snli_probs, start=1):
            #if i != 145: continue
            p['p'] = p['p'].replace("'", r"\'")
            p['h'] = p['h'].replace("'", r"\'")
            p['lab_num'] = len(p['labels'])
            c = Counter(p['labels'])
            p['lablist'] = ', '.join(p['labels'])
            p['dist'] =  ','.join([ str(c[i]) for i in lab_ord ])
            f.write("prob({pid}, ('{pairID}','{captionID}'), {lab_num}, [{dist}], {gold},\n"
                    "\t({p_id}, '{p}'),\n\t({h_id}, '{h}'),\n\t[{lablist}]).\n".format(**p))

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
