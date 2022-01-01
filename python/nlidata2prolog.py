#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''
Convert SICK into the sen.pl and sentence-per-line formats
'''

import os, sys, re, argparse, json
from os import path as op
from collections import Counter, defaultdict, OrderedDict
import xml.etree.ElementTree as ET
import nltk, spacy
from nltk.tokenize import word_tokenize
from utils import write_json

#################################
def parse_arguments():
    '''Read arguments from a command line'''
    parser = argparse.ArgumentParser(description='Extract sentences per line for parsing')
    parser.add_argument(
    '--files', metavar='FILE PATHS', nargs='+', required=True,
        help='Files containing NLI data. If files represent a split, then provide split names (e.g., TRAIN file1 TEST file2)')
    parser.add_argument(
    '--output', metavar='FILE PATH', required=True,
        help='File for writing output')
    parser.add_argument(
    '--ext', nargs="+", required=True, choices=['spl', 'sen.pl', 'off.json'],
        help='Format of the output file')
    parser.add_argument(
    '--corpus', required=True, choices=['sick_semeval', 'snlijson'],
        help='Corpus to be converted')
    parser.add_argument(
    '--tokenize', default='nltk', choices=['raw', 'nltk', 'spacy', 'own'],
        help='How to tokenize the text. "own" works for snli.jsonl files \
             which comes with parsed trees.')
    parser.add_argument(
    '-v', '--verbose', dest='v', default=0, action='count',
        help='verbosity level of reporting')
    args = parser.parse_args()
    args.files = process_files_arg(args.files)
    return args

def process_files_arg(files):
    # all are files (i.e., without split names)
    if all([ op.isfile(f) for f in files ]):
        return [ (None, f) for f in files ]
    # at odd positions there are no files while at even positions there are
    if all([ op.isfile(f) for f in files[1::2] ]) and\
       all([ not op.isfile(f) for f in files[::2] ]):
        return list(zip(files[::2], files[1::2]))

#################################
def report(message, priority, verbosity):
    if priority <= verbosity:
        print(message)

def sick_semeval2nli(fn, part=None, v=0):
    '''read nli problems from sick dataset files
    '''
    nli_dict = dict()
    with open(fn, 'r', encoding='UTF-8') as f:
        for p in f:
            # ignore the non-problem lines, i.e. not starting with ID
            if not re.match('\d+\t', p): continue
            # parse the problem
            (pid, pre, hyp, sco, lab) = p.strip().split('\t')
            nli_dict[int(pid)] = {'pid':pid, 'p':pre, 'h':hyp, 'r':sco, 'g':lab.lower()}
            if part: nli_dict[int(pid)]['part'] = part
    report("{} problems read".format(len(nli_dict)), 0, v)
    return nli_dict


########################################################
def write_nli_dict(nli_dict, sen_id, out, exts, tok='raw', v=0):
    if 'spl' in exts:
        sen_tokens = nli_spl(nli_dict, sen_id, out, tok, ext='.spl', v=v)
        report(f"{len(sen_tokens)} sentences written for parsing (spl)", 1, v)
    if 'sen.pl' in exts:
        cnt = nli_prolog(nli_dict, sen_id, out, ext="_sen.pl", cen_labs=False)
        report(f"{cnt} NLI sentences written (sen.pl)", 1, v)
    if 'off.json' in exts:
        # no need to rerun tokenization if it was already done for spl
        sen_tokens = sen_tokens if 'spl' in exts \
                     else nli_spl(nli_dict, sen_id, None, tok, v=v)
        sid_off = tok_off_json(nli_dict, sen_id, out, sen_tokens, tok, ext='.off.json', v=v)
        report(f"{sid_off} NLI sentences written (off.json)", 1, v)

############################
def tok_off_json(nli_dict, sen_id, out, sen_tokens, tokenizer, ext='', v=0):
    '''Recover and write token offsets from raw sentences and their list of tokens
    '''
    sens = sorted(sen_id, key=sen_id.get)
    assert len(sens) == len(sen_tokens), "Raw and tokenized sentence number mismatch"
    # meta info
    sid_off = OrderedDict()
    for sen, toks in zip(sens, sen_tokens):
        fr0, toks_off = 0, []
        for t in toks:
        # Detect initial token start position
            fr, l = quote_sensitive_find(sen, t, fr0) #FIXME prefixes can be omitted
            if fr < 0 or (sen[fr0:fr] and not re.match('\s+', sen[fr0:fr])):
                raise RuntimeError(f"weird: /{t}/ in /{s}/ at {fr}")
            assert sen[fr:fr+l] == t, \
                f"mismathc with tok off: {sen[fr:fr+l]} != {t}"
            toks_off.append(OrderedDict([('t', sen[fr:fr+l]), ('o', f'{fr}-{fr+l}')]))
            fr0 = fr + l
        sid_off[sen_id[sen]] = toks_off
    meta = OrderedDict([('sys', tokenizer), ('command', ' '.join(sys.argv))])
    write_json(f"{out}.off.json", sid_off, meta=meta)
    return sid_off


############################
def nli_spl(nli_dict, sen_id, out, tok, ext='', v=0):
    '''Write sentences of NLI problems in sentence-per-line format
    '''
    count, sen_tokens = 0, []
    report("Using {} tokenizer".format(tok), 1, v)
    if tok == 'nltk':
        tokenizer = word_tokenize
    elif tok == 'spacy':
        tokenizer = spacy.load("en_core_web_sm")
    else:
        pass
    # id_sen = { i: s for (s, i)  in sen_id.items() }
    # assert len(id_sen) == len(sen_id), "sen_id and id_sen have mismatch"
    already_written_sen = set()
    if out: F = open(f"{out}{ext}", 'w')
    for pid, d in sorted(nli_dict.items()):
        for k in 'ph':
            if d[k] in already_written_sen: continue
            if tok == 'spacy':
                tokens = [ t.text.strip() for t in tokenizer(d[k]) ]
            elif tok == 'nltk':
                tokens = tokenizer(d[k])
            elif tok == 'own' and f"{k}_btree" in d:
                tokens = binaryTree2tokens(d[f"{k}_btree"])
            else:
                tokens = d[k].split(' ') # for comaptibility with join
            sen_tokens.append(tokens)
            if out: F.write(' '.join(tokens) + '\n')
            count += 1
            already_written_sen.add(d[k])
            assert sen_id[d[k]] == count, f"Mismatch with sentence IDs"
    if out: F.close()
    return sen_tokens

############################
def nli_prolog(nli_dict, sen_id, out, ext='', cen_labs=True):
    '''Write NLI problems in prolog format
    '''
    count = 0
    cen2ynu = {'entailment': 'yes',
               'contradiction': 'no',
               'neutral': 'unknown'
              }
    with open(f"{out}{ext}", 'w') as f:
        for i, d in sorted(nli_dict.items()):
            part = f", '{d['part'].lower()}'" if 'part' in d else ''
            p, h = d['p'].replace("'", r"\'"), d['h'].replace("'", r"\'")
            p_id, h_id = sen_id[d['p']], sen_id[d['h']]
            g = d['g'] if cen_labs else cen2ynu[d['g']]
            pid = d['pid'].replace("'", r"\'")
            f.write(f"% problem id = {pid}\n"
                    f"sen_id({p_id}, '{pid}', 'p'{part}, '{g}', '{p}').\n"
                    f"sen_id({h_id}, '{pid}', 'h'{part}, '{g}', '{h}').\n")
            count += 2
    return count

################################################################################
################################################################################
def snlijson2nli(fn, part=None, v=0):
    # FIXME: adapt to the global changes
    '''
    '''
    nli_dict = dict()
    possible_labels = ['entailment', 'contradiction', 'neutral']
    with open(fn, 'r', encoding='UTF-8') as f:
        for json_prob in f:
            p = json.loads(json_prob)
            if p['gold_label'] in possible_labels:
                nli_dict[p['pairID']] = {
                               'pid':p['pairID'],
                               'p':p['sentence1'], 'h':p['sentence2'],
                               'g':p['gold_label'],
                               'p_btree': p['sentence1_binary_parse'],
                               'h_btree': p['sentence2_binary_parse']
                              }
                if part: nli_dict[p['pairID']]['part'] = part
    report("{} problems read".format(len(nli_dict)), 0, v)
    return nli_dict

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

#################################
def quote_sensitive_find(raw, tok, tok_fr):
    '''Check if tok was replaced or not and based on that
       carry out the search (this is relevant only for nltk tokenizer)
    '''
    fr2 = raw.find(tok, tok_fr)
    if tok in ['``', "''"]:
        fr1 = raw.find('"', tok_fr)
        # case when " is replaced with ``/''
        if fr1 >= 0 and (fr2 < 0 or fr1 < fr2):
            # treat this differently as real token length has changed from 1 to 2
            return fr1, 1
    return fr2, len(tok)

#################################
def sen2id(id_prob):
    '''Give id to sentences following the problem ID order'''
    sen_id = dict()
    for _, p in sorted(id_prob.items()):
        for s in (p['p'], p['h']):
            if s not in sen_id:
                sen_id[s] = len(sen_id) + 1
    return sen_id

################################################################################
###################################### MAIN ####################################
################################################################################
if __name__ == '__main__':
    args = parse_arguments()
    # detect the conversion function
    dataset2nli = globals()[args.corpus + '2nli']
    # convert problems and gather in a single dict
    id_prob = dict()
    for split_name, fn in args.files:
        # TODO Dict[ID,Pair] is not a general shape of NLI problem
        nli_dict = dataset2nli(fn, part=split_name, v=args.v)
        id_prob = {**id_prob, **nli_dict}
    # map sentences to ids, useful to parse a multi-occurring sentence once
    sen_id = sen2id(id_prob)

    # write problems/sentences in the file
    write_nli_dict(id_prob, sen_id, args.output, args.ext, \
                       tok=args.tokenize, v=args.v)


    # Some stats
    # print_docs(docs)
    # print in files inside a directory
    # write_docs(docs, args.dir)
