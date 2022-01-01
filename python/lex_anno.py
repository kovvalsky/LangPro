#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Annotated raw text with lemma, pos tags, WN senses
'''

#################################
import spacy
import argparse, sys, json, re, requests
from collections import OrderedDict
from utils import write_json, modify_dict

from typing import List
from spacy.language import Language
from spacy.tokens import Token, Doc


def parse_arguments():
    parser = argparse.ArgumentParser(description='Token annotation')

    # Arguments covering directories and files
    parser.add_argument(
    '--raw', metavar="FILE_PATH",
        help="A file with a sentence per line")
    parser.add_argument(
    '--tok', metavar="FILE_PATH",
        help="A file with a tokenized sentence per line")
    parser.add_argument(
    '--json', metavar="FILE_PATH", required=True,
        help="A json output file with annotations")
    parser.add_argument(
    '--spacy', metavar="SPACY MODEL SIZE",
        choices=['sm', 'md', 'lg', 'trf'],
        help="The space model size")
    parser.add_argument(
    '--amuse-wsd', metavar="LANG",
        choices=['EN', 'NL'],
        help="The language for amuse WSD api")
    parser.add_argument(
    '--ids', nargs='*', type=int, metavar="LIST OF IDS",
        help="A list of sentence IDs, i.e. line numbers, to be processed (starts from 1)")
    parser.add_argument(
    '-l', metavar="LANGUAGE", default='en',
        help="Language code for spacy models or Amuse-WSD")
    parser.add_argument(
    '-v', dest='v', action='count', default=0,
        help="Verbosity level")

    # pre-processing arguments
    args = parser.parse_args()
    if args.raw and args.tok:
        raise RuntimeError('Specify only one of --raw and --tok')
    return args

#################################
def lex_annotate(model: Language, docs: List[Doc], ids: List[int]) -> 'OrderedDict[int, List[OrderedDict[str, str]]]':
    def parse_doc(doc: Doc) -> 'List[OrderedDict[str, str]]':
        def parse_tok(token: Token) -> 'OrderedDict[str, str]':
            # pos_ is a UD pos while tag_ is Penn TB pos
            return OrderedDict([('t', token.text), ('l', token.lemma_), ('upos', token.pos_), ('ppos', token.tag_)] +
                               list(token.morph.to_dict().items()))
        return [parse_tok(token) for token in doc]
    docs = model.pipe(docs, disable=['parser', 'ner'], batch_size=128)
    return OrderedDict(zip(ids, (parse_doc(doc) for doc in docs)))

def tokenize(model, sents):
    return [ doc for doc in model.tokenizer.pipe(sents, batch_size=128) ]

#################################
def amuse_wsd_api(sens, lang, batch_size=0):
    '''The api takes care of tokenization, lemmatization, and upos tagging'''
    headers = {'accept': 'application/json', 'Content-Type': 'application/json'}
    url = 'http://nlp.uniroma1.it/amuse-wsd/api/model'
    # sentecnes should be formatted as {"text":"It rains", "lang":"EN"}
    if batch_size:
        res = []
        for i in range(0, len(sens), batch_size):
            input = [ {'text':s, 'lang':lang} for s in sens[i:i+batch_size] ]
            res += requests.post(url, json=input, headers=headers).json()
    else:
        input = [ {'text':s, 'lang':lang} for s in sens ]
        res = requests.post(url, json=input, headers=headers).json()
    return res

###################################
def set_tokens_for_amuse(sents):
    ''' To avoid Amuse API's spacy tokenizer to split t-shirt and make-up (or the/some),
        replace hyphens and slashes with underscores
    '''
    new2old, new_sents = {}, []
    for sen in sents:
        new_sen = []
        for tok in sen.split():
            new_tok = re.sub('(\w)[-/](\w)', r'\1_\2', tok)
            new_sen.append(new_tok)
            if tok != new_tok: new2old[new_tok] = tok
        new_sents.append(' '.join(new_sen))
    return new_sents, new2old

def recover_old_toks(anno_sents, new2old):
    ''' Takes annotated output from amuse API and
        substitutes 'text' values with original text
    '''
    for i, anno_sen in enumerate(anno_sents):
        for j, anno_tok in enumerate(anno_sen['tokens']):
            txt = anno_tok['text']
            anno_sents[i]['tokens'][j]['text'] = new2old[txt] if txt in new2old else txt

#################################
def spacy_meta(nlp):
    meta = OrderedDict([ (k, nlp._meta[k]) \
                         for k in "lang name version spacy_version".split() ])
    return meta

def read_raw_or_tok(raw, tok, meta, spacy=False):
    '''Return a list of sentences and update meta. spacy can be an nlp pipeline'''
    # read tokenized or raw sentences and create Docs out of them
    if raw:
        with open(raw) as F:
            sents = [ l.strip() for l in F ]
            if spacy: return tokenize(spacy, sents)
    elif tok:
        with open(tok) as F:
            if spacy:
                meta['tokenization'] = "pre-tokenized"
                return [ Doc(spacy.vocab, words=l.strip().split()) for l in F ]
            sents = [ l.strip() for l in F ]
    return sents

##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()

    # annotation with SpaCy
    if args.spacy:
        model_type = {'nl':'news', 'en':'web'}
        m = { size: f"{args.l}_core_{model_type[args.l]}_{size}" \
                for size in 'sm md lg trf'.split() }
        nlp = spacy.load(m[args.spacy])
        meta = spacy_meta(nlp)
        meta['sys'] = 'spacy'

        # read tokenized or raw sentences and create Docs out of them
        docs = read_raw_or_tok(args.raw, args.tok, meta, spacy=nlp)

        if args.v >= 1: print(f"{len(docs)} sentences are read")

        idxs, docs = list(zip(*((i, s) for i, s in enumerate(docs, start=1) \
                                            if not args.ids or i in args.ids)))
        sen_anno = lex_annotate(nlp, docs, idxs)

    elif args.amuse_wsd:
        meta = OrderedDict([('sys', 'amuse'), ('api', 'http://nlp.uniroma1.it/amuse-wsd/api/model')])
        # read tokenized or raw sentences and create Docs out of them
        sents = read_raw_or_tok(args.raw, args.tok, meta)
        if args.tok: # change certain tokesn is a way that spacy won't split them
            meta['tokenization'] = "pre-tokenized"
            sents, new2old = set_tokens_for_amuse(sents)
        wsd_sents = amuse_wsd_api(sents, args.amuse_wsd, batch_size=128)
        if args.tok:
            recover_old_toks(wsd_sents, new2old)
        mod_guide = {'text':'t', 'nltkSynset':'wn'} # ignore spacy's pos and lemma
        sen_anno = OrderedDict()
        for i, wsd in enumerate(wsd_sents, start=1):
            sen_anno[i] = [ modify_dict(t, mod_guide) for t in wsd['tokens'] ]

    # write annotations in a json format
    meta['command'] = ' '.join(sys.argv)
    write_json(args.json, sen_anno, meta=meta)
