#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Merge compatible token-level annotations
'''

#################################
import argparse, sys, json, re
from collections import OrderedDict, defaultdict
from utils import write_json


def parse_arguments():
    parser = argparse.ArgumentParser(description='Merge annotations')

    # Arguments covering directories and files
    parser.add_argument(
    '--json-ann', action="append", required=True, nargs='+',
        metavar="LIST OF [file_path|keys]",
        help="File paths for annotation files followed by the corresponding key list for each file. A key that is not system specific is followed by '!' (e.g., in case of token offset write 'o!').")
    parser.add_argument(
    '--shared-keys', metavar="STR LIST", nargs='+',
        help="A key that is shared by all annotations and that have the same values. For example, 't' is such for token values")
    parser.add_argument(
    '--json', metavar="FILE_PATH", required=True,
        help="A json output file with annotations")
    parser.add_argument(
    '--ids', nargs='*', metavar="LIST OF IDS",
        help="A list of sentence IDs, i.e. line numbers, to be processed (starts from 1)")

    # pre-processing arguments
    args = parser.parse_args()
    return args


def check_anno_compatibility(sys_annos, shared_keys):
    # get all sentence ids
    sids = set([ int(k) for d in sys_annos.values() for k in d ])
    sids = [ str(i) for i in sorted(sids) ]
    #
    for sid in sids:
        sen_annos = [ sys_annos[sys][sid] for sys in sys_annos if sid in sys_annos[sys] ]
        for tok_annos in zip(*sen_annos):
            for k in shared_keys:
                values = [ anno[k] for anno in tok_annos ]
                assert len(set(values)) == 1, f"{values} should have the same elements"

def clean(k):
    return k[0:-1] if k[-1] == '!' else k

##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()
    meta = OrderedDict()
    meta['command'] = ' '.join(sys.argv)

    sys_annos, sys_keys = OrderedDict(), OrderedDict()
    # dkey stands for dictionary key (as in annotations their value is dict:sys->anno)
    # while ukey is unique key, i.e., they are not system-soecific
    dkey_systems, dkey_order, ukey_sys = defaultdict(list), [], OrderedDict()
    for path_keys in args.json_ann:
        path, keys = path_keys[0], path_keys[1:]
        #print(f"Reading {path}")
        with open(path) as F:
            annos = json.load(F)
            sys = annos['meta']['sys']
            meta[sys] = annos.pop('meta')
            sys_annos[sys], sys_keys[sys] = annos, keys
            for k in keys: dkey_systems[clean(k)].append(sys)
        # cleaning keys and distinguishing sys-specific from unique keys
        for k in keys:
            if clean(k) != k:
                # if several files have the unique keys the latest will be taken
                ukey_sys[clean(k)] = sys
            elif k not in dkey_order:
                # order of system-specific keys according to which they will be written
                dkey_order.append(k)

    # takes care of annotation key ordering and sys annotation ordering inside annotation keys
    dkey_systems = OrderedDict([ (ck, dkey_systems[ck]) for ck in dkey_order ])
    meta['sys_order'] = dkey_systems

    if args.shared_keys:
        check_anno_compatibility(sys_annos, args.shared_keys)

    # FIXME what if first sys has incomplete annotations?
    first_sys_annos = next(iter(sys_annos.values()))
    sorted_sid = sorted(first_sys_annos.keys(), key=int)
    sid_len = { sid: len(tokens) for sid, tokens in first_sys_annos.items() }

    merged_annos = OrderedDict()
    for sid in sorted_sid:
        if args.ids and sid not in args.ids: continue
        merged_tokens = []
        for i in range(sid_len[sid]):
            # first, deal with sys-neutral keys
            # merged_token = OrderedDict([ (k, sys_annos[sys][sid][i][k]) \
            #         for k, sys in ukey_sys.items() if sid in sys_annos[sys] ])
            merged_token = OrderedDict()
            for k, sys in ukey_sys.items():
                merged_token[k] = sys_annos[sys][sid][i][k] \
                                  if sid in sys_annos[sys] else 'NULL'
            # deal with sys-specific keys
            for k, sys_list in dkey_systems.items():
                # merged_token[k] = OrderedDict([ (s, sys_annos[s][sid][i][k]) \
                #     for s in sys_list if sid in sys_annos[s] ])
                merged_token[k] = [ sys_annos[s][sid][i][k] \
                                    if sid in sys_annos[s] else 'NULL' \
                                    for s in sys_list ]
            merged_tokens.append(merged_token)
        merged_annos[sid] = merged_tokens

    # write annotations in a json format
    write_json(args.json, merged_annos, meta=meta)
