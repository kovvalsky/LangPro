#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Modify ccg derinations in prolog files

Usage:
    THIS.py --ccg ccg.pl --sys easyccg --anno-json tok.off.json --anno-ord 1 2 o
'''



#################################
import argparse, sys, json, re


def parse_arguments():
    parser = argparse.ArgumentParser(description='Modifying ccg derivations')

    # Arguments covering directories and files
    parser.add_argument(
    '--ccg', metavar="FILE_PATH", required=True,
        help="A prolog file with ccg derivations")
    parser.add_argument(
    '--sys', metavar="STR",
        help="System name to be injected in the ccg tree IDs")
    parser.add_argument(
    '--out', metavar="FILE_PATH",
        help="A prolog output file")
    parser.add_argument(
    '--anno-ord', metavar="Anno Order", nargs='+',
        help="Order of annotations in the output ccg. Numbers represent existing N-th annotation while string-identifiers correspond to new annotations")
    parser.add_argument(
    '--anno-json', metavar="FILE_PATH",
        help="Annotation file from where annotatiosn will be extracted")

    # pre-processing arguments
    args = parser.parse_args()
    return args

#########################
def parse_t_term(term, arity=None):
    prefix, body, suffix = re.match('(\s*t\()(.+?)([\s\),.]+)$', term).groups()
    # terrible pattern # FIXME
    single_anno_pattern = r"'(?:(?:(?:'')|(?:\\')|[\w\./\-]+)+|,)'|[\w\-\\/:\)\(]+"
    annos = re.findall(single_anno_pattern, body)
    assert not arity or len(annos) == arity, \
        f"Arity of {term.strip()} should be {arity}: {body}"
    return prefix, annos, suffix

def get_anno(ord, idx_anno, token_anno):
    '''Ord is eithr position of the annotation in the old annotatiosn
       or a key in the input annotation
    '''
    if ord in idx_anno:
        # no changes needs to be done as they are already prolog safe terms
        anno = idx_anno[ord]
        return anno
    anno = token_anno[ord]
    # sanity check that ccg annos includ token? #TODO
    if re.match('(\d+)-(\d+)$', anno):
        return anno
    # make prolog safe
    return "'" + anno.replace("'", r"''") + "'"

##############################################################################
################################ Main function ################################
if __name__ == '__main__':
    args = parse_arguments()

    ccg_start = 'ccg\((\d+)'
    t_start = "\s*t\("
    t_arity = None
    sid, tid = 0, 0 # sentecne id and token id

    if args.anno_json:
        with open(args.anno_json) as F:
            d = json.load(F)
            d.pop('meta')

    with open(args.ccg) as F:
        ccg_pl = F.readlines()

    O = open(args.out, 'w') if args.out else sys.stdout

    for l in ccg_pl:
        if re.match(ccg_start, l):
            sid = re.match(ccg_start, l).group(1)
            tid = 0
            # modify "ccg(" part
            if args.sys is not None:
                if args.sys == '': # remove system identifier
                    l = re.sub(f"{ccg_start}:[^,\s]+", 'ccg(\1', l)
                else: # add system identifier
                    l = re.sub(ccg_start, f'ccg(\\1:{args.sys}', l)
        elif re.match(t_start, l) and args.anno_ord:
            # rearranging, changing or adding new annotatiosn to the existing
            t_prefix, t_anno, t_suffix = parse_t_term(l, arity=t_arity)
            tid += 1
            if not t_arity: t_arity = len(t_anno)
            indx_anno = { str(i): anno for i, anno in enumerate(t_anno, start=1) }
            sen_input_anno = d[sid] if sid in d else d[str(sid)]
            tok_input_anno = sen_input_anno[tid-1]
            new_t_anno = [ get_anno(j, indx_anno, tok_input_anno) for j in args.anno_ord ]
            l = f"{t_prefix}{', '.join(new_t_anno)}{t_suffix}"
        O.write(l)

    if args.out: O.close()


# add offsets from json fiel to exsiting ccg derivations
