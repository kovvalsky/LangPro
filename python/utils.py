#!/usr/bin/env python3
# -*- coding: utf8 -*-

'''Utility functions
'''

#################################
import json, re
from collections import defaultdict, OrderedDict
from evaluate import canonical_label
import requests


#################################
def write_json(filename, sen_annotations, meta=None):
    '''write annotations in a json format. Each token on a separate line
    '''
    with open(filename, 'w') as F:
        anno_list = []
        for i, toks in sen_annotations.items():
            tokens = ',\n    '.join([ json.dumps(t, ensure_ascii=False) for t in toks ])
            anno_list.append(f'  "{i}": [\n    {tokens} ]')
        content = ',\n'.join(anno_list)
        meta_json = json.dumps(meta, ensure_ascii=False)
        F.write(f'{{\n  "meta":{meta_json},\n{content}\n}}')

#################################
def read_nli_sen_pl(sen_pl):
    '''Read sen.pl file into a dictionary'''
    nli = defaultdict(dict)
    pattern = re.compile(r"sen_id\((\d+), (\d+), '([ph])', ('[^']+')?,? ?('[^']+'), ('.+')\).")
    with open(sen_pl) as F:
        for l in F:
            if not l.strip(): continue # ignore empty lines
            if l.strip().startswith('%'): continue # ignore prolog comments
            m = pattern.match(l)
            if m:
                sid, pid, ph, part, label, sen = m.groups()
                nli[pid][ph] = sen.strip("'").replace("\\'", "'")
                nli[pid]['l'] = canonical_label(label.strip("'"))
                nli[pid]['part'] = part.strip("'") if part else part
                nli[pid][(ph, 'sid')] = int(sid)
    return nli

#################################
def read_t_leaf(line):
    # t(n/n, 'young', 'young', 'JJ', 'I-NP', 'O'),
    r = "\s*t\(([^,]+), '(.+?)', '(.+?)', '(.+?)', '(.+?)', '(.+?)'\)"
    m = re.match(r, line)
    if m:
        c, t, l, p, ch, n = m.groups()
        t = t.replace("\\'", "'")
        l = l.replace("\\'", "'")
        return OrderedDict([('t',t),('l',l.lower()),('ppos',p),('ner',n),
                            ('ccg',c), ('chk',ch)])
    return None

#################################
def read_ccg_pl(fn):
    toks = []
    sens = []
    with open(fn) as F:
        for line in F:
            if re.match('ccg\(\d+,\n$', line):
                if toks:
                    sens.append((sen_id, toks))
                    toks = []
                sen_id = int(line[4:-2])
                continue
            t = read_t_leaf(line)
            if t: toks.append(t)
    return OrderedDict(sens)

#################################
def modify_dict(d, guide, ord=True):
    ''' Guide is a dictionary that specifies which key-values are kept
        and for which key-values only key is renamed.
    '''
    if ord:
        return OrderedDict([ ((v if v else k), d[k]) for k, v in guide.items() ])
    else:
        return { (v if v else k):d[k] for k, v in guide.items() }
