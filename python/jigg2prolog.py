"""
Scan an entire directory containing a directory for each NLI problem.
Create ccg.pl and sen.pl files from jigg XML and CoNLL-U files, respectively.

Usage example:
    python3 python/jigg2prolog.py sick_trial -o sick_trial/ccg.pl -p sick_trial/sen.pl -v 2

sick_trial is a directory containing subdirectories for each problem.
Each problem subdirectory contains a jigg XML file with CCG parse
and a CoNLL-U file with NLI problem raw text.
"""

import argparse
import sys, re, os
import xml.etree.ElementTree as ET
from typing import TextIO

def xml_to_prolog(input_path: str, output: TextIO, verbosity: int = 0) -> None:
    """
    Reads a CCG XML file and writes Prolog CCG terms to an output stream.
    """
    prob_id = int(re.match(r'.+?(\d+)\.', input_path.split('/')[-1]).group(1))
    tree = ET.parse(input_path)
    root = tree.getroot()

    for sentence in root.iter('sentence'):
        sent_id = att(sentence, 'id')
        ccg_el = sentence.find('ccg')
        if ccg_el is None:
            if verbosity >= 1:
                print(f"Warning: No <ccg> element found for sentence {sent_id}",
                      file=sys.stderr)
            continue

        # Build a lookup of span_id -> span element
        spans = {att(sp, 'id'): sp for sp in ccg_el.findall('span')}

        # Find root span
        root_span_id = att(ccg_el, 'root')
        root_span = spans[root_span_id]
        try:
            term = build_term(root_span, spans, 2, verbosity=verbosity)
            sid = prob_id * 2 - (1 if sent_id  == "s0" else 0)
            output.write(f"% problem id = {prob_id}{'p' if sent_id  == 's0' else 'h'}\n")
            output.write(f"ccg({sid},\n {term}).\n\n")
        except Exception as e:
            if verbosity >= 1:
                print(f"Error in build_term for {sent_id} of prob {prob_id} in '{input_path}':\n{e}",
                      file=sys.stderr)


def build_term(span: ET.Element, spans: dict,
               level: int = 0, indent: str = ' ', verbosity: int = 0) -> str:
    """
    Recursively builds a Prolog term string from a span element.
    """
    pad = indent * level
    # Terminal token (leaf node)
    if span.get('terminal') is not None:
        tok, lem, pos = [ att(span, attr).replace("'", "\\'")
                         for attr in ('surf', 'base', 'pos')]
        cat  = normalize_cat(att(span, 'category'))
        return f"t({cat},'{tok}','{lem}','{pos}','O','O')"

    rule_arity = {'fa': 2, 'ba': 2, 'fc': 2, 'bc': 2, 'tr': 2,
                  'lex': 1, 'lx': 1, 'lp': 2, 'rp': 2, 'conj': 2,
                #   '?':2
                  }

    rule = att(span, 'rule')
    rule = "lx" if rule == "lex" else rule  # treat lex as lx for better prolog output
    if rule not in rule_arity:
        raise ValueError(f"Unknown rule '{rule}' in span with id {att(span, 'id')}")
    cat = normalize_cat(att(span, 'category'))
    children_ids = att(span, 'child').split()
    child_terms = [build_term(spans[cid], spans, level+1, verbosity=verbosity)
                   for cid in children_ids]

    if rule_arity[rule] == 1:
        # lx(target_cat, src_cat, child)
        assert len(child_terms) == 1, \
            f"Expected 1 child for rule '{rule}', got {len(child_terms)}"
        child_cat = normalize_cat(att(spans[children_ids[0]], 'category'))
        return f"{rule}({cat}, {child_cat},\n{pad}{child_terms[0]})"
    elif rule_arity[rule] == 2:
        assert len(child_terms) == 2, \
            f"Expected 2 children for rule '{rule}', got {len(child_terms)}"
        if rule == '?':
            # Format: rule(result_cat, left_child_term, right_child_term)
            if verbosity >= 2:
                left_cat = normalize_cat(att(spans[children_ids[0]], 'category'))
                right_cat = normalize_cat(att(spans[children_ids[1]], 'category'))
                print(f"Warning: Using '?' rule: {left_cat} {right_cat} -> {cat}'",
                      file=sys.stderr)
            return f"unk_rule({cat},\n{pad}{child_terms[0]},\n{pad}{child_terms[1]})"
        if rule == 'conj':
            # For conjunction, we want to keep the original category of the left child
            # Format: rule(result_cat, base_cat, left_child_term, right_child_term)
            right_cat = normalize_cat(att(spans[children_ids[1]], 'category'))
            return f"{rule}({cat},{right_cat},\n{pad}{child_terms[0]},\n{pad}{child_terms[1]})"
        # ordinary binary rules
        # Format: rule(result_cat, left_child_term, right_child_term)
        return f"{rule}({cat},\n{pad}{child_terms[0]},\n{pad}{child_terms[1]})"
    else:
        raise ValueError(f"Unsupported arity {rule_arity[rule]} for rule '{rule}'")


def normalize_cat(cat: str) -> str:
    """
    Converts category strings like 'S\\NP' or '(S\\NP)/(S\\NP)' to
    lowercase Prolog-friendly atoms, e.g. s\\np, (s\\np)/(s\\np).
    Handles attributes too, e.g. 'NP[nb]' -> 'np:nb' or 'NP[nb=true]' -> 'np:nb'.
    """
    if cat == ',':
        return 'comma'
    # Keep parentheses and slashes; lowercase; replace backslash sequences
    cat = cat.strip().lower().replace('=true', '')
    # Map common sentence types
    cat = re.sub(r'([a-z]+)\[([a-z]+)\]', r'\1:\2', cat)
    # Normalize spaces around slashes
    cat = cat.replace(' ', '')
    return cat


def indent_term(term: str, level: int, indent: str = ' ') -> str:
    """
    Simple pretty-printer: inserts newlines and indentation after each
    opening parenthesis that contains a comma, to mirror the target style.
    """
    result = []
    depth = 0
    i = 0
    pad = indent * level

    while i < len(term):
        ch = term[i]
        if ch == '(':
            result.append(ch)
            depth += 1
            result.append(f"\n{pad * depth}")
        elif ch == ')':
            depth -= 1
            result.append(f"\n{pad * depth}")
            result.append(ch)
        elif ch == ',':
            result.append(',')
            result.append(f"\n{pad * depth}")
            # Skip any space after comma
            if i + 1 < len(term) and term[i + 1] == ' ':
                i += 1
        else:
            result.append(ch)
        i += 1

    return pad + ''.join(result)


def att(element: ET.Element, attr: str) -> str:
    """ Helper function to get an attribute value from an XML element,
        with error handling for missing attributes.
    """
    try:
        return element.attrib[attr]
    except KeyError:
        raise ValueError(
            f"Missing required attribute '{attr}' on <{element.tag}> element "
            f"with attribs: {element.attrib}"
        )


def conllu_to_prolog(input_path: str, output: TextIO, v: int = 0) -> None:
    """
    Reads NLI problem from a CoNLL-U file and write it in a prolog format to stream.
    """
    label_mapping = {'entailment':'yes', 'neutral':'unknown', 'contradiction':'no'}
    prob_id = int(re.match(r'.+?(\d+)\.', input_path.split('/')[-1]).group(1))
    with open(input_path, 'r') as f:
        content = f.read().strip()
        label = re.search(r'# entailment_label = ([A-Z]+)', content).group(1).lower()
        label = label_mapping[label]
        premise, hypothesis = [ s.strip().replace("'", "\\'")
                               for s in re.findall(r'# text = ([^\n]+)', content) ]
        comment = f"% problem id = {prob_id}"
        premise = f"sen_id({2*prob_id-1}, {prob_id}, 'p', '{label}', '{premise}')."
        hypothesis = f"sen_id({2*prob_id}, {prob_id}, 'h', '{label}', '{hypothesis}')."
        output.write(f"{comment}\n{premise}\n{hypothesis}\n")


def collect_files(input_path: str, fn_regex: list, v: int = 0) -> list[str]:
    """
    If input_path is a file, return it directly.
    If it's a directory, walk it recursively and collect all files with a matching regex.
    For example, this helps to get paired jigg XML and CoNLL-U files for each problem dir.
    """
    if os.path.isfile(input_path):
        return [input_path]

    # walk down the directory and collect file tuples matching all regexes in fn_regex
    if os.path.isdir(input_path):
        matches = []
        for dirpath, dirnames, filenames in os.walk(input_path):
            dirnames.sort()  # walk subdirectories in sorted order
            file_list = []
            # For each regex, find matching files in the current directory
            for regex in fn_regex:
                for fn in sorted(filenames):
                    if re.search(regex, fn):
                        full_path = os.path.join(dirpath, fn)
                        file_list.append(full_path)
                        if v >= 3:
                            print(f"  Found: {full_path}", file=sys.stderr)
            # we need all regexes to match in the same directory
            if len(file_list) == len(fn_regex):
                matches.append(file_list)
        if v >= 2:
            print(f"Total: {len(matches)} /{fn_regex}/ file(s)",
                  f"found under '{input_path}'", file=sys.stderr)
        return matches
    else:
        print(f"Error: '{input_path}' is neither a file nor a directory.", file=sys.stderr)
        sys.exit(1)


def write_prolog_operators(output: TextIO):
    output.write(":- op(601, xfx, (/)).\n"
                 ":- op(601, xfx, (\\)).\n"
                 ":- multifile ccg/2, id/2.\n"
                 ":- discontiguous ccg/2, id/2.\n\n")

def parse_args():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        'input',
        help='Path to the input XML file or directory containing jigg XML files'
    )
    parser.add_argument(
        '-o', '--ccg-out',
        metavar='FILE',
        help='Write prolog ccg trees to FILE instead of stdout'
    )
    parser.add_argument(
        '-p', '--prob-out',
        metavar='FILE',
        help='Write NLI problems to prolog FILE'
    )
    parser.add_argument(
        '-v', '--verbosity',
        type=int,
        choices=[0, 1, 2, 3],
        default=0,
        metavar='LEVEL',
        help='Verbosity level: 0=silent, 1=errors, 2=info, 3=debug (default: 0)'
    )
    return parser.parse_args()


def main(input, ccg_out, prob_out, v=0):
    """ Main function to convert CCG XML files to Prolog format" ccg.pl and sen.pl.
        It collects paired jigg XML and CoNLL-U files for each problem,
        converts them to cgg and nli problems and writes them in
        prolog files ccg_out and prob_out, respectively.
    """
    # collect paired jigg XML and CoNLL-U files for each problem
    paired_jigg_conllu_files = collect_files(input, fn_regex=["jigg.xml", "conllu"], v=v)

    if not paired_jigg_conllu_files:
        print(f"No matching files found in '{input}'.", file=sys.stderr)
        sys.exit(1)

    # Write NLI problems extracted from CoNLL-U files to prob_out in sen.pl format
    with open(prob_out, 'w') as f:
        for _, conllu_path in paired_jigg_conllu_files:
            conllu_to_prolog(conllu_path, f, v=v)

    def process(output: TextIO):
        """ Process each jigg XML file and write Prolog CCG terms to the output stream.
             Also writes Prolog operators and directives at the beginning of the output.
        """
        write_prolog_operators(output)
        for jigg_path, _ in paired_jigg_conllu_files:
            if v >= 2:
                print(f"Processing: {jigg_path}", file=sys.stderr)
            xml_to_prolog(jigg_path, output, verbosity=v)

    if ccg_out:
        with open(ccg_out, 'w') as f:
            process(f)
        if v >= 2:
            print(f"Output written to '{ccg_out}'", file=sys.stderr)
    else:
        process(sys.stdout)

if __name__ == '__main__':
    args = parse_args()
    main(args.input, args.ccg_out, args.prob_out, v=args.verbosity)