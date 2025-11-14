"""
langpro_api.py

Defines Classes and functions for reading and processing
LangPro output such as CCG trees, CCG terms, LLFs,
Tableau proofs, and knowledge relations.
"""

import json, re
from typing import Any, List, Dict
from abc import ABC, abstractmethod
import nltk
from collections import defaultdict, Counter
from nltk import Tree, TreePrettyPrinter

##############################################################
# Classes
##############################################################

INFIX_F = {':', '~>', '@', ',', '/', '\\'}
TYPE_F = {'~>'}
CAT_F = {'/', '\\'}
CATY_F = CAT_F | TYPE_F

# FIXME: the dummy functions are temporary to silence imports in server.py
def from_json(*args):
    pass

def ccg_tree_to_tree(*args):
    pass

# ------------------------------------------------------------
# Abstract base classes that cannot be instantiated but reused
# to define subclasses
class PrologTerm(ABC):
    """Base of everything as everything is a prolog term"""
    @abstractmethod
    def __str__(self):
        pass

    @abstractmethod
    def __repr__(self):
        pass

class CCGCat(ABC):
    """Base of CCG categories"""
    pass

class CaTy(ABC):
    """Base of functional types and categories"""
    pass

class TreeLike(ABC):
    """Base of tree-like structures such as LLFs, CCG derivations, proofs"""
    pass

# ------------------------------------------------------------
# Base class for all Prolog term types

# class PrologTerm:
#     """A base class for representing Prolog terms."""
#     def __repr__(self):
#         return self.__str__()

#     def __str__(self) -> str:
#         raise NotImplementedError("Subclasses must implement __str__")

# superclass for atoms, integers, floats
class Atomic(PrologTerm):
    def __init__(self, value):
        self.value = value

    def __str__(self) -> str:
        return f"{self.value}"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.value})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Atomic) and self.value == other.value

# Represents a Prolog atom (subclass of atomic)
class Atom(Atomic):
    def __init__(self, value: str):
        if not isinstance(value, str):
            cname = self.__class__.__name__
            raise ValueError(f"{cname} expected arg of type str. Found {type(value)}.")
        self.value = value

    def __str__(self) -> str:
        return self.value

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.value})"

# Represents a Prolog integer (subclass of atomic)
class Integer(Atomic):
    def __init__(self, value: int):
        if not isinstance(value, int):
            cname = self.__class__.__name__
            raise ValueError(f"{cname} expected arg of type int. Found {type(value)}.")
        self.value = value

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.value})"

# Represents a Prolog float (subclass of atomic)
class Float(PrologTerm):
    def __init__(self, value: float):
        if not isinstance(value, float):
            cname = self.__class__.__name__
            raise ValueError(f"{cname} expected arg of type float. Found {type(value)}.")
        self.value = value

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.value})"

# Represents a Prolog variable (it is not atomic)
class Var(PrologTerm):
    def __init__(self, value: str):
        if not isinstance(value, str):
            cname = self.__class__.__name__
            raise ValueError(f"{cname} expected arg of type str. Found {type(value)}.")
        self.value = value

    def __str__(self) -> str:
        return self.value

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.value})"

    def __eq__(self, _: object) -> bool:
        NotImplementedError("Prolog var matching is tricky and not supported here.")

# Represents a Prolog compound term (e.g., father(john, X))
class Compound(PrologTerm):
    def __init__(self, f: str, args: List[Any]):
        self.f = f
        self.args = [ Compound(a["functor"], a["args"]) \
                     if isinstance(a, dict) and "functor" in a else a \
                     for a in args ]
        self.nargs = len(args)

    def __str__(self) -> str:
        if self.f in INFIX_F:
            if len(self.args) != 2:
                raise ValueError(f"Arg num for {self.f} expected 2, but got {self.args}")
            ws = ' ' if self.f == ',' else ''
            return f"({self.args[0]}{ws}{self.f}{ws}{self.args[1]})"
        else:
            return f"{self.f}({', '.join(str(arg) for arg in self.args)})"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}([{self.f}], {', '.join(repr(arg) for arg in self.args)})"

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, Compound) and
            self.f == other.f and
            self.args == other.args
        )
    
    # def split(self, sep=None, maxsplit=-1):
    #     """Split the string representation"""
    #     return str(self).split(sep, maxsplit)

    def __len__(self) -> int:
        return len(str(self))

# ------------------------------------------------------------
# Linguistic/semantic framework/theory-specific classes

class AtomCaTy(CaTy):
    """Atomic Category/Types"""
    def __init__(self, atom: str):
        self.value = atom
        if ":" in atom:
            self.main, self.feat = atom.split(":")
        else:
            self.main, self.feat = atom, None

    def __str__(self) -> str:
        return self.main + (f":{self.feat}" \
             if not(self.feat == "_" or self.feat is None or self.feat[0].isupper()) else "")    
    
    def __repr__(self) -> str:
        return f"AtomCaTy({self.main}" + \
            (f":{self.feat}" if self.feat is not None else "") + ")"


class CompCaTy(CaTy):
    """Compound Category/Types"""
    def __init__(self, f: str, args: List[Any]):
        if f not in CATY_F:
            raise ValueError(f"CompCaTy uses a wrong functor: {f}")
        if len(args) != 2:
            raise ValueError(f"CompCaTy expects two args: {args}")
        self.f = f
        self.arg = args[0] # already parsed by parse_caty
        self.fun = args[1]

    def __str__(self) -> str:
        return f"({self.arg}-{self.fun})"    
    
    def __repr__(self) -> str:
        return f"CompCaTy({repr(self.arg)}{self.f}{repr(self.fun)})"


class TreeLeaf(Compound):
    """Tree leaf in CCG derivation-like structures"""
    def __init__(self, f: str, args: List[Any]):
        if f not in {'t'}:
            raise ValueError(f"Terminal Compound uses a wrong functor: {f}")
        super().__init__(f, args)
        self.value = super().__str__()

    # different representation to better fit to a tree leaf
    def __str__(self) -> str:
        return '\n'.join(str(a) for a in self.args)

class TT(Compound):
    """Term-Type a format where a term is always paired with its type"""
    def __init__(self, tt: dict):
        f, args = tt['functor'], tt["args"]
        assert len(args) == 2, f"TT should have 2 args but has {len(args)}"
        assert f == ',', f"TT should have ',' functor but has {f}"
        super().__init__(f, args)
        term, ty = args
        self.type = parse_caty(ty)
        if isinstance(term, str):
            self.term = Var(term)
        else:
            self.term = parse_term(term)

    def __repr__(self) -> str:
        return f"TT({repr(self.term)}, {repr(self.type)})"

    def __str__(self) -> str:
        return f"({self.term} : {remove_outer_parens(str(self.type))})"
    
    def compact(self) -> str:
        return remove_outer_parens(compact_tt(self))
    
    def tree(self):
        return TT2Tree(self)
    
    def pretty_printer(self): 
        return TreePrettyPrinter(self.tree())

    def pretty_print(self): 
        return self.tree().pretty_print()

class AppTT(Compound):
    """Application of two TTs"""
    def __init__(self, fun: dict, arg: dict):
        self.fun, self.arg = parse_term(fun), parse_term(arg)
        super().__init__("@", [self.fun, self.arg])

    def __repr__(self) -> str:
        return f"AppTT({repr(self.fun)}, {repr(self.arg)})"

    def __str__(self) -> str:
        return f"{self.fun} @ {self.arg}"

class AbsTT(Compound):
    """Lambda abstraction of Var and TTs"""
    def __init__(self, var: dict, body: dict):
        self.var, self.body = parse_term(var), parse_term(body)
        super().__init__("λ", [self.var, self.body])

    def __repr__(self) -> str:
        return f"AbsTT({repr(self.var)}, {repr(self.body)})"
    
    def __str__(self) -> str:
        return f"λ{self.var}. {self.body}"

class TLP(Compound):
    """lexical constant is lambda terms that are a tuple of strings (token, lemma, pos tag)"""
    def __init__(self, f: str, args: List[Any]):
        super().__init__(f, args)
        self.tok, self.lem, self.pos = args[0], args[1], args[2]

    # different representation to better fit to a tree leaf
    def __repr__(self) -> str:
        return f"TLP({','.join(repr(a) for a in self.args)})"
    
    def __str__(self) -> str:
        return f"[{','.join(str(a) for a in self.args)}]"
    

class TreeNode(str):
    """Node in tableau proof tree"""
    def __new__(cls, trnd: dict):
        # a couple of checks
        try:
            f, (nd, node_id, rule_app, _) = trnd["functor"], trnd["args"]
            mod_list, head, arg_list, sign = nd["args"]
        except Exception as e:
            raise ValueError(f"Invalid tree node structure: {trnd}") from e        
        if f != 'trnd':
            raise ValueError(f"'trnd' functor is expected, found {f}")
        # process trnd args
        sign = sign == "true"
        rule_app = RuleApp(rule_app) if rule_app else None
        try:
            mod_list = list(map(parse_term, mod_list))
            arg_list = list(map(parse_term, arg_list))
            head = parse_term(head)
        except Exception as e:
            raise ValueError(f"Error parsing trnd args: {nd['args']}") from e
        
        # Create the string representation
        c_mods = ", ".join([mod.compact() for mod in mod_list])
        c_args = ", ".join([arg.compact() for arg in arg_list])
        c_head = head.compact()
        c_rule_app = f"\n{rule_app}" if rule_app else ""
        
        # TODO: improve formatting
        str_repr = f"{node_id}{c_rule_app}\n[{c_mods}]\n{c_head}\n[{c_args}]\n{sign}" 
        str_repr = str_repr.replace(') @ (', ')(').replace(' @ ', ' ').replace('. ', '.')
        # str_repr = "⯁"
        
        # Create the str instance with this representation
        instance = super().__new__(cls, str_repr)
        
        # Store additional attributes
        instance.id = node_id
        # instance.rule_app = RuleApp(rule_app) if rule_app else None
        instance.mod = mod_list
        instance.head = head
        instance.arg = arg_list
        instance.sign = sign

        return instance

    # def __str__(self) -> str:
    #     return "⯁"
    #     return f"NodeID: {self.node_id}, Rule: {self.rule_app}, Sign: {self.sign}"
    
    # def __repr__(self) -> str:
    #     return "⯁"
    #     return f"TreeNode({self.node_id}, {self.rule_app}, {list(self.mod_list)}, {self.head}, {list(self.arg_list)}, {self.sign})"

    # def __len__(self) -> int:
    #     return len(str(self))

class RuleApp(Compound):
    """Rule application info in tableau proof tree nodes"""
    def __init__(self, rule_app: dict):
        assert 'functor' in rule_app, f"Rule app has no functor: {rule_app}"
        print(">>> rule_app = ", rule_app)
        f, args = rule_app['functor'], rule_app["args"]
        super().__init__(f, args)
        self.rule = f
        # define ids and new/old constants
        if len(args) == 1:
            self.ids = args[0]
            self.new = self.old = None
        elif len(args) == 2:
            if isinstance(args[0][0], dict): # first is a list of terms
                old, self.ids = args
                self.new = None
                self.old = [ TT(i).compact() for i in old ]
            elif isinstance(args[1], list): # second is a list of terms
                self.ids, new = args
                self.old = None
                self.new = [ TT(i).compact() for i in new ]
            else:
                raise ValueError(f"Invalid rule app: {args}")
        else:
            raise ValueError(f"Invalid rule app (with 3+ args): {args}")
        
    def __str__(self) -> str:
        new = "" if self.new is None else f"{self.new}, "
        old = "" if self.old is None else f", {self.old}"
        return f"{self.rule}({new}{self.ids}{old})".replace(" ", "")
    
    def __repr__(self) -> str:
        return f"RuleApp({self.rule}, {self.ids}, new={self.new}, old={self.old})"


##############################################################
# Reading JSON data
##############################################################

COMPOUND_F_TYPE_MAP = {'tlp': TLP, 't': TreeLeaf, ':': AtomCaTy,
                       '~>': CompCaTy, '/': CompCaTy, '\\': CompCaTy}

def parse_langpro_json(json_output: Any, v=0) -> Any:
    """
    Recursively converts a Python dictionary/list (from JSON) into PrologTerm objects.
    Args:
        data: The input data, typically a dict, list, or primitive.
        functor: scoping functor, extra help to guess the class of the atomic args
        v: verbosity level
    Returns:
        A PrologTerm object, a list, a dict, or a primitive type.
    """
    new_output = dict()
    for key, value in json_output.items():
        if key == "kb":
            new_output[key] = parse_kb(value)
        if key == "prob":
            new_output[key] = [ parse_langpro_json(v) for v in value ]
        elif key == "tree":
            new_output[key] = parse_langpro_json(value)
        elif key == "ccg_tree":
            new_output[key] = parse_ccg_tree(value)
        elif key in ["ccg_term", "corr_term", "llf"]:
            new_output[key] = parse_term(value)
        elif key == "proofs":
            pass
        else:
            new_output[key] = value
    return new_output

##############################################################
# Reading certain Prolog objects
##############################################################

def parse_t_leaf(tleaf):
    """parses terminal nodes of CCG derivations"""
    f, args = tleaf['functor'], tleaf["args"]
    if f != 't':
        raise ValueError(f"'t' functor is expected, found {f} from {tleaf}")
    # process ccg category, while rest are token, lemma, pos, chunking, ner info
    c = parse_caty(args[0])
    return TreeLeaf(f, [c] + args[1:])

def parse_caty(caty: str | dict):
    """parses types and categories"""
    # atomic type or cat (without features)
    if isinstance(caty, str):
        return AtomCaTy(caty)
    f, args = caty['functor'], caty["args"]
    # atomic type or cat with a feature
    if f == ":" and len(args) == 2:
        return AtomCaTy(f"{args[0]}:{args[1]}")
    return CompCaTy(f, [ parse_caty(arg) for arg in args])

def parse_kb(kb: list):
    """parses KB, which is a list of rleations over a pair of words"""
    return [ Compound(r['functor'], r['args']) for r in kb ]


##############################################################
# Reading certain Prolog tree objects as NLTK Tree
##############################################################

def parse_ccg_tree(tree: dict):
    """
    Structure a CCG derivation as an NLTK Tree.
    Combinatory rules with a resulting category are
    used as non-terminal labels.
    """
    f, args = tree['functor'], tree["args"]
    # combinator names used by C&C and EasyCCG
    unary_combinators = {'lx', 'lex', 'tr'}
    binary_combinators = {'fa', 'ba', 'fc', 'bc', 'fxc', 'bxc', 'conj',
                          'lp', 'rp', 'ltc', 'rtc', 'gbxc', 'gfxc'}
    # attach the resulted category to the rule name
    root = f"{f}({parse_caty(args[0])})" # combinator + TypeCat
    # process combinatory rules
    if f in unary_combinators:
        children = [parse_ccg_tree(args[-1])]
    elif f in binary_combinators:
        children = [parse_ccg_tree(ch) for ch in args[-2:]]
    # process leaves
    elif f == 't':
        return parse_t_leaf(tree)
    else:
        raise ValueError(f"Unknown combinatory rule: {f}")
    return Tree(root, children)


def parse_term(term: dict):
    """
    Structure a lambda term as an NLTK Tree.
    CatTypes are used as non-terminal labels.
    Here combinatory rules are not present as
    they are replaced with function application & abstraction.
    """
    if not isinstance(term, dict):
        raise ValueError(f"InvNon-dict term: {term}")
    if 'functor' not in term:
        raise ValueError(f"Invalid term: {term}")
    f, args = term['functor'], term["args"]
    # term-type pair
    if f == ',':
        return TT(term)
    # application of terms
    if f == '@':
        return AppTT(args[0], args[1])
    # lambda abstraction
    if f == 'abst':
        return AbsTT(args[0], args[1])
    # lexical term
    if f == 'tlp': # TODO: move this under TT?
        return TLP(f, args)

    # catching unforeseen cases
    raise ValueError(f"Unknown case: {term}")


def TT2Tree(t: TT|AppTT|AbsTT|Var) -> Any:
    """
    Structure a TT as an NLTK Tree.
    The root is the type, and the term is its child.
    """
    if isinstance(t, TT):
        if isinstance(t.term, AppTT):
            func = "@\n" 
        elif isinstance(t.term, AbsTT):
            func = "λ\n"
        else:
            func = ""
        pretty_type = remove_outer_parens(str(t.type))
        return Tree(f"{func}{pretty_type}", TT2Tree(t.term))
    if isinstance(t, AppTT):
        return [TT2Tree(t.fun), TT2Tree(t.arg)]
    if isinstance(t, AbsTT):
        return [TT2Tree(t.var), TT2Tree(t.body)]
    if isinstance(t, TLP):
        # parts = str(t)[1:-1].rsplit(',', 3)
        # return [parts[0] + '\n' + ','.join(parts[1:])]
        return [str(t)[1:-1]]
    if isinstance(t, Var):
        return [str(t)]
    
def compact_tt(t: TT|AppTT|AbsTT|Var) -> str:
    """Represent TT as a single line compact string."""
    if isinstance(t, Var):
        return str(t)
    if isinstance(t, TLP):
        return t.lem
    if isinstance(t, AbsTT):
        return f"(λ{compact_tt(t.var)}. {compact_tt(t.body)})"
    if isinstance(t, AppTT):
        return f"({compact_tt(t.fun)} @ {compact_tt(t.arg)})"
    if isinstance(t, TT):
        return f"{compact_tt(t.term)}"


def parse_info_proof(proof: dict):
    """
    Structure tableau proof as an NLTK Tree.
    Input can be actual proof dict, i.e., the value of "proof" key
    or dict with keys "info" and "proof".
    """
    # get actual proof dict
    p = proof["proof"] if "proof" in proof else proof
    proof_tree = parse_proof_tree(p)
    return proof_tree                               
                
def parse_proof_tree(dict_tree: dict):
    """Recursively parse proof tree"""
    # check that it is a tree
    if 'functor' not in dict_tree:
        print(f"Invalid proof tree: {dict_tree}")
        return None
    assert dict_tree['functor'] == 'tree', \
        f"Proof tree should have 'tree' as a functor but found: {dict_tree['functor']}"
    parent, children = dict_tree['args']
    assert parent['functor'] == 'trnd', \
        f"node should have 'trnd' as a functor but found: {parent['functor']}"
    # process children
    if isinstance(children, list):
        parsed_children = [ parse_proof_tree(child) for child in children ]
    elif isinstance(children, str):
        parsed_children = [children] # corresponds to the Model leaf
    elif isinstance(children, dict):
        #for closure rule
        if children['functor'] == 'closer':
            ids, rule = children['args'][0]
            parsed_children = [ f"Closed\n{rule}({ids})" ]
        else:
            ValueError(f"Unknown proof child type: {children}")
    else:
        raise ValueError(f"Unknown proof child type: {children}")
    return Tree(TreeNode(parent), parsed_children)


# TODO: This is only used for CCG trees for now. adapt it to terms or remove?
def tree_to_line(tree, op=False):
    """Represent NLTk Tree object as a single line string.
       This is useful to represent LLFs as a single line in proof trees
    """
    if isinstance(tree, str):
        n_cnt = tree.count("\n") # tyoe tok lemma pos ... tuple
        if n_cnt > 4:
            lemma = tree.split("\n")[2]
            return lemma
        elif n_cnt == 1: # type-var pair
            return  tree.split("\n")[-1]
        return tree
    if isinstance(tree, TreeLeaf):
        return tree.value # TODO: make more compact?
    if isinstance(tree, Tree) and "abst" in tree.label():
        var, body = tree
        return f"(\\{tree_to_line(var)}. {tree_to_line(body)})"
    # if isinstance(tree, TreeLeaf):
        # return tree.value # TODO: make more compact?
    # else:
    #     print(f">>> {type(tree)}: {tree}")
    # otherwise recurse
    if op:
        return f"({' '.join(tree_to_line(child, op=True) for child in tree)})"
    else:
        return f"{' '.join(tree_to_line(child, op=True) for child in tree)}"
    

def remove_outer_parens(s):
    if s.startswith('(') and s.endswith(')'):
        return s[1:-1]
    return s