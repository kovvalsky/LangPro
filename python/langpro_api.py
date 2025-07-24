"""
langpro_api.py

Defines Classes and functions for reading and processing
LangPro output such as CCG trees, CCG terms, LLFs, 
Tableau proofs, and knowledge relations.
"""

import json
from typing import Any, List, Dict
import nltk
from collections import defaultdict, Counter
from nltk import Tree

##############################################################
# Classes
##############################################################

INFIX_F = {':', '~>', '@', ',', '/', '\\'}
TYPECAT_F = {'/', '\\', ':', '~>'}

# Base class for all Prolog term types
class PrologTerm:
    """A base class for representing Prolog terms."""
    def __repr__(self):
        return self.__str__()

    def __str__(self) -> str:
        raise NotImplementedError("Subclasses must implement __str__")

# Represents a Prolog atom
class Atom(PrologTerm):
    def __init__(self, value: str):
        self.value = value

    def __str__(self) -> str:
        return f"{self.value}"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Atom) and self.value == other.value

# Represents a Prolog variable
class Var(PrologTerm):
    def __init__(self, value: str):
        self.value = value

    def __str__(self) -> str:
        return self.value

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Var) and self.value == other.value

# Represents a Prolog integer
class Integer(PrologTerm):
    def __init__(self, value: int):
        self.value = value

    def __str__(self) -> str:
        return str(self.value)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Integer) and self.value == other.value

# Represents a Prolog float
class Float(PrologTerm):
    def __init__(self, value: float):
        self.value = value

    def __str__(self) -> str:
        return str(self.value)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Float) and self.value == other.value

# Represents a Prolog compound term (e.g., father(john, X))
class Compound(PrologTerm):
    def __init__(self, f: str, args: List[Any]):
        self.f = f
        self.args = args
        self.nargs = len(args)

    def __str__(self) -> str:
        if self.f in INFIX_F:
            assert len(self.args) == 2, f"Arg num != 2: {self.args}"
            ws = ' ' if  self.f == ',' else ''
            return f"({str(self.args[0])}{ws}{self.f}{ws}{str(self.args[1])})"
        else:
            return f"{self.f}({', '.join(str(arg) for arg in self.args)})"

    def __eq__(self, other: object) -> bool:
        return (
            isinstance(other, Compound) and
            self.f == other.f and
            self.args == other.args
        )

    def __len__(self) -> int:
        return len(str(self))

class TypeCat(Compound):
    def __init__(self, f: str, args: List[Any]):
        if f not in TYPECAT_F:
            raise ValueError(f"Category/Type Compound uses a wrong functor: {f}")
        super().__init__(f, args)

class TLP(Compound):
    def __init__(self, f: str, args: List[Any]):
        if f not in {'tlp'}:
            raise ValueError(f"TLP Compound uses a wrong functor: {f}")
        super().__init__(f, args)

class Terminal(Compound):
    def __init__(self, f: str, args: List[Any]):
        if f not in {'t'}:
            raise ValueError(f"Terminal Compound uses a wrong functor: {f}")
        super().__init__(f, args)

##############################################################
# Reading jSON data
##############################################################

COMPOUND_TYPE_MAP = {"tlp": TLP, "t": Terminal, **{key: TypeCat for key in TYPECAT_F}}

def from_json(data: Any, v=0) -> Any:
    """
    Recursively converts a Python dictionary/list (from JSON) into PrologTerm objects.
    Args:
        data: The input data, typically a dict, list, or primitive.
    Returns:
        A PrologTerm object, a list, a dict, or a primitive type.
    """
    # Case 1: A dictionary representing a tagged Prolog term or a JSON object
    if isinstance(data, dict):
        if 'functor' in data and 'args' in data:
            if v: 
                print('functor/args')
            # Recursively parse the arguments    
            args = [from_json(arg, v=v) for arg in data["args"]]
            compound_class = COMPOUND_TYPE_MAP.get(data['functor'], Compound)
            return compound_class(data["functor"], args)
        else:
            # It's a regular JSON object (Prolog dict)
            # Recursively parse the dictionary's values
            if v: 
                print(f'dict({len(data)})')
            return {key: from_json(value, v=v) for key, value in data.items() \
                    # if key not in ['kb', 'prob', 'prob_id', 'info']
                    }

    # Case 2: A list (Prolog list)
    elif isinstance(data, list):
        if v: 
            print('list')
        # Recursively parse each item in the list
        return [from_json(item, v=v) for item in data]
    
    # Case 3: booleans
    elif data in ['true', 'false']:
        if v: 
            print('true/false')
        return True if data == 'true' else False

    # Case 4: integer
    elif isinstance(data, int):
        if v: 
            print('integer')
        return Integer(data)
    
    # Case 5: float
    elif isinstance(data, float):
        if v: 
            print('float')
        return Float(data)

    # Case 5: float
    elif data == '_':
        if v: 
            print('_')
        return Var(data)

    # Case 5: float
    elif isinstance(data, str):
        if v: 
            print('data')
        return Atom(data)
    
    # Else: A primitive value (already handled inside dicts/lists)
    else:
        raise ValueError(f"Unsupported type: {type(data)}(value={data})")

##############################################################
# Reading certain Prolog tree objects as NLTK Tree
##############################################################

def ccg_tree_to_tree(tree):
    """process the ccg rules based on the arity of the combinatory rules"""
    inseperables = TYPECAT_F | {'t', 'tlp'}
    unary_combinators = {'lx', 'lex', 'tr'}
    binary_combinators = {'fa', 'ba', 'fc', 'bc', 'fxc', 'bxc', 'conj', 
                          'lp', 'rp', 'ltc', 'rtc', 'gbxc', 'gfxc'}
   
    # attach the resulted category to the rule name
    root = f"{tree.f}({tree.args[0]})"
    # process combinatory rules
    if tree.f in unary_combinators:
        children = [ccg_tree_to_tree(tree.args[-1])]
    elif tree.f in binary_combinators:
        children = [ccg_tree_to_tree(ch) for ch in tree.args[-2:]]
    # process leaves
    elif isinstance(tree, Terminal):
        return tree
    else:
        raise ValueError(f"Unknown combinatory rule: {tree.f}")
    return Tree(root, children)