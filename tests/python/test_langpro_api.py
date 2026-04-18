"""
Tests for langpro_api.py, which contains functions
to parse the prolog json output of LangPro into python objects.
The test cases are based on 3 NLI problems, which are represented in
a more readable format in NLI_PROBLEMS, and also in the prolog json format
in data/nli_prob{0,1,2}.json files.
The expected values for the tests are in data/expected.json,
which are also based on the same 3 NLI problems.
"""
import pytest
import sys
import json
from pathlib import Path

# preparation for import
LANGPRO_PY = Path(__file__).resolve().parents[2] / "python"
# Check the availability of the api file
if not (LANGPRO_PY / 'langpro_api.py').is_file():
    raise RuntimeError(f"Couldn't find langpro_api.py in {LANGPRO_PY}")
sys.path.insert(0, str(LANGPRO_PY))

# importing langpro_api functions
from langpro_api import (parse_ccg_tree, parse_term, parse_proof_tree,
                         parse_info_proof, CaTy)

DATA_DIR = Path(__file__).parents[1] / "data"


####################################################
############# Sample NLI problems ##################
# more readable nli problems than json files
NLI_PROBLEMS = [
    {   'premises': [   "John runs"],
        'hypothesis':   "John moves"
    },
    {   'premises': [   "All animals sleep"],
        'hypothesis':   "Every dog sleeps"
    },
    {   'premises': [   "Every man is working",
                        "Everybody who is working has an expensive car"],
        'hypothesis':   "Every man owns a car"
    },
]

SENT_FOR_TESTS = [
      (0, "p"),
      (0, "h"),
      (1, "p"),
      (1, "h"),
      (2, "p0"),
      (2, "p1"),
      (2, "h"),
]

# read the content of nli_prob{0,1,2}.json files, which serves as input to tests
NLI_PROB_LP_JSON = {}
for i in range(3):
    with open(DATA_DIR / f"nli_prob{i}.json", encoding="utf-8") as F:
        out = json.load(F)
        # check consistency with NLI_PROBLEMS
        assert NLI_PROBLEMS[i]['premises'] == \
            [e["sen"] for e in out["prob"] if e["role"] == "p"]
        assert NLI_PROBLEMS[i]['hypothesis'] == \
            [e["sen"] for e in out["prob"] if e["role"] == "h"][0]
        NLI_PROB_LP_JSON[f"prob{i}"] = out

# read all the expected values
with open(DATA_DIR / "expected.json", encoding="utf-8") as F:
    EXPECTED = json.load(F)


####################################################
################### TESTS UTILS ####################
def parse_ph_k(ph_k):
    """ parse ph_k string like "pN" and "h" into ("p", N) and ("h", 0)
    """
    ph = ph_k[0]
    k = 0 if len(ph_k) == 1 else int(ph_k[1:])
    return ph, k

def get_json_expected_and_sen(prob_id, ph, k):
    """ input is the identifier to the NLI problem sentence:
        problem id, premise or hypothesis, and the sentence position.
        Returns sentence related annotations for both input and expected values
    """
    pid = f"prob{prob_id}"
    json_prob = NLI_PROB_LP_JSON[pid]["prob"]
    json_sen = [ s for s in json_prob if s["role"] == ph ][k]
    expected_sen = EXPECTED[pid][ph] if ph == "h" else EXPECTED[pid][ph][k]
    return json_sen, expected_sen

def get_by_path(data: dict, path: list):
    """ get a value from a dictionary based on the path of keys
    """
    current = data
    for step in path:
        current = current[step]
    return current


####################################################
###################### TESTS #######################


# 7 tests
@pytest.mark.parametrize("prob_id, ph_k", SENT_FOR_TESTS)
def test_parse_ccg_tree(prob_id, ph_k):
    """ tests parse_ccg_tree
        Input: ccg_tree in prolog json format
        Expected: repr string of the expected output nltk Tree.
    """
    ph, k = parse_ph_k(ph_k)
    json_sen, expected_sen = get_json_expected_and_sen(prob_id, ph, k)
    ccg_tree = parse_ccg_tree(json_sen["tree"]["ccg_tree"])
    expected_repr = expected_sen["repr_ccg_tree"]
    assert repr(ccg_tree) == expected_repr


# 21 tests
@pytest.mark.parametrize("prob_id, ph_k, term_type",
    [ (prob_id, ph_k, type_of_term)
      for type_of_term in ["ccg_term", "corr_term", "llf"]
        for prob_id, ph_k in SENT_FOR_TESTS ]
    )
def test_parse_term(prob_id, ph_k, term_type):
    """ tests parse_term
        Input: ccg_term/corr_term/llf are in prolog json format
        Expected: repr string of the expected output TT term object.
    """
    ph, k = parse_ph_k(ph_k)
    json_sen, expected_sen = get_json_expected_and_sen(prob_id, ph, k)
    term = parse_term(json_sen["tree"][term_type])
    expected_repr = expected_sen[f"repr_{term_type}"]
    assert repr(term) == expected_repr


# 10 tests
@pytest.mark.parametrize("prob_id, ph_k, path, expected",
    [ # ccg categories
      (0, "p", ["ccg_tree", "args", 0],             "s:dcl"),
      (0, "p", ["ccg_tree", "args", 1, "args", 0],  "np"),
      (0, "p", ["ccg_tree", "args", 2, "args", 0],  "s:dcl\\np"),
      (2, "p0", ["ccg_tree", "args", 2, "args", 1, "args", 0],
       "(s:dcl\\np)/(s:ng\\np)"),
      (2, "h", ["ccg_tree", "args", 2, "args", 1, "args", 0],
       "(s:dcl\\np)/np"),
      # types
      (0, "p", ["ccg_term", "args", 1],             "s:dcl"),
      (0, "p", ["ccg_term", "args", 0, "args", 1, "args", 1],  "np"),
      (0, "p", ["ccg_term", "args", 0, "args", 0, "args", 1],  "np-s:dcl"),
      (2, "p0", ["ccg_term", "args", 0, "args", 0, "args", 0, "args", 0, "args", 1],
       "(np-s:ng)-np-s:dcl"),
      (2, "h", ["ccg_term", "args", 0, "args", 0, "args", 0, "args", 0, "args", 1],
       "np-np-s:dcl"),
    ])
def test_compcaty_str(prob_id, ph_k, path, expected):
    """ Test the string representation of CompCaTy for cherry-picked examples.
    """
    ph, k = parse_ph_k(ph_k)
    json_sen, _ = get_json_expected_and_sen(prob_id, ph, k)
    json_caty = get_by_path(json_sen["tree"], path)
    caty = CaTy.parse(json_caty)
    assert str(caty) == expected


# 6 tests
@pytest.mark.parametrize("prob_id, label",
    [ (prob_id, label)
        for prob_id in range(3)
            for label in ["entailment", "contradiction"]
    ])
def test_parse_proof_tree(prob_id, label):
    """ tests parse_proof_tree for ent. and cont. poofs trees per problem
        Input: proof tree in prolog json format
        Expected: repr string of the expected output nltk Tree.
    """
    json_proof = NLI_PROB_LP_JSON[f"prob{prob_id}"]["proofs"][label]["proof"]
    proof_tree = parse_proof_tree(json_proof)
    expected_repr = EXPECTED[f"prob{prob_id}"][f"repr_{label}"]
    assert repr(proof_tree) == expected_repr


if __name__ == "__main__":
    # for debugging
    pass