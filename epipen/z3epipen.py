import sys
from typing import Dict, FrozenSet

import pytest
import z3
from z3.z3util import is_const, is_expr_var

# ============
# Z3 utilities
# ============

if __name__ == "__main__":
    sys.exit(pytest.main([sys.argv[0], "-rP"]))


# The version in z3.z3util is extremely slow. This one's much faster, for a few reasons.
# (Including a cache.)

def my_get_vars(f: z3.ExprRef) -> FrozenSet[z3.ExprRef]:
    if f in _global_constants_in_expressions:
        return _global_constants_in_expressions[f]

    result = set()

    if is_const(f):
        if is_expr_var(f):
            result.add(f)
    else:
        for f_ in f.children():
            result.update(my_get_vars(f_))

    frozen_result = frozenset(result)

    _global_constants_in_expressions[f] = frozen_result

    return frozen_result


_global_constants_in_expressions: Dict[z3.ExprRef,
                                       FrozenSet[z3.ExprRef]] = dict()


def test_my_get_vars():
    a, b, c = z3.Ints("a b c")
    assert my_get_vars(a + c >= 0) == frozenset([a, c])


def model_to_expr(model):
    return z3.And([sym() == model[sym] for sym in model.decls()])


def get_models(e, max_models=10):
    """
    Returns the first `max_models` models satisfiying `e`, together with a "more
    results?" status indicator.

    If the indicator is `unsat`, there are no models beyond those returned.

    If the indicator is `sat`, there must be models beyond those returned.

    If the indicator is `unknown`, there may or may not be models beyond those
    returned.
    """
    result = []

    s = z3.Solver()
    s.add(e)
    while s.check() == z3.sat and len(result) < max_models:
        model = s.model()
        result.append(model)
        s.add(z3.Not(model_to_expr(model)))

    return result, s.check()

def test_get_models():
    a = z3.Int('a')

    models, status = get_models(z3.And(0 <= a, a <= 1))
    assert len(models) == 2
    assert status == z3.unsat

    models, status = get_models(z3.And(0 <= a), max_models=20)
    assert len(models) == 20
    assert status == z3.sat

def print_models(e, max_models=10, noun="model"):
    models, status = get_models(e, max_models)
    print(f"printing up to {max_models} {noun}(s)")
    for model in models:
        print(" ", model)
    if len(models) == 0:
        print("  none found!")
    if status == z3.sat:
        print("  (there are more)")
    if status == z3.unsat:
        print("  (and that's all)")
    if status == z3.unknown:
        print("  (might be more, but the solver doesn't know)")
    return models, status


def quantifier_elimination(e):
    return z3.Tactic('qe').apply(e).as_expr()
