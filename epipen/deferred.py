import z3
from typing import Any, Callable, Dict

from . import z3epipen

# =========================
# Deferred expression nodes
# =========================

# TODO: this might actually be kinda slow. (up to 0.2 sec.) booooo.

_global_deferred_thunks: Dict[z3.ExprRef, Callable[[Any], Any]] = {}

def defer(sort: z3.Sort, thunk: Callable[[Any], Any]):
    placeholder = z3.FreshConst(sort)
    global _global_deferred_thunks
    _global_deferred_thunks[placeholder] = thunk
    return placeholder

def has_deferreds(expr) -> bool:
    for var in z3epipen.my_get_vars(expr):
        if var in _global_deferred_thunks:
            return True
    return False

def resolve_deferreds(expr, ctx):
    for var in z3epipen.my_get_vars(expr):
        if var in _global_deferred_thunks:
            thunk = _global_deferred_thunks[var]
            resolved = resolve_deferreds(thunk(ctx), ctx)
            expr = z3.substitute(expr, (var, resolved))
            del _global_deferred_thunks[var]
    return expr

def test_defer():
    expr_with_defers = 2 + defer(z3.IntSort(), lambda ctx:
        ctx + defer(z3.IntSort(), lambda ctx:
            z3.IntSort().cast(ctx)))
    assert z3.simplify(resolve_deferreds(expr_with_defers, 100)) == 202
    assert len(_global_deferred_thunks) == 0
