from __future__ import annotations

import sys
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set

import pytest
import z3
from z3.z3util import is_contradiction, is_expr_val, is_tautology

from . import deferred, logic, z3epipen

# ==========
# EpiPEn DSL
# ==========

# --------------
# Internal types
# --------------

@dataclass(frozen=True)
class CharacterRef:
    name: str

@dataclass
class CharacterState:
    known_constants: Set[z3.ExprRef] = field(default_factory=set)

    def copy(self) -> CharacterState:
        return CharacterState(
            known_constants=self.known_constants.copy()
        )

@dataclass
class KnowledgeState:
    common_knowledge: z3.BoolRef
    character_states: Dict[CharacterRef, CharacterState]

    def copy(self) -> KnowledgeState:
        return KnowledgeState(
            common_knowledge=self.common_knowledge,
            character_states={
                character: state.copy()
                for character, state in self.character_states.items()
            }
        )


# -----------------------------------
# Managing the global knowledge state
# -----------------------------------

# TODO: typing
_global_knowledge_state : KnowledgeState = None  # type: ignore

def start_story():
    global _global_knowledge_state
    _global_knowledge_state = KnowledgeState(common_knowledge=z3.BoolSort().cast(True), character_states={})

@contextmanager
def story():
    global _global_knowledge_state
    if _global_knowledge_state is not None:
        raise RuntimeError("no nesting `with story():`")
    start_story()
    try:
        yield
    finally:
        _global_knowledge_state = None

def _check_story():
    global _global_knowledge_state
    if _global_knowledge_state is None:
        raise RuntimeError("can't use this function outside of a story!")

def _set_knowledge_state(knowledge_state: KnowledgeState):
    _check_story()
    global _global_knowledge_state
    _global_knowledge_state = knowledge_state

def _get_knowledge_state_readonly():
    _check_story()
    global _global_knowledge_state
    return _global_knowledge_state

def _get_knowledge_state_copy():
    _check_story()
    global _global_knowledge_state
    return _global_knowledge_state.copy()

def current_state():
    # TODO: could be readonly, but this is safer
    return _get_knowledge_state_copy()

def current_common_knowledge():
    return _get_knowledge_state_readonly().common_knowledge

def _directly_request_knowledge_state_action(action: Callable[[KnowledgeState], None]):
    knowledge_state = _get_knowledge_state_copy()
    action(knowledge_state)
    _set_knowledge_state(knowledge_state)

_batched_simultaneous_actions: List[Callable[[KnowledgeState], None]] | None = None

@contextmanager
def simultaneous():
    global _batched_simultaneous_actions
    if _batched_simultaneous_actions is not None:
        raise RuntimeError("no nesting `simultaneous`")
    _batched_simultaneous_actions = []
    try:
        yield
    finally:
        for action in _batched_simultaneous_actions:
            _directly_request_knowledge_state_action(action)
        _batched_simultaneous_actions = None

def _request_knowledge_state_action(action: Callable[[KnowledgeState], None]):
    if _batched_simultaneous_actions is None:
        _directly_request_knowledge_state_action(action)
    else:
        _batched_simultaneous_actions.append(action)


# ----------------------------
# Characters & known constants
# ----------------------------

def Character(name: str) -> CharacterRef:
    character = CharacterRef(name=name)
    def action(knowledge_state: KnowledgeState):
        knowledge_state.character_states[character] = CharacterState()
    _request_knowledge_state_action(action)
    return character

def Characters(names_str: str):
    names = names_str.split(" ")
    return [Character(name) for name in names]

def learn_constant(character: CharacterRef, constant: z3.ExprRef):
    def action(knowledge_state: KnowledgeState):
        knowledge_state.character_states[character].known_constants.add(constant)
    _request_knowledge_state_action(action)

def learn_constants(character: CharacterRef, constants: List[z3.ExprRef]):
    for constant in constants:
        learn_constant(character, constant)

def test_learn_constant_outside_of_story():
    with pytest.raises(RuntimeError):
        learn_constant("dummy", "dummy")

def test_learn_constant():
    with story():
        alice = Character("Alice")
        num = z3.Int("num")
        old_state = current_state()
        learn_constant(alice, num)
        new_state = current_state()

        assert old_state.character_states[alice].known_constants == set()
        assert new_state.character_states[alice].known_constants == set([num])


# -------------------------
# Announcements & knowledge
# -------------------------

def know(knower: Optional[CharacterRef] = None, that: Optional[z3.BoolRef] = None, value_of: Optional[z3.ExprRef] = None) -> z3.BoolRef:
    if knower is None:
        return deferred.defer(z3.BoolSort(), lambda knower: know(knower, that=that, value_of=value_of))

    if that is not None and value_of is None:
        func = logic.determines_truth
        target = that
    elif value_of is not None and that is None:
        func = logic.determines_value
        target = value_of
    else:
        raise RuntimeError("must provide one of `that` and `value_of`")

    knowledge_state = _get_knowledge_state_readonly()
    known_constants = knowledge_state.character_states[knower].known_constants
    common_knowledge = knowledge_state.common_knowledge

    common_knowledge_constants = z3epipen.my_get_vars(common_knowledge)
    target_constants = z3epipen.my_get_vars(target)
    all_constants = common_knowledge_constants.union(target_constants)
    unknown_constants = list(all_constants.difference(known_constants))

    return func(common_knowledge, unknown_constants, target)

class Storyteller:
    pass

storyteller = Storyteller()

def announce(announcer: CharacterRef | Storyteller, statement: z3.BoolRef):
    if isinstance(announcer, Storyteller):
        if deferred.has_deferreds(statement):
            raise RuntimeError("storyteller doesn't 'know' things")
    else:
        statement = deferred.resolve_deferreds(statement, announcer)

    if isinstance(announcer, Storyteller):
        added_common_knowledge = statement
    else:
        if is_tautology(z3.Implies(statement, know(announcer, that=statement))):
            added_common_knowledge = statement
        else:
            added_common_knowledge = know(announcer, that=statement)

    def action(knowledge_state: KnowledgeState):
        knowledge_state.common_knowledge = z3.simplify(z3.And(
            knowledge_state.common_knowledge,
            z3epipen.quantifier_elimination(added_common_knowledge)))
    _request_knowledge_state_action(action)

def test_announce():
    with story():
        alice = Character("Alice")
        a, b, sum = z3.Ints("a b prod")
        announce(storyteller, a >= 0)
        announce(storyteller, b >= a)
        announce(storyteller, sum == a + b)
        learn_constant(alice, sum)
        announce(alice, know(value_of=b))

        common_knowledge = current_common_knowledge()
        assert not is_contradiction(z3.And(common_knowledge, sum == 1))
        assert is_contradiction(z3.And(common_knowledge, sum == 2))

def test_announce_simultaneous():
    # This one is fine
    with story():
        alice = Character("Alice")
        bob = Character("Bob")
        a = z3.Int("a")
        learn_constant(alice, a)
        with simultaneous():
            announce(alice, a == 3)
            announce(bob, z3.Not(know(value_of=a)))
        assert not is_contradiction(current_common_knowledge())

    # This one is contradictory
    with story():
        alice = Character("Alice")
        bob = Character("Bob")
        a = z3.Int("a")
        learn_constant(alice, a)
        announce(alice, a == 3)
        announce(bob, z3.Not(know(value_of=a)))
        assert is_contradiction(current_common_knowledge())


# ----
# Misc
# ----

def narrate(*args):
    print(*args)

# thin wrapper around z3 model
class World:
    model: z3.ModelRef

    def __init__(self, source: z3.ModelRef | Dict[z3.ExprRef, Any]):
        if isinstance(source, z3.ModelRef):
            self.model = source
        else:
            models, status = z3epipen.get_models(z3.And([constant == value for constant, value in source.items()]), 2)
            assert len(models) == 1
            assert status == z3.unsat
            self.model = models[0]

    def value_of(self, expr: z3.ExprRef):
        result = z3.simplify(z3epipen.quantifier_elimination(self.model.eval(expr)))
        if not is_expr_val(result):
            raise RuntimeError("world does not have enough information to determine value of expression")
        return result

def print_possible_worlds(max_worlds=10):
    knowledge_state = _get_knowledge_state_readonly()
    models, status = z3epipen.print_models(knowledge_state.common_knowledge,
                                       max_models=max_worlds, noun="possible world")

    if status == z3.unsat:
        # print("  simplifying common knowledge using finite set of possible worlds...")
        knowledge_state.common_knowledge = z3.Or([z3epipen.model_to_expr(model) for model in models])
        _set_knowledge_state(knowledge_state)

# TODO: make an optional version?
def check_finitely_many_possible_worlds(max_worlds=10, asserted=False):
    global _batched_simultaneous_actions
    if _batched_simultaneous_actions is not None:
        raise RuntimeError("can't check inside of `simultaneous`")

    knowledge_state = _get_knowledge_state_readonly()
    models, status = z3epipen.get_models(knowledge_state.common_knowledge, max_models=max_worlds)

    if status == z3.unsat:
        print(f"simplifying to {len(models)} worlds")
        knowledge_state.common_knowledge = z3.Or([z3epipen.model_to_expr(model) for model in models])
        _set_knowledge_state(knowledge_state)
    else:
        print(f"cannot simplify to finitely many worlds")
        if asserted:
            raise RuntimeError("could not find finite set of possible worlds")

def assert_finitely_many_possible_worlds(max_worlds=10):
    check_finitely_many_possible_worlds(max_worlds, asserted=True)

@contextmanager
def assert_adds_ck(e: z3.ExprRef):
    global _batched_simultaneous_actions
    if _batched_simultaneous_actions is not None:
        raise RuntimeError("can't use inside `simultaneous`; sorry")

    before = current_common_knowledge()
    yield
    after = current_common_knowledge()
    alt_after = z3.And(before, e)
    if not is_tautology(after == alt_after):
        raise RuntimeError("assertion failed! fix your added-common-knowledge")

    def action(knowledge_state: KnowledgeState):
        knowledge_state.common_knowledge = alt_after
    _request_knowledge_state_action(action)
