from epipen import *
from z3 import *

n, k = 6, 3

start_story()

children = [Character(f"children[{i}]") for i in range(n)]
is_muddy = [Bool(f"is_muddy[{i}]") for i in range(n)]

actual_world = World({is_muddy[i]: i < k for i in range(n)})

# Each child sees which others are muddy
for i in range(n):
    for j in range(n):
        if i != j:
            learn_constant(children[i], is_muddy[j])

# Father: 'At least one of you is muddy'
announce(storyteller, Or([is_muddy[i] for i in range(n)]))
for step in range(1, 1000):
    print(f"Step {step}")
    # Father: 'If you know whether you are muddy, step forward'
    all_step_forward = True
    with simultaneous():
        for i in range(n):
            is_muddy_formula = know(children[i], value_of=is_muddy[i])
            is_actually_muddy = actual_world.value_of(is_muddy_formula)
            if is_actually_muddy:
                print(f"child {i} steps forward")
                announce(children[i], is_muddy_formula)
            else:
                announce(children[i], Not(is_muddy_formula))
                all_step_forward = False
    if all_step_forward:
        break

# > Step 1
# > Step 2
# > Step 3
# > child 0 steps forward
# > child 1 steps forward
# > child 2 steps forward
# > Step 4
# > child 0 steps forward
# > child 1 steps forward
# > child 2 steps forward
# > child 3 steps forward
# > child 4 steps forward
# > child 5 steps forward