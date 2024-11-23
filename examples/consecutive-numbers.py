from epipen import *
from z3 import *

start_story()
Anne, Bill = Characters('Anne Bill')
A, B = Ints('A B')

announce(storyteller,
    And(A >= 0, B >= 0,
        Or(A == B + 1, B == A + 1)))
learn_constant(Anne, A)
learn_constant(Bill, B)

# A: 'I don't know your number.'
announce(Anne, Not(know(value_of=B)))
# B: 'I don't know your number.'
announce(Bill, Not(know(value_of=A)))
# A: 'I know your number.'
announce(Anne, know(value_of=B))
# B: 'I know your number.'
announce(Bill, know(value_of=A))

print_possible_worlds()
# > printing up to 10 possible world(s)
# >   [A = 2, B = 3]
# >   [A = 1, B = 2]
# >   (and that's all)
