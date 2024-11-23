from epipen import *
from z3 import *

start_story()
Anne, Bill, Cath = Characters('Anne Bill Cath')
A, B, C = Ints('A B C')
announce(storyteller, And(
		A > 0, B > 0, C > 0,
		Or(A == B + C, B == A + C, C == A + B)
))
learn_constants(Anne, [B, C])
learn_constants(Bill, [A, C])
learn_constants(Cath, [A, B])

with assert_adds_ck(Not(B == C)):
	announce(Anne, Not(know(value_of=A)))
announce(Bill, Not(know(value_of=B)))
announce(Cath, Not(know(value_of=C)))
announce(Anne, A == 50)

print_possible_worlds()