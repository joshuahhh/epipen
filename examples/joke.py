# from https://twitter.com/maanow/status/1706789746033258628:

# Three logicians walk into a bar.
# The bartender asks: 'Does everyone want a drink?'
# The first logician says: 'I don't know.'
# The second logician says: 'I don't know.'
# The third logician says: 'Yes.'

from z3 import *
from epipen import *

start_story()
L1, L2, L3 = Characters('L1 L2 L3')
L1_thirsty, L2_thirsty, L3_thirsty = Bools('L1_thirsty L2_thirsty L3_thirsty')

learn_constant(L1, L1_thirsty)
learn_constant(L2, L2_thirsty)
learn_constant(L3, L3_thirsty)

all_thirsty = And(L1_thirsty, L2_thirsty, L3_thirsty)

announce(L1, Not(know(value_of=all_thirsty)))
announce(L2, Not(know(value_of=all_thirsty)))
announce(L3, all_thirsty)

print_possible_worlds()

# printing up to 10 possible world(s)
#   [L3_thirsty = True,
#  L2_thirsty = True,
#  L1_thirsty = True]
#   (and that's all)
