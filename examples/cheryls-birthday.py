from z3 import *
from epipen import *

start_story()
Albert, Bernard = Characters('Albert Bernard')
month, day = Ints('month day')

announce(storyteller,
    Or([
        And(month == m, day == d) for (m, d) in
        [(5, 15), (5, 16), (5, 19), (6, 17), (6, 18),
         (7, 14), (7, 16), (8, 14), (8, 15), (8, 17)]
    ])
)
learn_constant(Albert, month)
learn_constant(Bernard, day)

# Albert: I don't know when your birthday is...
announce(Albert, Not(know(value_of=day)))
# Albert: I know Bernard doesn't know either
announce(Albert, Not(know(Bernard, value_of=month)))
# Bernard: At first I didn't know when C's birthday is, but I know now.
announce(Bernard, know(value_of=month))
# Albert: Then I also know when Cheryl's birthday is.
announce(Albert, know(value_of=day))

print_possible_worlds()
# > printing up to 10 possible world(s)
# >   [day = 16, month = 7]
# >   (and that's all)