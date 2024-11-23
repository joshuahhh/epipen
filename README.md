# EpiPEn: Epistemic Programming Environment

EpiPEn is a Python library for expressing and solving epistemic puzzles – puzzles that require reasoning about knowledge and ignorance. For example, take this puzzle:


> Anne and Bill are told the following: “I have two natural numbers. They are consecutive numbers. I am going to whisper one of these numbers to Anne and the other number to Bill.” This happens. Anne and Bill then have the following conversation:
>
> - Anne: “I don’t know your number.”
> - Bill: “I don’t know your number.”
> - Anne: “I know your number.”
> - Bill: “I know your number.”
>
> How is this possible? What are their numbers?

With EpiPEn, you can express and solve this puzzle like this:

```python
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

announce(Anne, Not(know(value_of=B)))
announce(Bill, Not(know(value_of=A)))
announce(Anne, know(value_of=B))
announce(Bill, know(value_of=A))

print_possible_worlds()
```
Pulling this off requires a novel encoding of epistemic logic in first-order logic and some embedded-DSL shenanigans. Pretty neat!

EpiPEn was a project for [CSE 507](https://courses.cs.washington.edu/courses/cse507/21au/), executed by Josh Horowitz and Jack Zhang. See https://joshuahhh.com/epipen/ for a paper & slides.

## Running examples

1. Clone the repository & navigate into it
2. Create a virtual environment:
    ```sh
    python -m venv venv
    ```
3. Activate the virtual environment:
    ```sh
    source venv/bin/activate
    ```
    This will differ for non-standard shells. E.g. for fish, you run `. venv/bin/activate.fish`.
4. Install dependencies (into the virtual environment):
    ```sh
    pip install -r requirements.txt
    ```
5. Run an example:
    ```sh
    PYTHONPATH=. python examples/cheryls-birthday.py
