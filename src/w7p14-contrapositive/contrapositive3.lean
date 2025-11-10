-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p14-contrapositive/contrapositive3.lean)

import Mathlib.Tactic.Ring

-- Week 7 p14 third example: same as p10 first example

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- get rid of negations where possible
  push_neg
  -- introduce negation of original goal as hypothesis
  intro h
  -- rewrite goal based on a being empty
  rw [h]
  -- simplify intersection with empty set regardless of b
  rw [Set.empty_inter]
