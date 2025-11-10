-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p14-contrapositive/contrapositive2.lean)

import Mathlib.Tactic.Ring

-- Week 7 p14 second example: if x ^ 2 - 4 * x + 3 is even, then x is odd

example (x : ℕ) : Even (x ^ 2 - 4 * x + 3) → Odd x := by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- introduce negation of original goal as hypothesis
  intro hx
  -- rewrite hx without negation
  rw [Nat.not_odd_iff_even] at hx
  -- unpack evenness of x
  obtain ⟨k, hk⟩ := hx
  -- rewrite goal without negation
  rw [Nat.not_even_iff_odd]
  -- rewrite x in terms of k
  rw [hk]
  -- construct witness for oddness of goal
  use 2 * k ^ 2 - 4 * k + 1
  -- simplify using ring laws
  ring_nf
  -- deal with remaining arithmetic
  omega
