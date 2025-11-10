-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p14-contrapositive/contrapositive1.lean)

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Irrational

-- Week 7 p14 first example: if x ^ 2 is irrational, then x is irrational
-- TODO/deferred because of irrationality stuff

example (x : ℝ) : Irrational (x ^ 2) → Irrational x := by
  sorry
