-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p12-contradiction/sets1contradiction.lean)

import Mathlib.Data.Set.Basic

-- Week 7 p10 first example - by contradiction

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- assume hypothesis
  intro h
  -- assume opposite of goal to derive a contradiction
  intro ha
  -- replace a with ∅ in hypothesis
  rw [ha] at h
  -- simplify ∅ ∩ b to ∅
  rw [Set.empty_inter] at h
  -- contradiction from ∅ ≠ ∅
  contradiction
