-- Try this example in Lean 4 Web: https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/basic/basic1.lean

import Mathlib.Tactic.Ring

-- basic sanity check

#check 2 + 2

-- simple example about even numbers

example (m n : ℕ) : Even n → Even (m * n) := by
  -- assume hypothesis
  intro hn
  -- unpack evenness of n by obtaining witness k
  obtain ⟨k, hk⟩ := hn
  -- unpack evenness in goal by providing witness
  use m * k
  -- use hk to eliminate n in goal
  rw [hk]
  -- prove equality in goal using ring laws
  ring
