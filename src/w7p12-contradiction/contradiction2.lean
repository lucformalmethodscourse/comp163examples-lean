-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p12-contradiction/contradiction2.lean)

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

-- Week 7 p12 second example

example (a : ℝ) : a ^ 2 ≥ 7 * a → a ≤ 0 ∨ a ≥ 7 := by
  -- assume hypothesis
  intro h
  -- assume opposite of goal to derive a contradiction
  by_contra hcon
  -- push negation inside
  push_neg at hcon
  -- now we can simply use this one tactic and we're done:
  -- nlinarith
  -- (this needs import Mathlib.Tactic.Nlinarith)
  -- OR step-by-step (a bit tedious)
  obtain ⟨ha, hb⟩ := hcon
  -- rewrite square as multiplication
  rw [sq] at h
  -- cancel right multiplication by a
  have hc : a ≥ 7 := le_of_mul_le_mul_right h ha
  -- flip inequality
  rw [ge_iff_le] at hc
  -- rewrite as negation
  rw [← not_lt] at hc
  contradiction
