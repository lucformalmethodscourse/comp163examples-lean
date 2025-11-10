-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/basic/basic2.lean)

import Mathlib.Data.Real.Basic

-- a couple of very simple examples

example (a b : ℝ) : min a b = min b a := by
  -- case distinction on a or b being smaller
  by_cases h : a ≤ b
  -- h : a ≤ b
  · rw [min_eq_left h] -- min a b = a
    rw [min_eq_right h] -- min b a = a
  -- h : ¬ (a ≤ b)
  · push_neg at h -- b < a instead of not (a ≤ b)
    rw [min_eq_right (le_of_lt h)] -- min a b = b
    rw [min_eq_left (le_of_lt h)] -- min b a = b

example (a b : ℝ) : max a b = max b a := by
  rw [max_comm] -- built-in commutativity of max
