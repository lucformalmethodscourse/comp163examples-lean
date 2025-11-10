-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p12-contradiction/contradiction1.lean)

import Mathlib.Tactic.Ring

-- Week 7 p12 first example

example (x : ℕ) : Even (x ^ 2) → Even x := by
  -- assume hypothesis
  intro hsq
  -- assume opposite of goal to derive a contradiction
  by_contra hx
  -- remove negation
  rw [Nat.not_even_iff_odd] at hx
  -- unpack oddness
  obtain ⟨j, hj⟩ := hx
  -- unpack evenness
  obtain ⟨k, hk⟩ := hsq
  -- substitute
  rw [hj] at hk
  -- show that rhs is even (k + k form)
  have heven : Even (k + k) := by
    use k
  -- show that lhs is odd (2k + 1 form)
  have hodd : Odd ((2 * j + 1) ^ 2) := by
    use 2 * j * (j + 1)
    ring
  -- substitute
  rw [hk] at hodd
  -- reintroduce negation
  rw [← Nat.not_even_iff_odd] at hodd
  -- done
  contradiction
