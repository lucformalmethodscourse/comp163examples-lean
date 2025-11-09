import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


-- TaiNing's slides week 7 page 12
-- Proofs by contradiction

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

-- YHOO second example

example (a : ℝ) : a ^ 2 ≥ 7 * a → a ≤ 0 ∨ a ≥ 7 := by
  -- assume hypothesis
  intro h
  -- assume opposite of goal to derive a contradiction
  by_contra hcon
  -- push negation inside
  push_neg at hcon
  -- now we can simply use this one tactic and we're done:
  -- nlinarith
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


-- TODO third example: tricky because of irrationality stuff

example (x : ℝ) : Irrational x ∧ x ≥ 0 → Irrational (√x) := by
  -- assume hypothesis
  intro h
  -- apply definition of irrationality
  unfold Irrational
  -- assume opposite of goal to derive a contradiction
  by_contra hsq
  -- unpack rationality of √x
  obtain ⟨p, q⟩ := hsq
  -- construct rational representation of x
  -- use (p * p) / (q * q)
  -- break up conjunction in hypothesis
  obtain ⟨hirr, hpos⟩ := h
  sorry
