import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Defs

-- Week 7 p12 third example
-- TODO/deferred - tricky because of irrationality stuff

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
