import Mathlib.Tactic

-- Week 7 p7 first example: product of even integers is even
-- Claude did part of it

example (m n : ℤ) : Even m ∧ Even n → Even (m * n) := by
  -- assume premise
  intro h
  -- unpack conjunction
  obtain ⟨hm, _⟩ := h -- we only need one side of the conjunction
  -- unpack evenness of m by obtaining witness l
  obtain ⟨l, hl⟩ := hm
  -- unpack evenness in conclusion by providing witness
  use l * n
  -- use hl to eliminate m in goal
  rw [hl]
  -- prove equality in goal using ring laws
  ring
