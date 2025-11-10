import Mathlib.Tactic

-- Week 7 p7 third example: product of integers both congruent to 2 mod 3 is congruent to 1 mod 3
-- Claude did it

example (k1 k2 : ℤ) :
  (∃ m : ℤ, k1 = 3 * m + 2) ∧
  (∃ n : ℤ, k2 = 3 * n + 2) →
  ∃ p : ℤ, k1 * k2 = 3 * p + 1 := by
  -- assume hypothesis
  intro h
  -- unpack conjunction
  obtain ⟨hk1, hk2⟩ := h
  -- unpack both congruences
  obtain ⟨m, hm⟩ := hk1
  obtain ⟨n, hn⟩ := hk2
  -- construct witness for product congruence
  use 3 * m * n + 2 * m + 2 * n + 1
  -- rewrite product using hk's
  rw [hm, hn]
  -- simplify using ring laws
  ring
