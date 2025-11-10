import Mathlib.Tactic

-- Week 7 p14 second example: if x ^ 2 - 4 * x + 3 is even, then x is odd

example (x : ℕ) : Even (x ^ 2 - 4 * x + 3) → Odd x := by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- introduce negation of original conclusion as premise
  intro hx
  -- rewrite hx without negation
  rw [Nat.not_odd_iff_even] at hx
  -- unpack evenness of x
  obtain ⟨k, hk⟩ := hx
  -- rewrite conclusion without negation
  rw [Nat.not_even_iff_odd]
  -- rewrite x in terms of k
  rw [hk]
  -- construct witness for oddness of conclusion
  use 2 * k ^ 2 - 4 * k + 1
  -- simplify using ring laws
  ring_nf
  -- deal with remaining arithmetic
  omega
