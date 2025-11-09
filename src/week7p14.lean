import Mathlib.Tactic.Ring


-- TaiNing's slides week 7 page 14
-- Proofs by contrapositive

-- TODO first example: if x ^ 2 is irrational, then x is irrational


-- TODO second example: if x ^ 2 - 4 * x + 3 is even, then x is odd

example (x : ℕ) : Even (x ^ 2 - 4 * x + 3) → Odd x := by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- introduce negation of original goal as hypothesis
  intro hx
  -- rewrite hx without negation
  rw [Nat.not_odd_iff_even] at hx
  -- unpack evenness of x
  obtain ⟨k, hk⟩ := hx
  -- rewrite goal without negation
  rw [Nat.not_even_iff_odd]
  -- rewrite x in terms of k
  rw [hk]
  repeat ring_nf!
  -- construct witness for oddness of goal
  -- 4 * k ^ 2 - 8 * k + 3 = 2 * (2 * k ^ 2 - 4 * k + 1) + 1
  use 2 * k ^ 2 - 4 * k + 1
  repeat ring_nf!
  sorry


-- YHOO third example: same as p10 first example

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- get rid of negations where possible
  push_neg
  -- introduce negation of original goal as hypothesis
  intro h
  -- rewrite goal based on a being empty
  rw [h]
  -- simplify intersection with empty set regardless of b
  rw [Set.empty_inter]


-- DONE fourth example

example (n a b : ℕ) : ¬ n ∣ a * b → ¬ n ∣ a ∨ ¬ n ∣ b := by
  -- prove by contrapositive (negation of implication)
  contrapose
  -- simplify by pushing negation inside
  push_neg
  -- assume both divisibilities
  intro ⟨ha, hb⟩
  -- unpack both divisibilities
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  -- construct witness for divisibility of product
  use n * ka * kb
  -- rewrite product using hk's
  rw [hka, hkb]
  -- simplify using ring laws
  ring_nf
