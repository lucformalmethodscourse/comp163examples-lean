import Mathlib.Tactic.Ring


-- TaiNing's slides week 7 page 14
-- Proofs by contrapositive

-- TODO first example

-- TODO second example

-- TODO third example


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
