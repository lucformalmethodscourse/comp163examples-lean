import Mathlib.Data.Set.Basic

-- Week 7 p 10 second example - direct proof

example (a b : Set α) : a \ b ≠ ∅ → ¬(a ⊆ b) := by
  -- assume hypothesis
  intro h
  -- rewrite inequality as predicate in hypothesis
  rw [← Set.nonempty_iff_ne_empty] at h
  -- obtain witness x from nonempty difference
  obtain ⟨x, hx⟩ := h
  -- x is in a \ b, so x is in a and not in b
  have ⟨hxa, hxb⟩ := hx
  -- rewrite goal as existence of counterexample
  rw [Set.not_subset]
  -- provide x as that counterexample (witness)
  exact ⟨x, hxa, hxb⟩
