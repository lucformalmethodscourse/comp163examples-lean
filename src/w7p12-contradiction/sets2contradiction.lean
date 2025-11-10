import Mathlib.Data.Set.Basic

-- Week 7 p10 second example - by contradiction

example (a b : Set α) : a \ b ≠ ∅ → ¬(a ⊆ b) := by
  -- assume premise
  intro h
  -- assume opposite of conclusion to derive a contradiction
  intro hab
  -- rewrite h as negation
  simp at h
  -- rewrite h based on empty difference between subset and superset
  rw [← Set.diff_eq_empty] at hab
  -- contradiction from ∅ ≠ ∅
  contradiction
