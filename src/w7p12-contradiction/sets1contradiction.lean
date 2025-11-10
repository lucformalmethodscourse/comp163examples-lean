import Mathlib.Data.Set.Basic

-- Week 7 p10 first example - by contradiction

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- assume premise
  intro h
  -- assume opposite of conclusion to derive a contradiction
  intro ha
  -- replace a with ∅ in premise
  rw [ha] at h
  -- simplify ∅ ∩ b to ∅
  rw [Set.empty_inter] at h
  -- contradiction from ∅ ≠ ∅
  contradiction
