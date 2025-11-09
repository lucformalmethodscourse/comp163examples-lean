import Mathlib.Data.Set.Basic

-- TaiNing's slides week 7 page 10
-- Direct set-theoretic proofs


-- by contradiction because KL didn't know any better

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- assume hypothesis
  intro h
  -- assume opposite of goal to derive a contradiction
  intro ha
  -- replace a with ∅ in hypothesis
  rw [ha] at h
  -- simplify ∅ ∩ b to ∅
  rw [Set.empty_inter] at h
  -- contradiction from ∅ ≠ ∅
  contradiction

-- YHOO redo as direct proof

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- assume hypothesis
  intro h
  -- rewrite inequality as predicate in hypothesis
  rw [← Set.nonempty_iff_ne_empty] at h
  -- rewrite inequality as predicate in goal
  rw [← Set.nonempty_iff_ne_empty]
  -- obtain a witness x from nonempty intersection
  obtain ⟨x, hx⟩ := h
  -- x is in the intersection, so x is in a (and in b)
  -- can use _ to ignore warning about unused hxb
  have ⟨hxa, hxb⟩ := hx
  -- apply definition of nonemptiness using x as witness
  exact ⟨x, hxa⟩


-- by contradiction because KL didn't know any better

example (a b : Set α) : a \ b ≠ ∅ → ¬(a ⊆ b) := by
  -- assume hypothesis
  intro h
  -- assume opposite of goal to derive a contradiction
  intro hab
  -- rewrite h as negation
  simp at h
  -- rewrite h based on empty difference between set and superset
  rw [Set.diff_eq_empty.mpr hab] at h -- FIXME eliminate mpr
  -- contradiction from ∅ ≠ ∅
  contradiction

-- YHOO also redo as direct proof? Claude mostly did it.

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


example (x y z : Set α) : x ⊆ y → x ∪ z ⊆ y ∪ z := by
  -- assume hypothesis
  intro hxy
  -- assume element in union
  intro a ha
  -- rewrite union membership as or
  simp at ha
  -- case distinction on which set the element is in
  cases ha with
  -- element is in x
  | inl ha₁ =>
    -- simplify goal to left side of union
    left
    -- use subset property in goal
    apply hxy
    exact ha₁ -- use literally
  -- element is in z
  | inr ha₂ =>
    -- simplify goal to right side of union
    right
    exact ha₂ -- use literally
