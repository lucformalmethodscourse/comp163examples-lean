import Mathlib.Data.Set.Basic

-- Week 7 p 10 third example

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
