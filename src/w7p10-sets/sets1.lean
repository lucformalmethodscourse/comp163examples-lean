import Mathlib.Data.Set.Basic

-- Week 7 p 10 first example - direct proof

example (a b : Set α) : a ∩ b ≠ ∅ → a ≠ ∅:= by
  -- assume hypothesis
  intro h
  -- rewrite inequality as predicate in hypothesis and goal
  rw [← Set.nonempty_iff_ne_empty] at *
  -- obtain a witness x from nonempty intersection
  obtain ⟨x, hx⟩ := h
  -- x is in the intersection, so x is in a (and in b)
  -- can use _ to ignore warning about unused hxb
  have ⟨hxa, hxb⟩ := hx
  -- apply definition of nonemptiness using x as witness
  exact ⟨x, hxa⟩
