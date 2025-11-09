import Mathlib.Tactic.Ring


-- TaiNing's slides week 7 page 12
-- Proofs by contradiction

example (x : ℕ) : Even (x ^ 2) → Even x := by
  -- assume antecedent
  intro hsq
  -- assume opposite of consequent to derive a contradiction
  by_contra hx
  -- remove negation
  rw [Nat.not_even_iff_odd] at hx
  -- unpack oddness
  rcases hx with ⟨j, hj⟩
  -- unpack evenness
  rcases hsq with ⟨k, hk⟩
  -- substitute
  rw [hj] at hk
  -- show that rhs is even (k + k form)
  have heven : Even (k + k) := by
    use k
  -- show that lhs is odd (2k + 1 form)
  have hodd : Odd ((2 * j + 1) ^ 2) := by
    use 2 * j * (j + 1)
    ring
  -- substitute
  rw [hk] at hodd
  -- reintroduce negation
  rw [← Nat.not_even_iff_odd] at hodd
  -- done
  contradiction

-- TODO second example

-- TODO third example
