import Mathlib.Tactic

-- basic sanity check

#check 2 + 2

-- simple example about even numbers

example (m n : ℕ) : Even n → Even (m * n) := by
  -- assume premise
  intro hn
  -- unpack evenness of n by obtaining witness k
  obtain ⟨k, hk⟩ := hn
  -- unpack evenness in conclusion by providing witness
  use m * k
  -- use hk to eliminate n in goal
  rw [hk]
  -- prove equality in goal using ring laws
  ring
