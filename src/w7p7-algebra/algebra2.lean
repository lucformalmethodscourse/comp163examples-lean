import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

-- Week 7 p7 second example:
-- if x and y are rational, then x + y and x * y are also rational
-- Claude did most of it

example (a b c d : ℤ) (hb : b ≠ 0) (hd : d ≠ 0) :
  let x := (a : ℚ) / b
  let y := (c : ℚ) / d
  (∃ (p q : ℤ), q ≠ 0 ∧ x + y = p / q) ∧
  (∃ (r s : ℤ), s ≠ 0 ∧ x * y = r / s) := by
  constructor
  · -- x + y = (ad + bc) / (bd)
    -- provide witnesses for numerator and denominator
    use a * d + b * c, b * d
    -- prove denominator nonzero and equality with x + y
    constructor
    · exact mul_ne_zero hb hd
    · field_simp; ring
  · -- x * y = (ac) / (bd)
    -- provide witnesses for numerator and denominator
    use a * c, b * d
    -- prove denominator nonzero and equality with x * y
    constructor
    · exact mul_ne_zero hb hd
    · field_simp
