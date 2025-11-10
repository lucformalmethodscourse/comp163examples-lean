-- Try this example in [Lean 4 Web](https://live.lean-lang.org/#url=https://raw.githubusercontent.com/lucformalmethodscourse/comp163examples-lean/refs/heads/main/src/w7p14-contrapositive/contrapositive4.lean)

import Mathlib.Tactic.Ring

-- Week 7 p14 fourth example

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
