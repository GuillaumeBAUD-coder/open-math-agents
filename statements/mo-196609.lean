import Mathlib

/-!
# Conjectures on perfect squares (Proposition 3)

Source: https://mathoverflow.net/questions/196609 (CC BY-SA 4.0).

For positive integers `a < b < c`, suppose each of
`ab - 1, bc - 1, ca - 1, ab - a - b + c, bc - b - c + a, ca - c - a + b` is a perfect square. Must each
of `ab + a + b - c, bc + b + c - a, ca + c + a - b` be a perfect square? Counterexamples exist with
`a = 1` (e.g. `(1, 5, 65)`); the asker marks Propositions 2 and 4 as true and asks about
Proposition 3: the implication holds whenever `2 ≤ a < b < c`.

We state Proposition 3.

Formalization notes:
* Work in `ℤ`; `IsSquare` on `ℤ` excludes negative numbers, matching "perfect square" (`0` counts).
* Checked by search over `2 ≤ a < 400`, `a < b < 4000`, `c ≤ 2·10^7`: 960 triples satisfy the
  hypotheses and all of them satisfy the conclusion.
-/

namespace OMA.S_mo_196609

/-- Proposition 3. -/
theorem main : ∀ a b c : ℤ, 2 ≤ a → a < b → b < c →
    IsSquare (a * b - 1) → IsSquare (b * c - 1) → IsSquare (c * a - 1) →
    IsSquare (a * b - a - b + c) → IsSquare (b * c - b - c + a) → IsSquare (c * a - c - a + b) →
    IsSquare (a * b + a + b - c) ∧ IsSquare (b * c + b + c - a) ∧ IsSquare (c * a + c + a - b) := by
  sorry

end OMA.S_mo_196609
