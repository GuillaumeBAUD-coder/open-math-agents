import Mathlib

/-!
# Is `16a+5` always of the form `x^2+y^2+z^4`?

Source: https://mathoverflow.net/questions/446506 (2023).
Credit: @jagraj28

The post asks, over the integers, whether `16a + 5` is always of the form `x ^ 2 + y ^ 2 + z ^ 4`.
It reports the claim for `a ≤ 10 ^ 7`; comments extend the check to `10 ^ 8` and beyond
`1.2 · 10 ^ 9`. The post has no answer.

Formalization notes:
* `a` ranges over the natural numbers: for negative `a` the number `16a + 5` is negative and is
  not a sum of squares and a fourth power.
* `x, y, z` are integers in the post; only their absolute values matter, so they are taken in
  `ℕ`.
* `main` states the affirmative answer. A direct search confirms it for every `a < 10 ^ 6`.
-/

namespace OMA.S_mo_446506

/-- Every `16a + 5` is `x ^ 2 + y ^ 2 + z ^ 4`. -/
theorem main : ∀ a : ℕ, ∃ x y z : ℕ, 16 * a + 5 = x ^ 2 + y ^ 2 + z ^ 4 := by
  sorry

end OMA.S_mo_446506
