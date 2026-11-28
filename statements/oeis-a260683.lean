import Mathlib

/-!
# A260683: Twos in the base-3 expansion of `2^n`.

Source: https://oeis.org/A260683

Name: Number of 2's in the expansion of `2^n` in base 3.

Conjecture (Paul Erdős): `a(n) > 0` for `n > 8`, i.e. the base-3
expansion of `2^n` contains at least one digit `2` whenever `n > 8`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

The OEIS table gives `a(0) = 0`, `a(2) = 0`, `a(8) = 0` and reports
positive values for all `9 <= n <= 10000` (Robert Israel's b-file).
We state the conjecture directly as the existence of a digit `2` in
`Nat.digits 3 (2^n)`.  The body stays `sorry`; a person reviews the
translation before merging.
-/

namespace OMA.S_oeis_a260683

/-- The number of 2's in the base-3 expansion of `2^n`. -/
def a260683 (n : ℕ) : ℕ := (Nat.digits 3 (2 ^ n)).count 2

theorem main :
    ∀ n : ℕ, 8 < n → 0 < a260683 n := by
  sorry

end OMA.S_oeis_a260683
