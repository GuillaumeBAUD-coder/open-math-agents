import Mathlib

/-!
# OEIS A302920: p^2 = x^2 + 2y^2 + 3 * 2^z for every prime p

Source: https://oeis.org/A302920
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A302920(n) is the number of ways to write `prime(n)^2` as `x^2 + 2y^2 + 3 * 2^z` with `x, y, z`
nonnegative integers.

Conjecture: `a(n) > 0` for all `n > 0`. In other words, for any prime `p` there are nonnegative
integers `x`, `y` and `z` such that `x^2 + 2y^2 + 3 * 2^z = p^2`.

Formalization notes:
* Read from the OEIS entry itself: the term is `3 * 2^z` (some plain-text copies of the comment
  lose the multiplication sign and show `32^z`).
-/

namespace OMA.S_oeis_a302920

/-- Every prime square `p²` is `x² + 2y² + 3 * 2^z` with `x, y, z ≥ 0`. -/
theorem main :
    ∀ p : ℕ, p.Prime → ∃ x y z : ℕ, x ^ 2 + 2 * y ^ 2 + 3 * 2 ^ z = p ^ 2 := by
  sorry

end OMA.S_oeis_a302920
