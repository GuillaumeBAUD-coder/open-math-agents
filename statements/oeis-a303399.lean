import Mathlib

/-!
# A303399: Number of ordered pairs (a, b) with 0 <= a <= b such that n - 5^a - 5^b can be written as the sum of two triangular numbers.

Source: https://oeis.org/A303399
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, April 2018, in the comments of A303399): `a(n) > 0` for all `n > 1`.

Formalization notes:
* The sequence has offset `1`; `a 0` is not part of the sequence and plays no role in the
  statement (which only concerns `n > 1`).
* To avoid shadowing the sequence name `a`, the exponents `(a, b)` of the OEIS name are called
  `(x, y)`; the count is over pairs `(x, y)` with `x ≤ y`, not over representations.
* Triangular numbers are `T(i) = i * (i + 1) / 2` with `i ≥ 0`, so `T(0) = 0` is allowed and a
  remainder `n - 5^x - 5^y = 0` counts (it is `T(0) + T(0)`), as in the OEIS example for `a(6)`.
* `5 ^ x + 5 ^ y ≤ n` is required explicitly, so truncated subtraction in `ℕ` plays no role.
* The bounds are lossless: `5 ^ x ≤ n` and `x < 5 ^ x` give `x ≤ n` (likewise `y`), and
  `T(i) ≥ i` with `T(i) ≤ n - 5^x - 5^y ≤ n` gives `i ≤ n` (likewise `j`).
* Initial values for `n = 1, ..., 20`:
  `a(n) = 0, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 3, 2, 2, 2, ...`
-/

namespace OMA.S_oeis_a303399

/-- The `i`-th triangular number `T(i) = i * (i + 1) / 2`. -/
def triangular (i : ℕ) : ℕ := i * (i + 1) / 2

/-- `a n` is the number of pairs `(x, y)` with `0 ≤ x ≤ y` such that `n - 5 ^ x - 5 ^ y` is a
(nonnegative) sum of two triangular numbers `T(i) + T(j)` with `i, j ≥ 0`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ⟨x, y⟩ =>
    x ≤ y ∧ 5 ^ x + 5 ^ y ≤ n ∧
      ∃ i ∈ Finset.range (n + 1), ∃ j ∈ Finset.range (n + 1),
        triangular i + triangular j = n - (5 ^ x + 5 ^ y)).card

/-- OEIS A303399 conjecture (Zhi-Wei Sun): `a n > 0` for all `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303399
