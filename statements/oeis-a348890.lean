import Mathlib

/-!
# A348890: Number of ways to write n as 5*w^4 + x^4 + y^2 + z^2, where w,x,y,z are nonnegative integers with y <= z.

Source: https://oeis.org/A348890
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, OEIS A348890): `a(n) = 0` only for `n ≡ 12 (mod 16)`.

The entry also proves the converse (`a(n) = 0` whenever `n ≡ 12 (mod 16)`, by a mod 8
argument); only the conjectured direction is stated here: if `a(n) = 0` then `n % 16 = 12`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* `a n` counts ordered 4-tuples `(w, x, y, z)` of natural numbers with `y ≤ z` and
  `5 * w ^ 4 + x ^ 4 + y ^ 2 + z ^ 2 = n`.
* Since every term is nonnegative, any solution satisfies the lossless bounds
  - `5 * (w ^ 2) ^ 2 ≤ n`, hence `w ^ 4 ≤ n / 5` and `w ≤ (n / 5).sqrt.sqrt`;
  - `(x ^ 2) ^ 2 ≤ n`, hence `x ≤ n.sqrt.sqrt`;
  - `y ^ 2 ≤ n` and `z ^ 2 ≤ n`, hence `y, z ≤ n.sqrt`.
* Initial values for `n = 0, 1, ..., 15`:
  `a(n) = 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 4, 2, 0, 2, 3, 2, ...`.
-/

namespace OMA.S_oeis_a348890

/-- `a n` is the number of ordered 4-tuples `(w, x, y, z)` of nonnegative integers with `y ≤ z`
and `5 * w ^ 4 + x ^ 4 + y ^ 2 + z ^ 2 = n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range ((n / 5).sqrt.sqrt + 1) ×ˢ Finset.range (n.sqrt.sqrt + 1) ×ˢ
      Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1)).filter
    fun ⟨w, x, y, z⟩ => y ≤ z ∧ 5 * w ^ 4 + x ^ 4 + y ^ 2 + z ^ 2 = n).card

/-- OEIS A348890 conjecture: `a n = 0` only when `n ≡ 12 (mod 16)`. -/
theorem main : ∀ n : ℕ, a n = 0 → n % 16 = 12 := by
  sorry

end OMA.S_oeis_a348890
