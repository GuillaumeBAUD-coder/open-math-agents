import Mathlib

/-!
# A282494: Number of ways to write n as x^4 + y^2 + z^2 + w^2 with y*(y+240*z) a positive square, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A282494
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, OEIS A282494): `a(n) > 0` for all `n > 0`.

Formalization notes:
* The sequence has offset `1`; `a` is defined on all of `ℕ` and the conjecture is stated for
  `n > 0` (`a 0 = 0`, since `y * (y + 240 * z) > 0` forces `y > 0`).
* `a n` counts ordered 4-tuples `(x, y, z, w)` of natural numbers with
  `x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n` such that `y * (y + 240 * z)` is a positive square,
  i.e. `0 < y * (y + 240 * z)` and `IsSquare (y * (y + 240 * z))`. There is no ordering
  constraint between `z` and `w` (the OEIS entry imposes none; the data counts both orders).
* Since every term is nonnegative, any solution satisfies the lossless bounds
  - `(x ^ 2) ^ 2 ≤ n`, hence `x ≤ n.sqrt.sqrt`;
  - `y ^ 2, z ^ 2, w ^ 2 ≤ n`, hence `y, z, w ≤ n.sqrt`.
* Initial values for `n = 1, 2, ..., 16`:
  `a(n) = 1, 2, 1, 1, 4, 4, 1, 1, 3, 5, 4, 1, 3, 6, 3, 1, ...`.
-/

namespace OMA.S_oeis_a282494

/-- `a n` is the number of ordered 4-tuples `(x, y, z, w)` of nonnegative integers with
`x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n` and `y * (y + 240 * z)` a positive square. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1)).filter
    fun ⟨x, y, z, w⟩ => x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
      0 < y * (y + 240 * z) ∧ IsSquare (y * (y + 240 * z))).card

/-- OEIS A282494 conjecture: `a n > 0` for all `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282494
