import Mathlib

/-!
# A270112: Number of n X 2 0..7 arrays with some element plus some horizontally or vertically adjacent neighbor totalling seven exactly once

Source: https://oeis.org/A270112
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 1 (data 8, 1344, 100800, 6183744, 345422784, ...).

Conventions:
* An n X 2 array is `x : Fin n → Fin 2 → Fin 8`: row `i`, column `j`, entry `x i j` in `0..7`.
* Horizontally adjacent pairs: the two entries `x i 0` and `x i 1` of each row `i`.
* Vertically adjacent pairs: the entries `x i j` and `x (i + 1) j` for each column `j`.
  For an array with `m + 1` rows these are indexed by `(i, j) : Fin m × Fin 2`
  (rows `i.castSucc` and `i.succ`).
* Totalling seven exactly once: exactly one unordered pair of adjacent entries sums to 7.
* `a 0 = 0` is a convention outside the offset; it does not change the generating function
  identity, whose series has zero constant term.

Conjectures (empirical recurrence in the formula section, and Colin Barker, Jan 29 2019):
a(n) = 86*a(n-1) - 1849*a(n-2) for n > 3; G.f.: 8*x*(1 + 82*x + x^2) / (1 - 43*x)^2;
a(n) = 1344*43^(n-3) * (32*n-21) for n > 1.
The generating function is stated after multiplication by its denominator, whose constant
term is one. The closed form has negative exponents at `n = 2`, so it is stated in `ℚ`
with integer exponents.
-/

namespace OMA.S_oeis_a270112

open PowerSeries

/-- The number of horizontally or vertically adjacent pairs of the array `x` (with `m + 1` rows)
totalling seven. -/
def pairsTotallingSeven (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 8) : ℕ :=
  (Finset.univ.filter (fun i : Fin (m + 1) => (x i 0 : ℕ) + (x i 1 : ℕ) = 7)).card +
    (Finset.univ.filter
      (fun p : Fin m × Fin 2 => (x p.1.castSucc p.2 : ℕ) + (x p.1.succ p.2 : ℕ) = 7)).card

/-- A270112: the number of n X 2 arrays over `0..7` with exactly one adjacent pair totalling
seven. -/
def a : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    (Finset.univ.filter (fun x : Fin (m + 1) → Fin 2 → Fin 8 => pairsTotallingSeven m x = 1)).card

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 86 * a (n - 1) - 1849 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 43 * X) ^ 2 =
      8 * X * (1 + 82 * X + X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 1344 * 43 ^ ((n : ℤ) - 3) * (32 * n - 21)) := by
  sorry

end OMA.S_oeis_a270112
