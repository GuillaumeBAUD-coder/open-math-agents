import Mathlib

/-!
# A089936: 5 × n binary matrices without adjacent 0's, generating function

Source: https://oeis.org/A089936
Credit: @brinderjaswal-eng

`a(n)` is the number of `5 × n` matrices with entries in `{0, 1}` without adjacent `0`'s in any
row or column (offset `1`: `a(1) = 13`, `a(2) = 99`, `a(3) = 827`, `a(4) = 6743`, …). Equivalently,
the number of independent vertex sets of the grid graph `P_5 × P_n`.

Conjecture (Colin Barker, Jun 06 2017, formula section of the entry): the generating function is

`x (13 + 47x - 37x² - 129x³ + 68x⁴ + 49x⁵ - 23x⁶ - 3x⁷ + x⁸) /
 (1 - 4x - 36x² + 105x⁴ - 15x⁵ - 64x⁶ + 20x⁷ + 4x⁸ - x⁹)`.

(The entry also records a remark of Andrew Howroyd, Dec 24 2019, that the conjecture is correct.)

Conventions:
* A matrix is `M : Fin 5 → Fin n → Fin 2`, row index first. Two entries are adjacent in a row when
  they are `M i j` and `M i j'` with `j' = j + 1`, and adjacent in a column when they are `M i j`
  and `M i' j` with `i' = i + 1`. "Without adjacent `0`'s" says no such pair is `0, 0`.
* The generating function is the ordinary one, `∑_{n ≥ 1} a(n) xⁿ`, in `ℤ⟦X⟧`. The entry has
  offset `1`, so the coefficient of `x⁰` is `0` (the value of the Lean `a 0` plays no role).
* `G = N / D` is stated as `G * D = N`. The denominator has constant coefficient `1`, so it is a
  unit of `ℤ⟦X⟧` and the two forms say the same thing.
-/

namespace OMA.S_oeis_a089936

open PowerSeries

/-- The number of `5 × n` matrices with entries in `{0, 1}` in which no two entries that are
adjacent in a row, or adjacent in a column, are both `0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun M : Fin 5 → Fin n → Fin 2 =>
    (∀ i : Fin 5, ∀ j j' : Fin n, j.val + 1 = j'.val → ¬ (M i j = 0 ∧ M i j' = 0)) ∧
    (∀ i i' : Fin 5, ∀ j : Fin n, i.val + 1 = i'.val → ¬ (M i j = 0 ∧ M i' j = 0))).card

/-- Conjecture (Barker): `∑_{n ≥ 1} a(n) xⁿ` is the stated rational function. -/
theorem main :
    (PowerSeries.mk fun n : ℕ => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        (1 - 4 * X - 36 * X ^ 2 + 105 * X ^ 4 - 15 * X ^ 5 - 64 * X ^ 6 + 20 * X ^ 7
          + 4 * X ^ 8 - X ^ 9) =
      X * (13 + 47 * X - 37 * X ^ 2 - 129 * X ^ 3 + 68 * X ^ 4 + 49 * X ^ 5 - 23 * X ^ 6
          - 3 * X ^ 7 + X ^ 8) := by
  sorry

end OMA.S_oeis_a089936
