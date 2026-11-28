import Mathlib

/-!
# A188556: Number of 5 X n binary arrays without the pattern 0 1 diagonally, vertically, antidiagonally or horizontally.

Source: https://oeis.org/A188556
Credit: @Salofe

The sequence is due to R. H. Hardin (Apr 04 2011); it is row 5 of A188553.

Conjectures from Colin Barker, Apr 27 2018, quoted verbatim from the entry:
* "G.f.: x*(6 - 25*x + 44*x^2 - 39*x^3 + 18*x^4 - 3*x^5) / (1 - x)^6."
* "a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 6, 11, 20, 36, 64, 112, 192, ...): for n ≥ 1, `a n` is the
  number of 5 X n arrays. We set `a 0 = 0`: the g.f. has no constant term, so `a 0` is its
  coefficient of x^0, and the recurrence (n > 6) never uses it.
* A 5 X n binary array (5 rows, n columns, as in the 5 X 3 examples of the entry) is a function
  `g : Fin 5 → Fin n → Bool`; `g i j` is the entry in row `i` (rows numbered from top to bottom)
  and column `j` (columns numbered from left to right), with `false` = 0 and `true` = 1. Arrays
  are labelled: they are not identified up to symmetry.
* "Without the pattern 0 1" in a direction: no entry 0 is immediately followed by an entry 1 along
  a line in that direction. Every line is read in the reading order of the array (rows from top to
  bottom, each row from left to right): horizontally from `(i, j)` to `(i, j + 1)`, vertically from
  `(i, j)` to `(i + 1, j)`, diagonally from `(i, j)` to `(i + 1, j + 1)`, and antidiagonally from
  `(i, j + 1)` to `(i + 1, j)` (from top right to bottom left).
* This reading reproduces the data: a column-by-column count of exactly this definition gives all
  200 terms of the b-file (n = 1..200), and the seven 5 X 3 solutions shown in the entry satisfy
  it. Among the 16 ways of choosing a reading direction for each of the four kinds of lines, it is
  the only one that does both. For instance, reading the antidiagonals from bottom left to top
  right instead would give 6, 17, 32, 48, 64, ... and would reject four of the seven examples.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℤ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it is
  invertible in `ℤ⟦X⟧`).
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a188556

/-- A 5 X n binary array: `g i j` is the entry in row `i` and column `j` (`false` = 0,
`true` = 1). -/
abbrev Grid (n : ℕ) := Fin 5 → Fin n → Bool

/-- The array `g` contains the pattern `0 1` in none of the four directions: horizontally
(`(i, j)` then `(i, j + 1)`), vertically (`(i, j)` then `(i + 1, j)`), diagonally (`(i, j)` then
`(i + 1, j + 1)`) or antidiagonally (`(i, j + 1)` then `(i + 1, j)`). -/
def Valid {n : ℕ} (g : Grid n) : Prop :=
  (∀ (i : Fin 5) (j : Fin n) (hj : j.val + 1 < n),
    ¬ (g i j = false ∧ g i ⟨j.val + 1, hj⟩ = true)) ∧
  (∀ (i : Fin 5) (j : Fin n) (hi : i.val + 1 < 5),
    ¬ (g i j = false ∧ g ⟨i.val + 1, hi⟩ j = true)) ∧
  (∀ (i : Fin 5) (j : Fin n) (hi : i.val + 1 < 5) (hj : j.val + 1 < n),
    ¬ (g i j = false ∧ g ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩ = true)) ∧
  (∀ (i : Fin 5) (j : Fin n) (hi : i.val + 1 < 5) (hj : j.val + 1 < n),
    ¬ (g i ⟨j.val + 1, hj⟩ = false ∧ g ⟨i.val + 1, hi⟩ j = true))

instance {n : ℕ} (g : Grid n) : Decidable (Valid g) := by
  unfold Valid
  infer_instance

/-- A188556(n) for n ≥ 1: the number of 5 X n binary arrays without the pattern 0 1 diagonally,
vertically, antidiagonally or horizontally. The offset is 1, and `a 0 = 0`. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((Finset.univ.filter (fun g : Grid (n + 1) => Valid g)).card : ℤ)

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(6 - 25x + 44x^2 - 39x^3 + 18x^4 - 3x^5)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk a * (1 - X) ^ 6 =
        X * (6 - 25 * X + 44 * X ^ 2 - 39 * X ^ 3 + 18 * X ^ 4 - 3 * X ^ 5) ∧
    ∀ n : ℕ, 6 < n →
      a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a188556
