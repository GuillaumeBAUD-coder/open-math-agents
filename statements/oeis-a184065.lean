import Mathlib

/-!
# A184065: Number of (n+1) X 4 binary arrays with rows and columns in nondecreasing order and with no 2 X 2 subblock sum differing from a horizontal or vertical neighbor subblock sum by more than one

Source: https://oeis.org/A184065 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated (Antigravity / gemini-4-neon-high), submitted by @Solfanbtc.

Conjectures from Colin Barker, Apr 11 2018, quoted verbatim from the OEIS entry:
* G.f.: x*(20 - 44*x + 106*x^2 - 2*x^3 + 52*x^4 - 4*x^5 + 73*x^6 - 62*x^7 + 31*x^8 - 31*x^9 + 5*x^10 - x^11 + x^12) / (1 - x)^4.
* a(n) = 757 + 14*n - 115*n^2 + 24*n^3 for n>9.
* a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>13.

Formalization notes:
* Offset 1,1: the sequence is indexed by `n >= 1`, starting with
  20, 36, 130, 382, 924, 1884, 3463, 5800, 9065, 13397, 18940, 25837, 34232,
  44269, 56092, 69845, 85672, 103717, 124124, 147037, 172600, 200957, 232252,
  266629, 304232, 345205, 389692, 437837, 489784, 545677, 605660, 669877,
  738472, 811589.
* In R. H. Hardin's convention for A184065 (Column 3 of A184071), rows and columns
  being in nondecreasing order means the rows `M 0, ..., M n` are in nondecreasing
  lexicographic order as 4-bit vectors and the columns `col 0, ..., col 3` are in
  nondecreasing lexicographic order as `(n+1)`-bit vectors. This definition reproduces
  all 34 listed OEIS data terms exactly.
* Each `2 X 2` subblock sum at `(i, j)` for `i : Fin n` and `j : Fin 3` is the sum of
  its four binary entries; horizontal neighbors `(i, j)` and `(i, j+1)` and vertical
  neighbors `(i, j)` and `(i+1, j)` must differ by at most 1.
* `series` is the ordinary generating function `Sum_{n >= 1} a(n) x^n` over `ℚ`
  (constant term 0 since the offset is 1). The g.f. conjecture is stated with the
  invertible denominator `(1 - X)^4` cleared.
* The closed form is stated in `ℤ` for `n > 9`, and the linear recurrence is stated
  in `ℤ` for `n > 13`, matching the OEIS entry verbatim.
-/

namespace OMA.S_oeis_a184065

/-- Lexicographic order on finite binary vectors `Fin k → Fin 2`:
`u ≤_lex v` iff `u = v`, or at the first coordinate where they differ `u i < v i`. -/
def LexLe {k : ℕ} (u v : Fin k → Fin 2) : Prop :=
  u = v ∨ ∃ i : Fin k, (∀ j : Fin k, j < i → u j = v j) ∧ u i < v i

/-- The sum of the four entries in the `2 × 2` subblock with top-left corner `(i, j)`. -/
def subblockSum {n : ℕ} (M : Fin (n + 1) → Fin 4 → Fin 2) (i : Fin n) (j : Fin 3) : ℤ :=
  ((M i.castSucc j.castSucc).val : ℤ) + ((M i.castSucc j.succ).val : ℤ) +
  ((M i.succ j.castSucc).val : ℤ) + ((M i.succ j.succ).val : ℤ)

/-- An `(n + 1) × 4` binary array with rows and columns in nondecreasing lexicographic order
and with no `2 × 2` subblock sum differing from a horizontal or vertical neighbor subblock
sum by more than `1`. -/
def IsValidArray (n : ℕ) (M : Fin (n + 1) → Fin 4 → Fin 2) : Prop :=
  (∀ i : Fin n, LexLe (M i.castSucc) (M i.succ)) ∧
  (∀ j : Fin 3, LexLe (fun i => M i j.castSucc) (fun i => M i j.succ)) ∧
  (∀ (i : Fin n) (j : Fin 2), |subblockSum M i j.castSucc - subblockSum M i j.succ| ≤ 1) ∧
  (∀ (i₁ i₂ : Fin n), i₁.val + 1 = i₂.val →
    ∀ j : Fin 3, |subblockSum M i₁ j - subblockSum M i₂ j| ≤ 1)

/-- `A184065(n)` (offset 1): the number of valid `(n + 1) × 4` binary arrays. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card { M : Fin (n + 1) → Fin 4 → Fin 2 // IsValidArray n M }

/-- The ordinary generating function `∑_{n ≥ 1} a(n) X^n` over `ℚ`. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

open PowerSeries in
theorem main :
    (1 - X) ^ 4 * series =
      X * (20 - 44 * X + 106 * X ^ 2 - 2 * X ^ 3 + 52 * X ^ 4 - 4 * X ^ 5 +
           73 * X ^ 6 - 62 * X ^ 7 + 31 * X ^ 8 - 31 * X ^ 9 + 5 * X ^ 10 -
           X ^ 11 + X ^ 12) ∧
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 757 + 14 * (n : ℤ) - 115 * (n : ℤ) ^ 2 + 24 * (n : ℤ) ^ 3) ∧
    (∀ n : ℕ, 13 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a184065
