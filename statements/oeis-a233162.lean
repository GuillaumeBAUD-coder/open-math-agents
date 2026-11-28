import Mathlib

/-!
# OEIS A233162: Barker's generating function and closed form

Source: https://oeis.org/A233162 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 05 2013), offset 1: Number of n X 1 0..7 arrays with no element x(i,j)
adjacent to itself or value 7-x(i,j) horizontally, diagonally, antidiagonally or vertically, top
left element zero, and 1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3
appearing before 4 in row major order (unlabeled 8-colorings with no clashing color pairs).
Data: 1, 1, 3, 11, 48, 236, 1248, ... Formula section: Conjectures from Colin Barker, Feb 18 2018:
G.f.: x*(1 - 11*x + 35*x^2 - 29*x^3) / ((1 - 2*x)*(1 - 4*x)*(1 - 6*x)).
a(n) = (2^(n-6)*(90 + 9*2^n + 2*3^n)) / 9 for n>1.

Formalization notes:
* An n X 1 array has only vertical neighbours, so the adjacency condition says that no two
  vertically adjacent elements are equal or sum to 7. Row major order is the order from the top.
  1 appearing before 2, 3, 4, 5 and 6 means that none of them occurs before the first 1, and
  likewise for 2 before 3, 4 and 5 and for 3 before 4 (the value 7 is not constrained). The array
  is a function `Fin n → Fin 8` and its column is `List.ofFn x`.
* `ok p s1 s2 s3 l` scans the rest `l` of the column, where `p` is the element above it and `s1`,
  `s2`, `s3` record whether a 1, a 2, a 3 has appeared; `valid` adds that the top left element is
  0. This reading reproduces the first seven terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n > 1, with 2^(n-6) as an integer power of 2.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..13) = 1, 1, 3, 11, 48, 236, 1248, 6896, 39168,
  226496, 1325568, 7821056, 46399488, the entry's data, and a(3) = 3 by direct enumeration of the
  512 arrays.
-/

namespace OMA.S_oeis_a233162

open PowerSeries

/-- Scanning a column from the top. `p` is the element above the rest of the column, and `s1`,
`s2`, `s3` say whether a 1, a 2, a 3 has appeared. No element is adjacent to itself or to 7 minus
itself; a 2, 3, 4, 5 or 6 may appear only after a 1 has appeared, a 3, 4 or 5 only after a 2 has
appeared, and a 4 only after a 3 has appeared. -/
def ok : Fin 8 → Bool → Bool → Bool → List (Fin 8) → Bool
  | _, _, _, _, [] => true
  | p, s1, s2, s3, c :: l =>
    decide (c ≠ p) && decide (c.val + p.val ≠ 7) &&
      (s1 || !decide (2 ≤ c.val ∧ c.val ≤ 6)) && (s2 || !decide (3 ≤ c.val ∧ c.val ≤ 5)) &&
      (s3 || decide (c.val ≠ 4)) &&
      ok c (s1 || decide (c.val = 1)) (s2 || decide (c.val = 2)) (s3 || decide (c.val = 3)) l

/-- An n X 1 array, read as its single column from the top: the top left element is 0 and the
rest of the column passes the scan. -/
def valid : List (Fin 8) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok c false false false l

/-- A233162(n): the number of valid n X 1 arrays with entries 0..7. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 8 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 1. -/
theorem main :
    gf = X * (1 - 11 * X + 35 * X ^ 2 - 29 * X ^ 3) *
      ((1 - 2 * X) * (1 - 4 * X) * (1 - 6 * X))⁻¹ ∧
    ∀ n : ℕ, 1 < n → (a n : ℚ) = 2 ^ ((n : ℤ) - 6) * (90 + 9 * 2 ^ n + 2 * 3 ^ n) / 9 := by
  sorry

end OMA.S_oeis_a233162
