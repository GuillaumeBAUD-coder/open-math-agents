import Mathlib

/-!
# OEIS A269091: Barker's generating function and closed form

Source: https://oeis.org/A269091 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Feb 19 2016), offset 1: Number of n X 2 0..3 arrays with some element plus
some horizontally or vertically adjacent neighbor totalling three exactly once. Data: 4, 96, 1152,
11424, 103488, ... Formula section: Conjectures from Colin Barker, Mar 21 2018:
G.f.: 4*x*(1 + 10*x + x^2) / (1 - 7*x)^2.
a(n) = 96*7^(n-3)*(5*n-3) for n>1.

Formalization notes:
* The condition is that exactly one unordered pair of horizontally or vertically adjacent
  elements totals three (an ordered reading would count every pair twice and could never give
  exactly once, while the data are positive). The array is a function from the n rows to pairs
  (x(i,0), x(i,1)); the adjacent pairs are (x(i,0), x(i,1)) in each row and (x(i,j), x(i+1,j))
  between consecutive rows.
* `ok r e l` scans the rows `l` below the row `r`, where `e` is the number of pairs totalling
  three found so far (the horizontal pairs of the rows read and the vertical pairs between them);
  stopping as soon as e exceeds one does not change the count of arrays with exactly one; `valid`
  starts the scan with the horizontal pair of the first row. This reading reproduces the first
  four terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n > 1, with 7^(n-3) an integer power (it is 1/7 at n = 2).
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..10) = 4, 96, 1152, 11424, 103488, 889056, 7375872,
  59698464, 474360768, 3715826016, the entry's data, and a(2) = 96 by direct enumeration of the
  256 arrays with two rows.
-/

namespace OMA.S_oeis_a269091

open PowerSeries

/-- The number of pairs totalling three among the adjacent pairs that a new row (c, d) adds below
the row (a, b): the horizontal pair (c, d) and the vertical pairs (a, c) and (b, d). -/
def hits (a b c d : Fin 4) : ℕ :=
  (if c.val + d.val = 3 then 1 else 0) + (if a.val + c.val = 3 then 1 else 0) +
    (if b.val + d.val = 3 then 1 else 0)

/-- Scanning the rows from the top: `r` is the row above the rest of the array and `e` the number
of horizontally or vertically adjacent pairs totalling three found so far, which may never exceed
one; at the end there must be exactly one. -/
def ok : Fin 4 × Fin 4 → ℕ → List (Fin 4 × Fin 4) → Bool
  | _, e, [] => decide (e = 1)
  | r, e, s :: l => decide (e + hits r.1 r.2 s.1 s.2 ≤ 1) && ok s (e + hits r.1 r.2 s.1 s.2) l

/-- An n X 2 array, given by its rows (x(i,0), x(i,1)) from the top: the first row contributes its
horizontal pair, and the rest of the rows pass the scan. -/
def valid : List (Fin 4 × Fin 4) → Bool
  | [] => false
  | s :: l => ok s (if s.1.val + s.2.val = 3 then 1 else 0) l

/-- A269091(n): the number of n X 2 arrays with entries 0..3 in which exactly one pair of
horizontally or vertically adjacent elements totals three. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 × Fin 4 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 1. -/
theorem main :
    gf = 4 * X * (1 + 10 * X + X ^ 2) * ((1 - 7 * X) ^ 2)⁻¹ ∧
    ∀ n : ℕ, 1 < n → (a n : ℚ) = 96 * 7 ^ ((n : ℤ) - 3) * (5 * n - 3) := by
  sorry

end OMA.S_oeis_a269091
