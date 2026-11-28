import Mathlib

/-!
# OEIS A229472: Barker's generating function and closed form

Source: https://oeis.org/A229472 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Sep 24 2013), offset 1: Number of defective 4-colorings of an n X 1 0..3
array connected horizontally, antidiagonally and vertically with exactly one mistake, and colors
introduced in row-major 0..3 order. Data: 0, 1, 2, 6, 20, 70, 246, 854, ... Formula section:
Conjectures from Colin Barker, Mar 16 2018:
G.f.: x^2*(1 - 6*x + 12*x^2 - 8*x^3 + 3*x^4) / ((1 - x)^2*(1 - 3*x)^2).
a(n) = (27+3^n) * (n-1) / 54 for n>2.

Formalization notes:
* An n X 1 array has only vertical connections (no horizontal or antidiagonal neighbours), so a
  mistake is a pair of vertically adjacent elements of the same color, and the coloring has
  exactly one such pair. Colors introduced in row-major 0..3 order means that the colors first
  appear in the order 0, 1, 2, 3: the upper left element is 0, and each element is at most the
  number k of colors used above it. The array is a function `Fin n → Fin 4` and its column, read
  from the top, is `List.ofFn x`.
* `ok p k e l` scans the rest `l` of the column, where `p` is the element above it, `k` the
  number of colors used so far and `e` the number of mistakes so far; `valid` adds that the upper
  left element is 0. This reading reproduces the first nine terms of the entry's data by brute
  force and gives the six solutions listed for n = 4.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n > 2.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..15) = 0, 1, 2, 6, 20, 70, 246, 854, 2920, 9846, 32810,
  108262, 354300, 1151462, 3720094, the entry's data, and a(4) = 6 by direct enumeration of the
  256 arrays.
-/

namespace OMA.S_oeis_a229472

open PowerSeries

/-- Scanning a column from the top. `p` is the element above the rest of the column, `k` is the
number of colors used so far (they are 0, ..., k - 1) and `e` is the number of mistakes so far.
A mistake is an element equal to the element above it (vertical neighbours of the same color); a
second mistake rejects the column, and at the end there must be exactly one. Every element is at
most k, so a color that has not been used is the next new color. -/
def ok : Fin 4 → ℕ → ℕ → List (Fin 4) → Bool
  | _, _, e, [] => decide (e = 1)
  | p, k, e, c :: l =>
    decide (c.val ≤ k) &&
      (if c = p then decide (e = 0) && ok c k 1 l else ok c (max k (c.val + 1)) e l)

/-- An n X 1 array, read as its single column from the top: the upper left element is color 0,
the first new color, and the rest of the column passes the scan. -/
def valid : List (Fin 4) → Bool
  | [] => false
  | c :: l => decide (c = 0) && ok c 1 0 l

/-- A229472(n): the number of valid n X 1 arrays with colors 0..3. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 4 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 2. -/
theorem main :
    gf = X ^ 2 * (1 - 6 * X + 12 * X ^ 2 - 8 * X ^ 3 + 3 * X ^ 4) *
      ((1 - X) ^ 2 * (1 - 3 * X) ^ 2)⁻¹ ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (27 + 3 ^ n) * (n - 1) / 54 := by
  sorry

end OMA.S_oeis_a229472
