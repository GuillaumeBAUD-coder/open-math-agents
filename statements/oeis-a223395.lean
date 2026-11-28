import Mathlib

/-!
# OEIS A223395: Barker's generating function and closed form for walks on the 4 X 4 grid

Source: https://oeis.org/A223395 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 19 2013), offset 1: 4 X 4 square grid graph coloring a rectangular
array: number of n X 1 0..15 arrays where 0..15 label nodes of the square grid graph and every
array movement to a horizontal or vertical neighbor moves along an edge of this graph. Data: 16,
48, 152, 488, 1576, 5096, ... Formula section: Conjectures from Colin Barker, Aug 20 2018:
G.f.: 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)).
a(n) = (8 + (11-5*sqrt(5))*(1-sqrt(5))^n + (1+sqrt(5))^n*(11+5*sqrt(5))) / 5.

Formalization notes:
* The labels 0..15 are given to the nodes of the 4 X 4 grid row by row: label x is the node in
  row x / 4 and column x % 4, and two labels are adjacent when their nodes are in the same row and
  neighbouring columns or in the same column and neighbouring rows. Any other bijection between
  labels and nodes gives the same count.
* An n X 1 array is a function from the n rows to the labels; it has no horizontal neighbours, so
  the condition is that the labels in rows i and i + 1 are adjacent for every i.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for the terms
  of the sequence, n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..12) = 16, 48, 152, 488, 1576, 5096, 16488, 53352,
  172648, 558696, 1807976, 5850728, the entry's data, and a(2) = 48 by direct enumeration of the
  256 arrays with two rows.
-/

namespace OMA.S_oeis_a223395

open PowerSeries Finset

/-- Nodes of the 4 X 4 square grid graph, labelled 0..15 row by row: label x is the node in row
x / 4 and column x % 4. Two nodes are joined when they are in the same row and in neighbouring
columns, or in the same column and in neighbouring rows. -/
def adj (x y : Fin 16) : Prop :=
  (x.val / 4 = y.val / 4 ∧ (x.val % 4 + 1 = y.val % 4 ∨ y.val % 4 + 1 = x.val % 4)) ∨
    (x.val % 4 = y.val % 4 ∧ (x.val / 4 + 1 = y.val / 4 ∨ y.val / 4 + 1 = x.val / 4))

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223395(n): the number of n X 1 arrays with entries 0..15 in which every move to the vertical
neighbour (row i to row i + 1) is along an edge of the grid graph. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 16)).filter
    (fun f => ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j))).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = 8 * X * (2 - 3 * X ^ 2) * ((1 - X) * (1 - 2 * X - 4 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
      (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5 := by
  sorry

end OMA.S_oeis_a223395
