import Mathlib

/-!
# OEIS A208044: Barker's g.f. and closed form for n X 3 0..3 arrays, values introduced in row major order, no element equal to a horizontal, vertical or antidiagonal neighbor

Source: https://oeis.org/A208044 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A208044 (R. H. Hardin, Feb 22 2012), offset 1: Number of n X 3 0..3 arrays with new values
0..3 introduced in row major order and no element equal to any horizontal, vertical or antidiagonal
neighbor (colorings ignoring permutations of colors). Column 3 of A208050.
Formula section:
Conjectures from Colin Barker, Mar 06 2018:
G.f.: 2*x*(1 - x)*(1 - 2*x) / (1 - 7*x + 8*x^2).
a(n) = (2^(-5-n)*((7-sqrt(17))^n*(-13+5*sqrt(17)) + (7+sqrt(17))^n*(13+5*sqrt(17)))) / sqrt(17) for n>1.

Formalization notes:
* An array is a function x : Fin n -> Fin 3 -> Fin 4, x i j being the entry in row i and column j.
* The neighbors of x(i,j) are x(i,j+1) and x(i,j-1) (horizontal), x(i+1,j) and x(i-1,j) (vertical),
  and x(i-1,j+1) and x(i+1,j-1) (antidiagonal); since the relation is symmetric, no element equal to
  any of them means that x(i,j) differs from x(i,j+1), x(i,j) differs from x(i+1,j), and x(i,j+1)
  differs from x(i+1,j) (`NoEqualNeighbor`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 7x + 8x^2) = 2x(1 - x)(1 - 2x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 2, with the powers of 2 of negative exponent as integer powers (zpow).
* Controls proved in the proof file: the definition gives 2, 8, 44, 244, 1356, 7540, 41932, 233204,
  1296972, 7213172 for n = 1..10, the entry's data, and a direct enumeration of all arrays with one
  row gives a(1) = 2.
-/

namespace OMA.S_oeis_a208044

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- No element of x is equal to a horizontal, vertical or antidiagonal neighbor: x(i,j) differs from
x(i,j+1) and from x(i+1,j), and x(i,j+1) differs from x(i+1,j). -/
def NoEqualNeighbor {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  (∀ i, ∀ j j' : Fin C, j'.val = j.val + 1 → x i j ≠ x i j') ∧
  (∀ i i' : Fin R, i'.val = i.val + 1 → ∀ j, x i j ≠ x i' j) ∧
  (∀ i i' : Fin R, i'.val = i.val + 1 → ∀ j j' : Fin C, j'.val = j.val + 1 → x i j' ≠ x i' j)

instance {R C K : ℕ} : DecidablePred (@NoEqualNeighbor R C K) := fun x => by
  unfold NoEqualNeighbor; infer_instance

/-- A208044(n): the number of n X 3 arrays with entries 0..3, x i j being the entry in row i and
column j, in which no element is equal to a horizontal, vertical or antidiagonal neighbor
(`NoEqualNeighbor`) and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 → Fin 4)).filter
    (fun x => NoEqualNeighbor x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 7 * X + 8 * X ^ 2) = 2 * X * (1 - X) * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) =
      (2 ^ (-5 - (n : ℤ)) * ((7 - Real.sqrt 17) ^ n * (-13 + 5 * Real.sqrt 17) +
        (7 + Real.sqrt 17) ^ n * (13 + 5 * Real.sqrt 17))) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a208044
