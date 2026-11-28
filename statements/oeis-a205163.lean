import Mathlib

/-!
# OEIS A205163: Barker's g.f. and closed form for (n+1) X 2 0..3 arrays with values introduced in row major order and no 2 X 2 subblock with equal diagonal and equal antidiagonal elements

Source: https://oeis.org/A205163 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A205163 (R. H. Hardin, Jan 22 2012), offset 1: Number of (n+1) X 2 0..3 arrays with every
2 X 2 subblock having unequal diagonal elements or unequal antidiagonal elements, and new values
0..3 introduced in row major order. Column 1 of A205170.
Formula section:
Conjectures from Colin Barker, Mar 03 2018:
G.f.: x*(13 - 75*x) / ((1 - 3*x)*(1 - 15*x)).
a(n) = 3^(n-1)*(2*5^n+3).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the entry in row i and
  column j.
* The 2 X 2 subblocks are the blocks in rows i, i + 1 and columns j, j + 1. The diagonal elements
  of a block are x(i,j), x(i+1,j+1) and its antidiagonal elements are x(i,j+1), x(i+1,j); every
  block must have unequal diagonal elements or unequal antidiagonal elements (`BlocksOK`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 3x)(1 - 15x) = x(13 - 75x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  natural numbers for every n >= 1. The site's excerpt prints 2*5^n as 25^n because the
  multiplication signs are dropped; the entry has 2*5^n.
* Controls proved in the proof file: the definition gives 13, 159, 2277, 33831, 506493, 7594479,
  113908437, 1708600311, 25628925933, 384433652799 for n = 1..10, the entry's data, and a direct
  enumeration of all arrays with two rows gives a(1) = 13.
-/

namespace OMA.S_oeis_a205163

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- Every 2 X 2 subblock of x, in rows i, i + 1 and columns j, j + 1, has unequal diagonal
elements x(i,j), x(i+1,j+1) or unequal antidiagonal elements x(i,j+1), x(i+1,j). -/
def BlocksOK {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
    x i j ≠ x i' j' ∨ x i j' ≠ x i' j

instance {R C K : ℕ} : DecidablePred (@BlocksOK R C K) := fun x => by
  unfold BlocksOK; infer_instance

/-- A205163(n): the number of (n+1) X 2 arrays with entries 0..3, x i j being the entry in row i
and column j, in which every 2 X 2 subblock has unequal diagonal or unequal antidiagonal elements
and the values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun x => BlocksOK x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. x(13 - 75x)/((1 - 3x)(1 - 15x)) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - 3 * X) * (1 - 15 * X)) = X * (13 - 75 * X) ∧
    ∀ n : ℕ, 1 ≤ n → a n = 3 ^ (n - 1) * (2 * 5 ^ n + 3) := by
  sorry

end OMA.S_oeis_a205163
