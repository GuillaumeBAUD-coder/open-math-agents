import Mathlib

/-!
# OEIS A210406: Barker's g.f. and closed form for (n+1) X 2 0..3 arrays, values introduced in row major order, every 2 X 2 subblock with three or four distinct values

Source: https://oeis.org/A210406 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A210406 (R. H. Hardin, Mar 21 2012), offset 1: Number of (n+1) X 2 0..3 arrays with every 2 X
2 subblock having three or four distinct values, and new values 0..3 introduced in row major order.
Column 1 of A210413.
Formula section:
Conjectures from Colin Barker, Jul 15 2018:
G.f.: x*(7 + 8*x) / (1 - 10*x - 12*x^2).
a(n) = ((5-sqrt(37))^n*(-11+2*sqrt(37)) + (5+sqrt(37))^n*(11+2*sqrt(37))) / (6*sqrt(37)).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the entry in row i and
  column j.
* The 2 X 2 subblocks are the blocks in rows i, i + 1 and columns j, j + 1; `blockCount` is the
  number of distinct values among the four entries of a block, and every block must have three or
  four distinct values (`BlocksOK`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..3 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 10x - 12x^2) = x(7 + 8x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1.
* Controls proved in the proof file: the definition gives 7, 78, 864, 9576, 106128, 1176192,
  13035456, 144468864, 1601114112, 17744767488 for n = 1..10, the entry's data, and a direct
  enumeration of all arrays with two rows gives a(1) = 7.
-/

namespace OMA.S_oeis_a210406

open PowerSeries Finset

/-- The values of the array x are introduced in row major order: every value below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of distinct values in the 2 X 2 subblock of x in rows i, i' and columns j, j'. -/
def blockCount {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i i' : Fin R) (j j' : Fin C) : ℕ :=
  ({x i j, x i j', x i' j, x i' j'} : Finset (Fin K)).card

/-- Every 2 X 2 subblock of x, in rows i, i + 1 and columns j, j + 1, has three or four distinct values. -/
def BlocksOK {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
    blockCount x i i' j j' = 3 ∨ blockCount x i i' j j' = 4

instance {R C K : ℕ} : DecidablePred (@BlocksOK R C K) := fun x => by
  unfold BlocksOK; infer_instance

/-- A210406(n): the number of (n+1) X 2 arrays with entries 0..3, x i j being the entry in row i and
column j, in which every 2 X 2 subblock has three or four distinct values (`BlocksOK`) and the
values are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter
    (fun x => BlocksOK x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 10 * X - 12 * X ^ 2) = X * (7 + 8 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((5 - Real.sqrt 37) ^ n * (-11 + 2 * Real.sqrt 37) +
        (5 + Real.sqrt 37) ^ n * (11 + 2 * Real.sqrt 37)) / (6 * Real.sqrt 37) := by
  sorry

end OMA.S_oeis_a210406
