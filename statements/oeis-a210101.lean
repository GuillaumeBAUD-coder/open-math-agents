import Mathlib

/-!
# OEIS A210101: Barker's g.f. and closed form for (n+1) X 3 0..2 arrays, values introduced in row major order, every 2 X 2 subblock with one or three distinct values

Source: https://oeis.org/A210101 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A210101 (R. H. Hardin, Mar 17 2012), offset 1: Number of (n+1) X 3 0..2 arrays with every 2 X
2 subblock having one or three distinct values, and new values 0..2 introduced in row major order.
Column 2 of A210107.
Formula section:
Conjectures from Colin Barker, Jul 14 2018:
G.f.: 5*x*(6 - 3*x - 4*x^2) / ((1 - x)*(1 - 7*x - 4*x^2)).
a(n) = (1/13)*2^(-2-n)*(13*2^(1+n) + (117-11*sqrt(65))*(7-sqrt(65))^n + (7+sqrt(65))^n*(117+11*sqrt(65))).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 3 -> Fin 3, x i j being the entry in row i and
  column j.
* The 2 X 2 subblocks are the blocks in rows i, i + 1 and columns j, j + 1; `blockCount` is the
  number of distinct values among the four entries of a block, and every block must have one or
  three distinct values (`BlocksOK`).
* New values introduced in row major order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every value smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring of the cells up to renaming of the colors. Not every value of 0..2 has to
  occur; this reading reproduces the entry's data.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)(1 - 7x - 4x^2)) = 5x(6 - 3x - 4x^2) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed
  form in the reals for every n >= 1, with the powers of 2 of negative exponent as integer powers
  (zpow).
* Controls proved in the proof file: the definition gives 30, 225, 1690, 12725, 95830, 721705,
  5435250, 40933565, 308275950, 2321665905 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a210101

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

/-- Every 2 X 2 subblock of x, in rows i, i + 1 and columns j, j + 1, has one or three distinct values. -/
def BlocksOK {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i i' : Fin R, ∀ j j' : Fin C, i'.val = i.val + 1 → j'.val = j.val + 1 →
    blockCount x i i' j j' = 1 ∨ blockCount x i i' j j' = 3

instance {R C K : ℕ} : DecidablePred (@BlocksOK R C K) := fun x => by
  unfold BlocksOK; infer_instance

/-- A210101(n): the number of (n+1) X 3 arrays with entries 0..2, x i j being the entry in row i and
column j, in which every 2 X 2 subblock has one or three distinct values (`BlocksOK`) and the values
are introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 3)).filter
    (fun x => BlocksOK x ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 7 * X - 4 * X ^ 2)) = 5 * X * (6 - 3 * X - 4 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (1 / 13) * 2 ^ (-2 - (n : ℤ)) *
        (13 * 2 ^ (1 + n) + (117 - 11 * Real.sqrt 65) * (7 - Real.sqrt 65) ^ n +
          (7 + Real.sqrt 65) ^ n * (117 + 11 * Real.sqrt 65)) := by
  sorry

end OMA.S_oeis_a210101
