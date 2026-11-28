import Mathlib

/-!
# OEIS A187292: Hardin's quadratic and Barker's conjectures for 7-step tours

Source: https://oeis.org/A187292 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187292 (R. H. Hardin, Mar 08 2011), offset 1: Number of 7-step one or two space at a time rook's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 109360*n^2 - 763776*n + 1206864 for n>11.
Conjectures from Colin Barker, Apr 23 2018: (Start)
G.f.: 4*x^3*(576 + 10184*x + 23120*x^2 + 17964*x^3 + 7392*x^4 - 280*x^5 - 1716*x^6 - 1604*x^7 - 637*x^8 - 261*x^9 - 47*x^10 - 11*x^11) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>14.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the rook's moves one or two spaces at a time: (1,0), (-1,0), (0,1), (0,-1), (2,0), (-2,0), (0,2), (0,-2).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 7-step tour is a sequence of 7 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..7). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 2304, 47648, 228512, 616752, 1241936, 2102944, 3192912, 4505424, 6037932, 7789392, 9759616 for n = 1..13,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187292

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the rook's moves one or two spaces at a time. -/
def moves : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (2, 0), (-2, 0), (0, 2), (0, -2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187292(n): the 7-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin n × Fin n)).filter (IsTour n 7)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 109360 * n ^ 2 - 763776 * n + 1206864) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 3 * (576 + 10184 * PowerSeries.X + 23120 * PowerSeries.X ^ 2 + 17964 * PowerSeries.X ^ 3 + 7392 * PowerSeries.X ^ 4 - 280 * PowerSeries.X ^ 5 - 1716 * PowerSeries.X ^ 6 - 1604 * PowerSeries.X ^ 7 - 637 * PowerSeries.X ^ 8 - 261 * PowerSeries.X ^ 9 - 47 * PowerSeries.X ^ 10 - 11 * PowerSeries.X ^ 11) ∧
    (∀ n : ℕ, 14 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187292
