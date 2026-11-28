import Mathlib

/-!
# OEIS A187176: Hardin's quadratic and Barker's conjectures for 6-step tours

Source: https://oeis.org/A187176 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187176 (R. H. Hardin, Mar 06 2011), offset 1: Number of 6-step left-handed knight's tours (moves only out two, left one) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 284*n^2 - 3100*n + 7944 for n>9.
G.f.: 8*x^6*(11 + 29*x + 27*x^2 + 18*x^3 - 3*x^4 - 9*x^5 - 2*x^6) / (1 - x)^3 (conjectured). - Colin Barker, Apr 22 2018

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the left-handed knight's moves: two spaces out in a direction, then one to the left: (-1,-2), (2,-1), (1,2), (-2,1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 6-step tour is a sequence of 6 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..6). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 0, 0, 88, 496, 1440, 3064, 5344, 8208, 11640, 15640 for n = 1..13,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187176

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the left-handed knight's moves: two spaces out in a direction, then one to the left. -/
def moves : List (ℤ × ℤ) := [(-1, -2), (2, -1), (1, 2), (-2, 1)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187176(n): the 6-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin n × Fin n)).filter (IsTour n 6)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 284 * n ^ 2 - 3100 * n + 7944) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 8 * PowerSeries.X ^ 6 * (11 + 29 * PowerSeries.X + 27 * PowerSeries.X ^ 2 + 18 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4 - 9 * PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a187176
