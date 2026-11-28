import Mathlib

/-!
# OEIS A187177: Hardin's quadratic and Barker's conjectures for 7-step tours

Source: https://oeis.org/A187177 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187177 (R. H. Hardin, Mar 06 2011), offset 1: Number of 7-step left-handed knight's tours (moves only out two, left one) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 780*n^2 - 9880*n + 29384 for n>11.
G.f.: 4*x^6*(4 + 80*x + 136*x^2 + 143*x^3 + 85*x^4 + 19*x^5 - 43*x^6 - 29*x^7 - 5*x^8) / (1 - x)^3 (conjectured). - Colin Barker, Apr 22 2018

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the left-handed knight's moves: two spaces out in a direction, then one to the left: (-1,-2), (2,-1), (1,2), (-2,1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 7-step tour is a sequence of 7 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..7). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 0, 0, 16, 368, 1600, 4284, 8760, 15104, 23144, 32764 for n = 1..13,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187177

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

/-- A187177(n): the 7-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin n × Fin n)).filter (IsTour n 7)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 780 * n ^ 2 - 9880 * n + 29384) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 6 * (4 + 80 * PowerSeries.X + 136 * PowerSeries.X ^ 2 + 143 * PowerSeries.X ^ 3 + 85 * PowerSeries.X ^ 4 + 19 * PowerSeries.X ^ 5 - 43 * PowerSeries.X ^ 6 - 29 * PowerSeries.X ^ 7 - 5 * PowerSeries.X ^ 8) := by
  sorry

end OMA.S_oeis_a187177
