import Mathlib

/-!
# OEIS A187607: Hardin's quadratic and Barker's conjectures for 3-step tours

Source: https://oeis.org/A187607 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187607 (R. H. Hardin, Mar 11 2011), offset 1: Number of 3-step one space for components leftwards or up, two space for components rightwards or down asymmetric quasi-bishop's tours (antidiagonal moves become knight moves) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 16*n^2 - 80*n + 100 for n>3.
Conjectures from Colin Barker, Apr 25 2018: (Start)
G.f.: x^3*(9 + 9*x + 19*x^2 - 5*x^3) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>6.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are on the diagonals, one space for components leftwards or up and two spaces for components rightwards or down, so the antidiagonal moves become knight moves: (-1,-1), (2,2), (2,-1), (-1,2).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 3-step tour is a sequence of 3 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..3). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 9, 36, 100, 196, 324, 484, 676 for n = 1..9,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187607

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): on the diagonals, one space for components leftwards or up and two spaces for components rightwards or down, so the antidiagonal moves become knight moves. -/
def moves : List (ℤ × ℤ) := [(-1, -1), (2, 2), (2, -1), (-1, 2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187607(n): the 3-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n × Fin n)).filter (IsTour n 3)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 16 * n ^ 2 - 80 * n + 100) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = PowerSeries.X ^ 3 * (9 + 9 * PowerSeries.X + 19 * PowerSeries.X ^ 2 - 5 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187607
