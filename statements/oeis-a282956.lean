import Mathlib

/-!
# A282956: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 533', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282956
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 17*a(n-4) - 16*a(n-8) for n > 24.
* G.f.: (384*x^24 - 448*x^23 + 64*x^22 + 384*x^21 - 120*x^20 - 4*x^19 - 4*x^18 - 472*x^17 + 208*x^16 + 8*x^15 + 12*x^13 - 12*x^12 + x^11 + 2*x^10 - x^9 + 10*x^8 - 8*x^7 + 7*x^6 + 2*x^5 + x^4 + 9*x^3 + 4*x^2 + 2*x + 1)/(16*x^8 - 17*x^4 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a282956

/-- `cell code t i j` is the value of the cell at `(i, j)` after `t` steps of the two-dimensional
outer totalistic cellular automaton with Wolfram code `code` on the 5-celled von Neumann
neighbourhood, starting from a single ON cell at `(0, 0)` on an all-OFF background: the new value
of a cell is bit number `c + 2 * s` of `code`, where `c` is its old value and `s` is the number of
ON cells among its four neighbours. -/
def cell (code : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat + (cell code t i (j - 1)).toNat))

/-- The number of ON cells in the square `[-t, t] × [-t, t]` after `t` steps. -/
def onCount (code t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if cell code t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0

/-- A282956(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 533 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 25 ≤ n → (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) = 384 * X ^ 24 - 448 * X ^ 23 + 64 * X ^ 22 + 384 * X ^ 21 - 120 * X ^ 20 - 4 * X ^ 19 - 4 * X ^ 18 - 472 * X ^ 17 + 208 * X ^ 16 + 8 * X ^ 15 + 12 * X ^ 13 - 12 * X ^ 12 + X ^ 11 + 2 * X ^ 10 - X ^ 9 + 10 * X ^ 8 - 8 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 + X ^ 4 + 9 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1) := by
  sorry

end OMA.S_oeis_a282956
