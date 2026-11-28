import Mathlib

/-!
# A283582: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 646', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A283582
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: (1 + 11*x + x^2 - 89*x^3 + x^4 - 89*x^5 - 9999*x^6 + 909911*x^7 - 10000*x^8 - 1090100*x^9 + 100000000*x^10 - 8900000000*x^11) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 + x^2)*(1 + x^4)).
* a(n) = 100*a(n-2) + a(n-8) - 100*a(n-10) for n>11.

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a283582

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

/-- A283582(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 646 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2) * (1 + X ^ 4) : PowerSeries ℚ) = 1 + 11 * X + X ^ 2 - 89 * X ^ 3 + X ^ 4 - 89 * X ^ 5 - 9999 * X ^ 6 + 909911 * X ^ 7 - 10000 * X ^ 8 - 1090100 * X ^ 9 + 100000000 * X ^ 10 - 8900000000 * X ^ 11) ∧
    (∀ n : ℕ, 12 ≤ n → (a n : ℚ) = 100 * a (n - 2) + a (n - 8) - 100 * a (n - 10)) := by
  sorry

end OMA.S_oeis_a283582
