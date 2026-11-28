import Mathlib

/-!
# A284348: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 873', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284348
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10*a(n-1) + a(n-8) - 10*a(n-9) for n > 23.
* G.f.: (-1000000000000000*x^23 + 90000000000000*x^22 - 9100000000000*x^21 + 909000000000*x^20 + 9100000000*x^19 + 100000000*x^18 + 999999989900000*x^15 - 89999999090000*x^14 + 9099999910000*x^13 - 908999990000*x^12 - 9100000000*x^11 - 90000100*x^10 - 898980*x^9 - 9091*x^8 + 10099910*x^7 - 909990*x^6 + 91010*x^5 - 9090*x^4 - 90*x^3 + 110*x^2 - 10*x + 1)/(10*x^9 - x^8 - 10*x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284348

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

/-- A284348(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 873 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = 10 * a (n - 1) + a (n - 8) - 10 * a (n - 9)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (10 * X ^ 9 - X ^ 8 - 10 * X + 1 : PowerSeries ℚ) = -1000000000000000 * X ^ 23 + 90000000000000 * X ^ 22 - 9100000000000 * X ^ 21 + 909000000000 * X ^ 20 + 9100000000 * X ^ 19 + 100000000 * X ^ 18 + 999999989900000 * X ^ 15 - 89999999090000 * X ^ 14 + 9099999910000 * X ^ 13 - 908999990000 * X ^ 12 - 9100000000 * X ^ 11 - 90000100 * X ^ 10 - 898980 * X ^ 9 - 9091 * X ^ 8 + 10099910 * X ^ 7 - 909990 * X ^ 6 + 91010 * X ^ 5 - 9090 * X ^ 4 - 90 * X ^ 3 + 110 * X ^ 2 - 10 * X + 1) := by
  sorry

end OMA.S_oeis_a284348
