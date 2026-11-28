import Mathlib

/-!
# A284299: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 865', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284299
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2) + 100000000*a(n-8) - 100000000*a(n-10) for n > 36.
* G.f.: (100000000000000*x^36 + 100000000000*x^35 - 98990000000000*x^34 - 100000000000*x^33 - 9900000000*x^32 + 1000000000*x^31 - 100000000*x^30 + 99000000000*x^29 - 1000001000000*x^28 - 100000001000*x^27 + 989900*x^26 + 1000*x^25 + 99*x^24 - 10*x^23 + x^22 - 100990*x^21 + 10000*x^20 + 1000*x^19 - 9900000*x^17 - 990100000*x^13 + 100000000*x^12 + 890099000*x^11 - x^10 + 109900990*x^9 - 89999999*x^8 + 1099010*x^7 + 100000*x^6 + 11000*x^5 + 999*x^4 + 101*x^3 + 10*x^2 + 1)/(100000000*x^10 - 100000000*x^8 - x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284299

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

/-- A284299(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 865 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 37 ≤ n → (a n : ℚ) = a (n - 2) + 100000000 * a (n - 8) - 100000000 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (100000000 * X ^ 10 - 100000000 * X ^ 8 - X ^ 2 + 1 : PowerSeries ℚ) = 100000000000000 * X ^ 36 + 100000000000 * X ^ 35 - 98990000000000 * X ^ 34 - 100000000000 * X ^ 33 - 9900000000 * X ^ 32 + 1000000000 * X ^ 31 - 100000000 * X ^ 30 + 99000000000 * X ^ 29 - 1000001000000 * X ^ 28 - 100000001000 * X ^ 27 + 989900 * X ^ 26 + 1000 * X ^ 25 + 99 * X ^ 24 - 10 * X ^ 23 + X ^ 22 - 100990 * X ^ 21 + 10000 * X ^ 20 + 1000 * X ^ 19 - 9900000 * X ^ 17 - 990100000 * X ^ 13 + 100000000 * X ^ 12 + 890099000 * X ^ 11 - X ^ 10 + 109900990 * X ^ 9 - 89999999 * X ^ 8 + 1099010 * X ^ 7 + 100000 * X ^ 6 + 11000 * X ^ 5 + 999 * X ^ 4 + 101 * X ^ 3 + 10 * X ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a284299
