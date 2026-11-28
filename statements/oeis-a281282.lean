import Mathlib

/-!
# A281282: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 350', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281282
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10001*a(n-4) - 10000*a(n-8) for n > 23.
* G.f.: (9900000000000000*x^23 + 9010000000000000*x^22 - 1000000000000000*x^21 - 11000000000000*x^20 - 9999000000000000*x^19 - 9000000000000000*x^18 + 1000000000000000*x^17 + 11011100000000*x^16 - 101100000000*x^15 - 100000000000*x^14 - 11000000000*x^12 + 1100000000*x^11 + 9000000000*x^10 + 90000000*x^9 - 109000000*x^8 + 890000*x^7 + 1000*x^6 - 109000*x^5 + 1010*x^4 + 1011*x^3 + 11*x^2 + 11*x + 1)/(10000*x^8 - 10001*x^4 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281282

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

/-- A281282(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 350 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = 10001 * a (n - 4) - 10000 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 8 - 10001 * X ^ 4 + 1 : PowerSeries ℚ) = 9900000000000000 * X ^ 23 + 9010000000000000 * X ^ 22 - 1000000000000000 * X ^ 21 - 11000000000000 * X ^ 20 - 9999000000000000 * X ^ 19 - 9000000000000000 * X ^ 18 + 1000000000000000 * X ^ 17 + 11011100000000 * X ^ 16 - 101100000000 * X ^ 15 - 100000000000 * X ^ 14 - 11000000000 * X ^ 12 + 1100000000 * X ^ 11 + 9000000000 * X ^ 10 + 90000000 * X ^ 9 - 109000000 * X ^ 8 + 890000 * X ^ 7 + 1000 * X ^ 6 - 109000 * X ^ 5 + 1010 * X ^ 4 + 1011 * X ^ 3 + 11 * X ^ 2 + 11 * X + 1) := by
  sorry

end OMA.S_oeis_a281282
