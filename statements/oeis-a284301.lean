import Mathlib

/-!
# A284301: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 865', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284301
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2) + 256*a(n-8) - 256*a(n-10) for n > 36.
* G.f.: (16384*x^36 + 2048*x^35 - 11264*x^34 - 2048*x^33 - 768*x^32 + 512*x^31 - 256*x^30 + 1536*x^29 - 4160*x^28 - 2056*x^27 + 44*x^26 + 8*x^25 + 3*x^24 - 2*x^23 + x^22 - 38*x^21 + 16*x^20 + 8*x^19 - 96*x^17 - 416*x^13 + 256*x^12 + 152*x^11 - x^10 + 358*x^9 - 127*x^8 + 90*x^7 + 32*x^6 + 24*x^5 + 7*x^4 + 5*x^3 + 2*x^2 + 1)/(256*x^10 - 256*x^8 - x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284301

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

/-- A284301(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 865 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 37 ≤ n → (a n : ℚ) = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (256 * X ^ 10 - 256 * X ^ 8 - X ^ 2 + 1 : PowerSeries ℚ) = 16384 * X ^ 36 + 2048 * X ^ 35 - 11264 * X ^ 34 - 2048 * X ^ 33 - 768 * X ^ 32 + 512 * X ^ 31 - 256 * X ^ 30 + 1536 * X ^ 29 - 4160 * X ^ 28 - 2056 * X ^ 27 + 44 * X ^ 26 + 8 * X ^ 25 + 3 * X ^ 24 - 2 * X ^ 23 + X ^ 22 - 38 * X ^ 21 + 16 * X ^ 20 + 8 * X ^ 19 - 96 * X ^ 17 - 416 * X ^ 13 + 256 * X ^ 12 + 152 * X ^ 11 - X ^ 10 + 358 * X ^ 9 - 127 * X ^ 8 + 90 * X ^ 7 + 32 * X ^ 6 + 24 * X ^ 5 + 7 * X ^ 4 + 5 * X ^ 3 + 2 * X ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a284301
