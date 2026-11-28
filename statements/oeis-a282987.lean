import Mathlib

/-!
# A282987: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 541', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282987
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 17*a(n-4) - 16*a(n-8) for n > 33.
* G.f.: (-2097152*x^33 - 1572864*x^32 + 59506688*x^31 + 12320768*x^30 - 44826624*x^29 + 14155776*x^28 - 53215232*x^27 - 17432576*x^26 + 45219840*x^25 - 10813440*x^24 - 6619136*x^23 + 5636096*x^22 - 1802240*x^21 - 622592*x^20 + 770048*x^19 - 73728*x^18 - 4096*x^17 + 86016*x^16 - 20480*x^15 - 14336*x^14 - 3072*x^13 - 512*x^12 - 256*x^11 - 256*x^10 + 640*x^9 - 32*x^8 - 16*x^7 + 88*x^6 - 8*x^5 - 8*x^4 + 9*x^3 + x^2 + x + 1)/(16*x^8 - 17*x^4 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a282987

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

/-- A282987(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 541 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 34 ≤ n → (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) = -2097152 * X ^ 33 - 1572864 * X ^ 32 + 59506688 * X ^ 31 + 12320768 * X ^ 30 - 44826624 * X ^ 29 + 14155776 * X ^ 28 - 53215232 * X ^ 27 - 17432576 * X ^ 26 + 45219840 * X ^ 25 - 10813440 * X ^ 24 - 6619136 * X ^ 23 + 5636096 * X ^ 22 - 1802240 * X ^ 21 - 622592 * X ^ 20 + 770048 * X ^ 19 - 73728 * X ^ 18 - 4096 * X ^ 17 + 86016 * X ^ 16 - 20480 * X ^ 15 - 14336 * X ^ 14 - 3072 * X ^ 13 - 512 * X ^ 12 - 256 * X ^ 11 - 256 * X ^ 10 + 640 * X ^ 9 - 32 * X ^ 8 - 16 * X ^ 7 + 88 * X ^ 6 - 8 * X ^ 5 - 8 * X ^ 4 + 9 * X ^ 3 + X ^ 2 + X + 1) := by
  sorry

end OMA.S_oeis_a282987
