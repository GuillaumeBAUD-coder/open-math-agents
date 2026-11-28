import Mathlib

/-!
# A284302: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 865', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284302
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 4*a(n-2) + a(n-8) - 4*a(n-10) for n > 36.
* G.f.: (4194304*x^36 + 16777216*x^35 + 19922944*x^34 - 4194304*x^33 + 12582912*x^32 + 4194304*x^31 - 4194304*x^30 - 786432*x^29 - 4259840*x^28 - 16842752*x^27 - 19922944*x^26 + 4194304*x^25 - 12582912*x^24 - 4194304*x^23 + 4194304*x^22 + 720896*x^21 + 65536*x^20 + 65536*x^19 + 3072*x^17 - 208*x^13 + 16*x^12 - 212*x^11 - 1024*x^10 - 202*x^9 + 257*x^8 + 54*x^7 + 2*x^6 + 6*x^5 - 14*x^4 + 10*x^3 + 2*x^2 + 1)/(4*x^10 - x^8 - 4*x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284302

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

/-- A284302(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 865 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 37 ≤ n → (a n : ℚ) = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (4 * X ^ 10 - X ^ 8 - 4 * X ^ 2 + 1 : PowerSeries ℚ) = 4194304 * X ^ 36 + 16777216 * X ^ 35 + 19922944 * X ^ 34 - 4194304 * X ^ 33 + 12582912 * X ^ 32 + 4194304 * X ^ 31 - 4194304 * X ^ 30 - 786432 * X ^ 29 - 4259840 * X ^ 28 - 16842752 * X ^ 27 - 19922944 * X ^ 26 + 4194304 * X ^ 25 - 12582912 * X ^ 24 - 4194304 * X ^ 23 + 4194304 * X ^ 22 + 720896 * X ^ 21 + 65536 * X ^ 20 + 65536 * X ^ 19 + 3072 * X ^ 17 - 208 * X ^ 13 + 16 * X ^ 12 - 212 * X ^ 11 - 1024 * X ^ 10 - 202 * X ^ 9 + 257 * X ^ 8 + 54 * X ^ 7 + 2 * X ^ 6 + 6 * X ^ 5 - 14 * X ^ 4 + 10 * X ^ 3 + 2 * X ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a284302
