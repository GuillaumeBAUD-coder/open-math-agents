import Mathlib

/-!
# A287129: Binary representation of the diagonal from the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 245', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A287129
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: (1 + 10*x - 101*x^2 + 100*x^3 + 111*x^4 - 1100*x^6 - 10*x^7 + 1000*x^9) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
* a(n) = 11 for n>5 and even.
* a(n) = 10*(10^n - 10)/9 for n>5 and odd.

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (n, n), (n - 1, n - 1), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a287129

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

/-- A287129(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (n, n), (n - 1, n - 1), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 245 n ((n : ℤ) - k) ((n : ℤ) - k) then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) = 1 + 10 * X - 101 * X ^ 2 + 100 * X ^ 3 + 111 * X ^ 4 - 1100 * X ^ 6 - 10 * X ^ 7 + 1000 * X ^ 9) ∧
    (∀ n : ℕ, 6 ≤ n → Even n → (a n : ℚ) = 11) ∧
    (∀ n : ℕ, 6 ≤ n → Odd n → (a n : ℚ) = 10 * ((10 : ℚ) ^ n - 10) / 9) := by
  sorry

end OMA.S_oeis_a287129
