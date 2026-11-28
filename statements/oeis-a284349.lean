import Mathlib

/-!
# A284349: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 873', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284349
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-1) + 256*a(n-8) - 256*a(n-9) for n > 23.
* G.f.: (-256*x^23 - 256*x^22 - 768*x^21 - 1280*x^20 + 1536*x^19 + 1024*x^18 - 1279*x^15 + 769*x^14 + 259*x^13 + 261*x^12 - 6*x^11 - 252*x^10 + 584*x^9 - 176*x^8 + 37*x^7 + 29*x^6 + 19*x^5 + 5*x^4 + 2*x^3 + 3*x^2 - x + 1)/(256*x^9 - 256*x^8 - x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284349

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

/-- A284349(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 873 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = a (n - 1) + 256 * a (n - 8) - 256 * a (n - 9)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (256 * X ^ 9 - 256 * X ^ 8 - X + 1 : PowerSeries ℚ) = -256 * X ^ 23 - 256 * X ^ 22 - 768 * X ^ 21 - 1280 * X ^ 20 + 1536 * X ^ 19 + 1024 * X ^ 18 - 1279 * X ^ 15 + 769 * X ^ 14 + 259 * X ^ 13 + 261 * X ^ 12 - 6 * X ^ 11 - 252 * X ^ 10 + 584 * X ^ 9 - 176 * X ^ 8 + 37 * X ^ 7 + 29 * X ^ 6 + 19 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 - X + 1) := by
  sorry

end OMA.S_oeis_a284349
