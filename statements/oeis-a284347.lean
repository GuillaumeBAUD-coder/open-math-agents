import Mathlib

/-!
# A284347: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 873', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284347
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-1) + 100000000*a(n-8) - 100000000*a(n-9) for n > 23.
* G.f.: (-100000000*x^23 - 900000000*x^22 - 9100000000*x^21 - 90900000000*x^20 + 91000000000*x^19 + 10000000000*x^18 - 10099999999*x^15 + 9100000009*x^14 + 900000091*x^13 + 100000909*x^12 - 910*x^11 - 99999100*x^10 + 201009000*x^9 - 90910000*x^8 + 900101*x^7 + 99909*x^6 + 10091*x^5 + 909*x^4 + 90*x^3 + 11*x^2 - x + 1)/(100000000*x^9 - 100000000*x^8 - x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284347

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

/-- A284347(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 873 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = a (n - 1) + 100000000 * a (n - 8) - 100000000 * a (n - 9)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (100000000 * X ^ 9 - 100000000 * X ^ 8 - X + 1 : PowerSeries ℚ) = -100000000 * X ^ 23 - 900000000 * X ^ 22 - 9100000000 * X ^ 21 - 90900000000 * X ^ 20 + 91000000000 * X ^ 19 + 10000000000 * X ^ 18 - 10099999999 * X ^ 15 + 9100000009 * X ^ 14 + 900000091 * X ^ 13 + 100000909 * X ^ 12 - 910 * X ^ 11 - 99999100 * X ^ 10 + 201009000 * X ^ 9 - 90910000 * X ^ 8 + 900101 * X ^ 7 + 99909 * X ^ 6 + 10091 * X ^ 5 + 909 * X ^ 4 + 90 * X ^ 3 + 11 * X ^ 2 - X + 1) := by
  sorry

end OMA.S_oeis_a284347
