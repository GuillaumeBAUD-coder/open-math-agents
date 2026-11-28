import Mathlib

/-!
# The recurrence recorded in OEIS A099576

Source: https://oeis.org/A099576
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A099/A099576.seq
Credit: @Heart-galaxy

The sequence is given by the double sum over 0 ≤ k ≤ n and
0 ≤ j ≤ floor(k/2) of the binomial coefficient C(n+j,j).
The sequence starts at index 0, so the recurrence starts at index 2.
R. J. Mathar proposed the recurrence in 2014. Robert Israel resolved it
in the OEIS entry in 2018 using separate binomial formulas for even and
odd indices.
-/

namespace OMA.S_oeis_a099576

open Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), ∑ j ∈ range (k / 2 + 1), (n + j).choose j

theorem main : ∀ n : ℕ, 2 ≤ n →
    4 * (n : ℤ) * ((n : ℤ) - 1) * (3 * (n : ℤ) + 2) * ((n : ℤ) + 2) * (a n : ℤ) -
      36 * ((n : ℤ) - 1) * ((n : ℤ) + 1) * (a (n - 1) : ℤ) -
      3 * (n : ℤ) * (3 * (n : ℤ) + 5) * (3 * (n : ℤ) - 1) *
        (3 * (n : ℤ) - 2) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a099576
