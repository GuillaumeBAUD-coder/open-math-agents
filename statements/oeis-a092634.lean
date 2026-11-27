import Mathlib

/-!
# A092634: a(n) = 1 - Sum_{k=2..n} k*k!.

Source: https://oeis.org/A092634
Credit: @marcelopierry

Conjecture (R. J. Mathar, Sep 27 2014, in the formulas of A092634):
a(n) + (-n-3)*a(n-1) + (2*n+1)*a(n-2) + (-n+1)*a(n-3) = 0.

Conventions:
* The sequence has offset 2 (data -3, -21, -117, -717, -5037, ...); it is computed in the
  integers.
* The recurrence involves a(n-3), so it is stated for n >= 5, where all four terms lie in the
  range of the sequence.
-/

namespace OMA.S_oeis_a092634

/-- A092634(n) = 1 - Sum_{k=2..n} k*k!. -/
def a (n : ℕ) : ℤ := 1 - ∑ k ∈ Finset.Icc 2 n, (k : ℤ) * (k.factorial : ℤ)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-(n : ℤ) - 3) * a (n - 1) + (2 * (n : ℤ) + 1) * a (n - 2) +
      (-(n : ℤ) + 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a092634
