import Mathlib

/-!
# A092634: a(n) = 1 - Sum_{k=2..n} k*k!.

Source: https://oeis.org/A092634
Credit: @agchua

R. J. Mathar (Sep 27 2014), in the formula section of A092634:
  Conjecture: a(n) +(-n-3)*a(n-1) +(2*n+1)*a(n-2) +(-n+1)*a(n-3)=0.
The sequence has offset 2 (its first term is a(2) = -3). The recurrence uses a(n-3), so the
conjecture is stated for n ≥ 5, the range in which a(n), a(n-1), a(n-2), a(n-3) are all terms
of the sequence. The sum runs over the integers k with 2 ≤ k ≤ n; the terms are integers (ℤ).
-/

namespace OMA.S_oeis_a092634

/-- A092634(n) = 1 - Sum_{k=2..n} k*k!. -/
def a (n : ℕ) : ℤ := 1 - ∑ k ∈ Finset.Icc 2 n, (k : ℤ) * (k.factorial : ℤ)

/-- Mathar's conjecture: for n ≥ 5, a(n) - (n+3) a(n-1) + (2n+1) a(n-2) - (n-1) a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-(n : ℤ) - 3) * a (n - 1) + (2 * (n : ℤ) + 1) * a (n - 2)
      + (-(n : ℤ) + 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a092634
