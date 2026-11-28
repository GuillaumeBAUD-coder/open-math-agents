import Mathlib

/-!
# A386829: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(2*n+1,k) * binomial(2*n-k,n-k).

Source: https://oeis.org/A386829
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 13, 204, 3457, 61006, 1103598, 20299434, 377871297, 7097430726, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 2*n*a(n) +(-31*n+20)*a(n-1) +90*(-2*n+1)*a(n-2)=0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a386829

/-- A386829: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(2*n+1,k) * binomial(2*n-k,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) * ((2 * n + 1).choose k : ℤ) * ((2 * n - k).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386829. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (2 * (n : ℤ)) * a n
      + (-31 * (n : ℤ) + 20) * a (n - 1)
      + (-180 * (n : ℤ) + 90) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a386829
