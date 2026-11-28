import Mathlib

/-!
# A069972: a(n) = Sum_{d|2*n,d+1|2*n} d.

Source: https://oeis.org/A069972
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 1, 3, 1, 1, 6, 1, 1, 3, 5, 1, 6, ...
It is defined as in the name of the entry: the sum of the d such that both d and d+1 divide 2n.

Conjecture (Joerg Arndt, Jan 30 2011):
G.f.: Sum_{n>=1} n*x^(n*(n+1)/2)/(1-x^(n*(n+1)/2)).
The right-hand side is an infinite sum of power series in which the k-th term has order k*(k+1)/2,
so its coefficient of x^N is the coefficient of x^N in any partial sum with at least N terms.
The claim that it is the generating function Sum_{n>=1} a(n) x^n is therefore stated as: for all
N <= K, the coefficient of x^N in the K-th partial sum G K is a(N) (and 0 for N = 0).
-/

namespace OMA.S_oeis_a069972

open PowerSeries

/-- A069972: the sum of the d such that both d and d+1 divide 2n. -/
def a (n : ℕ) : ℕ := ∑ d ∈ (2 * n).divisors with (d + 1) ∣ 2 * n, d

/-- The K-th partial sum of Sum_{k>=1} k*x^(k*(k+1)/2)/(1-x^(k*(k+1)/2)). -/
noncomputable def G (K : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.Icc 1 K,
    PowerSeries.C (k : ℚ) * X ^ (k * (k + 1) / 2) * (1 - X ^ (k * (k + 1) / 2))⁻¹

/-- The conjectured generating function for A069972. -/
theorem main : ∀ N K : ℕ, N ≤ K →
    PowerSeries.coeff N (G K) = if N = 0 then 0 else (a N : ℚ) := by
  sorry

end OMA.S_oeis_a069972
