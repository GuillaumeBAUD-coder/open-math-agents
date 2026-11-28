import Mathlib

/-!
# OEIS A187035: the recurrence a(n) = a(n-2) - a(n-3) + a(n-5)

Source: https://oeis.org/A187035
Credit: @SudharsanAnimations

A187035 is the sequence of diagonal sums of the number triangle A187034, where
`T(n, k) = (-1)^(n-k)` if `binomial(k, n-k) > 0` and `0` otherwise (`0 ≤ k ≤ n`). R. J. Mathar
conjectured (Jun 2011) the g.f. `1/((1-x)(1-x+x^2)(1+x)^2)` with `a(n) = a(n-2) - a(n-3) + a(n-5)`;
Charles R Greathouse IV recorded (Dec 2011) that the conjecture is correct. We state the recurrence
for all `n ≥ 5` (the g.f. is equivalent to it given the initial terms).

Conventions: offset `0`; diagonal sums `a(n) = ∑_{k=0}^{⌊n/2⌋} T(n-k, k)`, written as a sum over
`k ≤ n` since the terms with `k > n/2` vanish.
-/

namespace OMA.S_oeis_a187035

/-- A187034: `T(n, k) = (-1)^(n-k)` if `binomial(k, n-k) > 0`, `0` otherwise, for `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℤ := if k ≤ n ∧ 0 < Nat.choose k (n - k) then (-1) ^ (n - k) else 0

/-- A187035: the diagonal sums `a(n) = ∑_{k=0}^{⌊n/2⌋} T(n - k, k)` (terms with `k > n/2` vanish). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T (n - k) k

theorem main : ∀ n : ℕ, 5 ≤ n → a n = a (n - 2) - a (n - 3) + a (n - 5) := by
  sorry

end OMA.S_oeis_a187035
