import Mathlib

/-!
# OEIS A362727: supercongruences for [x^n] (E(x)/E(-x))^n

Source: https://oeis.org/A362727
Credit: @LordMike

a(n) = [x^n] ( E(x)/E(-x) )^n where E(x) = exp( Sum_{k >= 1} A208675(k)*x^k/k ).

Conjecture: the supercongruence a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) holds for all primes p >= 7 and positive
integers n and r.

Reading used here: A208675(k) = Sum_{j = 0..k-1} (-1)^j*binomial(k-1,j)*binomial(2*k-j-1,k-j)^2 (the OEIS Maple
formula). Since E(x)/E(-x) = exp(S) with S = 2*Sum_{k odd} A208675(k)*x^k/k (as in the OEIS Maple program),
a(n) = [x^n] exp(n*S) = Sum_{j = 0..n} n^j/j! * [x^n] S^j, computed over ℚ (offset 0, a(0) = 1, a(1) = 2).
The congruence is stated as: the difference is p^(3r) times an integer.
-/

namespace OMA.S_oeis_a362727

/-- `a n = [x^n] (E(x)/E(-x))^n` over `ℚ`, expanding `exp(n*S)` with `S = 2 * ∑_{k odd} A208675(k) x^k / k`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (n : ℚ) ^ j / j.factorial * PowerSeries.coeff n
    ((PowerSeries.mk fun k => if Odd k then 2 * (∑ i ∈ Finset.range k, (-1 : ℚ) ^ i * (k - 1).choose i *
      ((2 * k - i - 1).choose (k - i) : ℚ) ^ 2) / k else 0) ^ j)

theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ n r : ℕ, 0 < n → 0 < r →
    ∃ m : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * m := by
  sorry

end OMA.S_oeis_a362727
