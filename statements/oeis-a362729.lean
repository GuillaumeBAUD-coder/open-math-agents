import Mathlib

/-!
# OEIS A362729: a(n) = [x^n] ( E(x)/E(-x) )^n, E(x) = exp( Sum_{k >= 1} A108628(k-1)*x^k/k )

Source: https://oeis.org/A362729
Credit: @LordMike

A362729: a(n) = [x^n] ( E(x)/E(-x) )^n where E(x) = exp( Sum_{k >= 1} A108628(k-1)*x^k/k ).

Conjecture: a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) for primes p >= 7 and positive integers n and r.

Reading used here: offset 0 (a(0) = 1, a(1) = 2, a(2) = 8, a(3) = 146, ...). A108628(n) =
Sum_{k=0..n} C(n,k)*C(n+1,k)*C(n+k+1,k) (OEIS Maple code), so 1, 7, 55, 471, ... The series are in `ℚ⟦X⟧`;
the `k = 0` coefficient of the exponent is `c 0 / 0 = 0` in Lean, as required. The congruence is stated as
"the difference is `p^(3r)` times an integer" (the terms are integers).
-/

namespace OMA.S_oeis_a362729

/-- A108628(n) = Sum_{k=0..n} C(n,k)*C(n+1,k)*C(n+k+1,k). -/
def c (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n + 1).choose k * (n + k + 1).choose k

/-- E(x) = exp( Sum_{k >= 1} A108628(k-1)*x^k/k ). -/
noncomputable def E : PowerSeries ℚ := (PowerSeries.exp ℚ).subst (PowerSeries.mk fun k => (c (k - 1) : ℚ) / k)

/-- a(n) = [x^n] ( E(x)/E(-x) )^n. -/
noncomputable def a (n : ℕ) : ℚ := PowerSeries.coeff n ((E * (PowerSeries.evalNegHom E)⁻¹) ^ n)

theorem main : ∀ p n r : ℕ, p.Prime → 7 ≤ p → 0 < n → 0 < r →
    ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a362729
