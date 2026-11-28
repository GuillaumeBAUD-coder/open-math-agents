import Mathlib

/-!
# OEIS A327123

Expansion of `Sum_{k >= 1} phi(k) * x^k / (1 + x^(2 * k))`:
`a(n) = Sum_{k ∣ n, (n / k) odd} (-1)^(((n / k) - 1) / 2) * phi(k)`.

Conjecture (Velin Yanev and Vaclav Kotesovec, Jun 01 2024):
`a(n) = Sum_{k = 1..n} sin(gcd(k, n) * pi / 2)` for all `n >= 1`.
-/

namespace OMA.S_oeis_a327123

/-- Coefficient of `x^n` in `Sum_{k >= 1} phi(k) * x^k / (1 + x^(2 * k))`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ n.divisors,
    if (n / k) % 2 = 1 then (-1 : ℤ) ^ ((n / k - 1) / 2) * (Nat.totient k : ℤ) else 0

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = ∑ k ∈ Finset.Icc 1 n, Real.sin ((Nat.gcd k n : ℝ) * Real.pi / 2) := by
  sorry

end OMA.S_oeis_a327123
