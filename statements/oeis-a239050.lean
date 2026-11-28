import Mathlib

/-!
# OEIS A239050: 4 σ(n) = σ(3n) iff 3 ∤ n

Source: https://oeis.org/A239050
Credit: @SudharsanAnimations

`A239050(n) = 4 σ(n)`. The entry's conjecture "a(n) = sigma(3n) = A144613(n) iff n is not a multiple
of 3" is recorded as correct (write `n = 3^e m` with `3 ∤ m`; then
`σ(3n) = ((3^(e+2) - 1)/2) σ(m)`). We state the proved result for all `n ≥ 1`.

Conventions: `σ = ArithmeticFunction.sigma 1` (sum of divisors).
-/

namespace OMA.S_oeis_a239050

/-- `A239050(n) = 4 σ(n)`. -/
def a (n : ℕ) : ℕ := 4 * ArithmeticFunction.sigma 1 n

theorem main : ∀ n : ℕ, 1 ≤ n → (a n = ArithmeticFunction.sigma 1 (3 * n) ↔ ¬ 3 ∣ n) := by
  sorry

end OMA.S_oeis_a239050
