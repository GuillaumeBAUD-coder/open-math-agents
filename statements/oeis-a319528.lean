import Mathlib

/-!
# OEIS A319528: 8 σ(n) = σ(7n) exactly when 7 ∤ n

Source: https://oeis.org/A319528
Credit: @SudharsanAnimations

`A319528(n) = 8 σ(n)`. Charlie Neder conjectured that `a(n) = σ(7n)` (`= A283078(n)`) if and only if
`n` is not a multiple of `7`. The entry records that this is true: if `gcd(7, n) = 1` then
`σ(7n) = σ(7) σ(n) = 8 σ(n)` by multiplicativity. We state this proved result, both directions, for
`n ≥ 1` (offset `1`).

Conventions: `σ` is `ArithmeticFunction.sigma 1`, the sum of divisors.
-/

namespace OMA.S_oeis_a319528

/-- `A319528(n) = 8 σ(n)`. -/
def a (n : ℕ) : ℕ := 8 * ArithmeticFunction.sigma 1 n

theorem main : ∀ n : ℕ, 1 ≤ n → (a n = ArithmeticFunction.sigma 1 (7 * n) ↔ ¬ 7 ∣ n) := by
  sorry

end OMA.S_oeis_a319528
