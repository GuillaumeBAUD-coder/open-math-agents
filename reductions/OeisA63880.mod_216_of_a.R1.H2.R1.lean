import OMAReductions.R_OeisA63880_mod_216_of_a_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H2.R1 of step OeisA63880.mod_216_of_a.R1.H2
-- Credit: @Ciphore
-- Writing the Mersenne equation as `(2^k - 1) * σ(m) = (2^k + 2) * usigma(m)`, the
-- coprimality structure of the two multipliers is the first obstruction:
-- `gcd(2^k - 1, 2^k + 2)` is `3` when `k` is even and `1` when `k` is odd, since
-- `2^k ≡ (-1)^k (mod 3)`. The two divisibility regimes are independent arithmetic cores.

/-!
## Reduction of the Mersenne-multiplier step

The equation `(2^k - 1) * (σ(m) - usigma(m)) = 3 * usigma(m)` rearranges to
`(2^k - 1) * σ(m) = (2^k + 2) * usigma(m)`. The two multipliers differ by `3`, so their
gcd divides `3`; it equals `3` exactly when `k` is even. For odd `k` the multipliers are
coprime and `2^k - 1` must divide the unitary divisor sum outright; for even `k` the
shared factor `3` interacts with the right-hand side. The split by the parity of `k`
separates these regimes.
-/

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H2_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The even-exponent case of the Mersenne-multiplier step: `3` divides `2^k - 1`, so the
    3-adic valuation of the two sides of the equation is the binding constraint. -/
def H1 : Prop := ∀ m k : ℕ, Odd m → 4 ≤ k → Even k →
  (2 ^ k - 1) * (σ 1 m - usigma m) ≠ 3 * usigma m

/-- The odd-exponent case of the Mersenne-multiplier step: `2^k - 1` is coprime to `3`,
    so the factor `3` on the right must be absorbed by the unitary divisor sum. -/
def H2 : Prop := ∀ m k : ℕ, Odd m → 4 ≤ k → Odd k →
  (2 ^ k - 1) * (σ 1 m - usigma m) ≠ 3 * usigma m

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1.H2 := by
  intro heven hodd m k hom hk4
  by_cases hk : Even k
  · exact heven m k hom hk4 hk
  · exact hodd m k hom hk4 (Nat.not_even_iff_odd.mp hk)

end OMA.R_OeisA63880_mod_216_of_a_R1_H2_R1
