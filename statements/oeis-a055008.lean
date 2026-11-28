import Mathlib

/-!
# OEIS A055008: numbers with gcd(φ(k), σ(k)) = 1

Source: https://oeis.org/A055008
Credit: @SudharsanAnimations

A055008 lists the numbers `k` with `gcd(φ(k), σ(k)) = 1`. The entry conjectures that every term is
a square or twice a square, and records the proof (Amiram Eldar, Jason Yuen): if `k` is neither,
then `σ(k)` is even, so `φ(k)` would have to be odd, which happens only for `k = 1, 2`. We state
this proved result.

Conventions: `φ` is `Nat.totient`, `σ` is `ArithmeticFunction.sigma 1` (sum of divisors);
"twice a square" means `k = 2 m²` for some natural `m`. (For `k = 0`, `gcd(φ 0, σ 0) = 0`, so
`0` is not a term.)
-/

namespace OMA.S_oeis_a055008
open ArithmeticFunction

theorem main : ∀ k : ℕ, Nat.gcd k.totient (ArithmeticFunction.sigma 1 k) = 1 → IsSquare k ∨ ∃ m, k = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a055008
