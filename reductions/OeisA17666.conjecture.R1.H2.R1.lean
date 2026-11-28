import OMAReductions.R_OeisA17666_conjecture_R1

-- Reduction OeisA17666.conjecture.R1.H2.R1 of step OeisA17666.conjecture.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd multiply perfect numbers: at most six prime factors, and the open rest

The parent step says that no odd `b > 1` has `σ(b) = k * b` with `k ≥ 3`: there is no odd
multiply perfect number of abundancy three or more, which is open.

* `H1` (elementary): such a `b` has at least seven distinct prime factors. For any `n`,
  `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`. If these are `r` distinct odd
  numbers `≥ 3`, then `∏ p / (p - 1)` is at most `(3/2)(5/4)⋯((2r+1)/(2r))` (remove the largest
  element, which is at least `2r + 1`), and for `r ≤ 6` this is `135135 / 46080 < 3`.
* `H2`: no such `b` with seven or more distinct prime factors. This is the open problem and
  stays open.
-/

namespace OMA.R_OeisA17666_conjecture_R1_H2_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- An odd multiply perfect number of abundancy at least three has at least seven distinct
prime factors. -/
def H1 : Prop :=
  ∀ b k : ℕ, 1 < b → Odd b → 3 ≤ k → b.primeFactors.card ≤ 6 → σ 1 b ≠ k * b

/-- The open part: seven or more distinct prime factors. -/
def H2 : Prop :=
  ∀ b k : ℕ, 1 < b → Odd b → 3 ≤ k → 7 ≤ b.primeFactors.card → σ 1 b ≠ k * b

theorem main : H1 → H2 → OMA.R_OeisA17666_conjecture_R1.H2 := by
  intro h1 h2 b k hb hodd hk
  by_cases hc : b.primeFactors.card ≤ 6
  · exact h1 b k hb hodd hk hc
  · exact h2 b k hb hodd hk (by omega)

end OMA.R_OeisA17666_conjecture_R1_H2_R1
