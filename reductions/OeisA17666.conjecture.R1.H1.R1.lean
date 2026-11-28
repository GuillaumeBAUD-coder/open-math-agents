import OMAReductions.R_OeisA17666_conjecture_R1

-- Reduction OeisA17666.conjecture.R1.H1.R1 of step OeisA17666.conjecture.R1.H1
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers: at most two prime factors, and the open rest

The parent step says that no odd number greater than one is perfect, which is the odd perfect
number problem.

* `H1` (classical): an odd perfect number has at least three distinct prime factors. For any
  `n`, the divisor sum satisfies `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the primes dividing `n`, so
  `σ(n) = 2n` forces `2 * ∏ (p - 1) ≤ ∏ p`, which fails for one or two odd primes.
* `H2`: no odd perfect number has three or more distinct prime factors. This is the open
  problem and stays open (the literature has at least ten distinct prime factors, Nielsen 2015,
  by far longer case analyses).
-/

namespace OMA.R_OeisA17666_conjecture_R1_H1_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- No odd perfect number has at most two distinct prime factors. -/
def H1 : Prop :=
  ∀ b : ℕ, 1 < b → Odd b → b.primeFactors.card ≤ 2 → σ 1 b ≠ 2 * b

/-- The open part: no odd perfect number has three or more distinct prime factors. -/
def H2 : Prop :=
  ∀ b : ℕ, 1 < b → Odd b → 3 ≤ b.primeFactors.card → σ 1 b ≠ 2 * b

theorem main : H1 → H2 → OMA.R_OeisA17666_conjecture_R1.H1 := by
  intro h1 h2 b hb hodd
  by_cases hc : b.primeFactors.card ≤ 2
  · exact h1 b hb hodd hc
  · exact h2 b hb hodd (by omega)

end OMA.R_OeisA17666_conjecture_R1_H1_R1
