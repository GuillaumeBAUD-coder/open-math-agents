import OMAReductions.R_OeisA108569_conjecture_R2

-- Reduction OeisA108569.conjecture.R2.H1.R1 of step OeisA108569.conjecture.R2.H1
-- Credit: @marcusbuffett

/-!
# Odd primes in A108569: at most two prime factors of `2p - 1`, and the open rest

The parent step says that no odd prime `p` has `φ(p) = φ(p + φ(p))`, that is `φ(2p - 1) = p - 1`.
With `m = 2p - 1` this reads `2 φ(m) = m - 1`, a case of Lehmer's totient problem, which is open.

* `H1` (elementary): `m = p + φ(p)` then has at least three distinct prime factors. From
  `φ(m) * ∏ q = m * ∏ (q - 1)` over the primes `q` dividing `m`, the equation `2 φ(m) = m - 1`
  gives `2 * ∏ (q - 1) < ∏ q`; for `r` distinct odd numbers `≥ 3` the product of `q / (q - 1)` is
  at most `(3/2)(5/4)⋯((2r+1)/(2r))`, which is below `2` for `r ≤ 2`.
* `H2`: the case of three or more distinct prime factors, which stays open.
-/

namespace OMA.R_OeisA108569_conjecture_R2_H1_R1

/-- If `p + φ(p)` has at most two distinct prime factors there is no collision. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → (p + p.totient).primeFactors.card ≤ 2 →
    p.totient ≠ (p + p.totient).totient

/-- The open part: three or more distinct prime factors. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → 3 ≤ (p + p.totient).primeFactors.card →
    p.totient ≠ (p + p.totient).totient

theorem main : H1 → H2 → OMA.R_OeisA108569_conjecture_R2.H1 := by
  intro h1 h2 p hp hodd
  by_cases hc : (p + p.totient).primeFactors.card ≤ 2
  · exact h1 p hp hodd hc
  · exact h2 p hp hodd (by omega)

end OMA.R_OeisA108569_conjecture_R2_H1_R1
