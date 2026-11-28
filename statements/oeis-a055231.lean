import Mathlib

/-!
# OEIS A055231: a(nm) = a(n) a(m) / (gcd(n, a(m)) gcd(m, a(n)))

Source: https://oeis.org/A055231
Credit: @SudharsanAnimations

A055231(n) is the powerfree part of `n`: the product of the primes that divide `n` exactly once.
Velin Yanev conjectured (Feb 2019) that `a(nm) = a(n) a(m) / (gcd(n, a(m)) gcd(m, a(n)))` for all
`n, m > 0`; N. J. A. Sloane noted (Mar 2019) that this follows easily from the multiplicativity of
`a` (`a(p) = p`, `a(p^e) = 1` for `e > 1`). We state the proved identity.

Conventions: `a(n) = ∏ p` over the primes `p` with `p`-adic valuation `1` in `n`; `/` is
natural-number division (exact here).
-/

namespace OMA.S_oeis_a055231

/-- A055231: the powerfree part of `n`, the product of the primes that divide `n` exactly once. -/
def a (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

theorem main : ∀ n m : ℕ, 0 < n → 0 < m →
    a (n * m) = a n * a m / (Nat.gcd n (a m) * Nat.gcd m (a n)) := by
  sorry

end OMA.S_oeis_a055231
