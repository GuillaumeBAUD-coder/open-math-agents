import Mathlib

/-!
# OEIS A090523: no zeros for n > 2

Source: https://oeis.org/A090523
Credit: @SudharsanAnimations

A090523(n) is the smallest prime p such that floor(n!/p) is prime, or 0 if no such prime exists.
The entry's conjecture "there are no zeros for n > 2" is recorded as correct (Franklin T. Adams-Watters,
Jul 2011): by Bertrand's postulate there is a prime p with n!/4 < p <= n!/2, and then floor(n!/p) is
2 or 3. We state the proved result: for every n > 2 such a prime exists.

Conventions: `/` is natural-number (floor) division.
-/

namespace OMA.S_oeis_a090523

/-- A090523(n) is the smallest prime `p` with `⌊n!/p⌋` prime, or `0` if there is none; the
conjecture "there are no zeros for `n > 2`" says such a prime exists for every `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ (n.factorial / p).Prime := by
  sorry

end OMA.S_oeis_a090523
