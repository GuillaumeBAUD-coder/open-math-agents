import Mathlib

/-!
# OEIS A143727: near-prime numbers are multiples of 15

Source: https://oeis.org/A143727
Credit: @SudharsanAnimations

A143727 lists the numbers `n` such that `n-2, n+2, n-4, n+4, n-8, n+8` are all prime. Harvey P. Dale
conjectured (Aug 2026) that all terms are multiples of 15; the entry records that this is true
(David A. Corneth): for every residue mod 15 other than 0, one of the numbers is a multiple of 3 or of 5
and hence not prime. We state the proved result.

Conventions: subtraction is natural-number subtraction; since `n - 8` must be prime, every term is at
least 10, so no subtraction truncates.
-/

namespace OMA.S_oeis_a143727

/-- Near-prime numbers: `n - 2, n + 2, n - 4, n + 4, n - 8, n + 8` are all prime. -/
def NearPrime (n : ℕ) : Prop :=
  (n - 2).Prime ∧ (n + 2).Prime ∧ (n - 4).Prime ∧ (n + 4).Prime ∧ (n - 8).Prime ∧ (n + 8).Prime

theorem main : ∀ n : ℕ, NearPrime n → 15 ∣ n := by
  sorry

end OMA.S_oeis_a143727
