import Mathlib

/-!
# A007675: Numbers m such that m, m+1 and m+2 are squarefree

Source: https://oeis.org/A007675
Credit: @niclorusso

Conjecture (Thomas Ordowski, in the comments of A007675): for every prime p, the numbers p# - 1,
p#, p# + 1 are squarefree, where primorial p# = product of all primes <= p.

Conventions:
* p# is Mathlib's `primorial p`, the product of all primes <= p.
* Squarefree is Mathlib's `Squarefree` on the natural numbers.
-/

namespace OMA.S_oeis_a007675

/-- Ordowski's conjecture on A007675: for every prime `p`, the three consecutive numbers
`p# - 1`, `p#` and `p# + 1` are squarefree (so `p# - 1` is a term of A007675). -/
theorem main : ∀ p : ℕ, p.Prime →
    Squarefree (primorial p - 1) ∧ Squarefree (primorial p) ∧ Squarefree (primorial p + 1) := by
  sorry

end OMA.S_oeis_a007675
