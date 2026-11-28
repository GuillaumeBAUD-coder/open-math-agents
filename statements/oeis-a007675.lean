import Mathlib

/-!
# A007675: squarefree neighbours of primorials

Source: https://oeis.org/A007675
Credit: @jagraj28

A007675 lists the numbers `m` such that `m`, `m + 1` and `m + 2` are squarefree. The entry
records a conjecture (Thomas Ordowski, 2013): for every prime `p`, the numbers `p# - 1`, `p#`,
`p# + 1` are squarefree, where the primorial `p#` is the product of all primes `≤ p`.

`main` states it with Mathlib's `primorial p` (the product of the primes `≤ p`). Since
`p# ≥ 2`, the natural-number subtraction `p# - 1` is the usual one. (`p#` itself is squarefree
for every `p`, as a product of distinct primes; it is kept in the statement to match the source.)
-/

namespace OMA.S_oeis_a007675

/-- Ordowski's conjecture in OEIS A007675. -/
theorem main : ∀ p : ℕ, p.Prime →
    Squarefree (primorial p - 1) ∧ Squarefree (primorial p) ∧ Squarefree (primorial p + 1) := by
  sorry

end OMA.S_oeis_a007675
