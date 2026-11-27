import Mathlib

/-!
# A002981: Numbers k such that k! + 1 is prime.

Source: https://oeis.org/A002981
Credit: @mattdorman

The source states (Mohammed Bouayoun, 2004): we can conjecture that for `n > 2`, if `n! + 1` is
prime then `(n + 1)! + 1` is not prime.

Reading used here: `n` is a natural number with `n > 2` (for `n = 1, 2` both `n! + 1` and
`(n + 1)! + 1` are prime, which is why the source excludes them). The equivalent reformulation
in terms of `nextprime` that the source also gives is not part of the conjecture.
-/

namespace OMA.S_oeis_a002981

theorem main :
    ∀ n : ℕ, 2 < n → (n.factorial + 1).Prime → ¬ ((n + 1).factorial + 1).Prime := by
  sorry

end OMA.S_oeis_a002981
