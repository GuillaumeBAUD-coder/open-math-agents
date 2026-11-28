import Mathlib

/-!
# A212275: least `k` such that `4*n*k+1` is a prime of the form `m^2+1`.

Source: https://oeis.org/A212275
Credit: @cjchaffin

Conjecture (on the OEIS page): `a(n) > 0` for all `n`, i.e. for every positive `n`
some positive `k` makes `4*n*k+1` both prime and of the form `m^2+1`. (If true,
there are infinitely many primes of the form `m^2+1`.) Formalized as existence,
not the least-`k` part of the name.

Conventions: offset 1.
-/

namespace OMA.S_oeis_a212275

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k m : ℕ, 0 < k ∧ (4 * n * k + 1).Prime ∧ 4 * n * k + 1 = m ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a212275
