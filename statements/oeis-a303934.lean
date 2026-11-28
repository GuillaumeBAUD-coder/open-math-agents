import Mathlib

/-!
# A303934: Number of ways to write 2*n as p + 2^k + 5^m with p prime and 2^k + 5^m squarefree, where k and m are nonnegative integers.

Source: https://oeis.org/A303934
Credit: @keiichisince1986-bot

A303934 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `a(n) > 0` means that there are a prime `p` and natural numbers `k, m` with
  `2n = p + 2^k + 5^m` and `2^k + 5^m` squarefree.
-/

namespace OMA.S_oeis_a303934

theorem main :
    ∀ n : ℕ, 1 < n → ∃ p k m : ℕ, p.Prime ∧ Squarefree (2 ^ k + 5 ^ m) ∧ 2 * n = p + 2 ^ k + 5 ^ m := by
  sorry

end OMA.S_oeis_a303934
