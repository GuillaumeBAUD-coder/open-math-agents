import Mathlib

/-!
# A232398: Number of ways to write n = p + (2^k - k) + (2^m - m) with p prime and 0 < k <= m.

Source: https://oeis.org/A232398
Credit: @keiichisince1986-bot

A232398 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3.

Conventions:
- `a(n) > 0` means that there is at least one such representation. Since `k < 2^k`, the
  truncated subtractions `2 ^ k - k` in `ℕ` are exact.
-/

namespace OMA.S_oeis_a232398

theorem main :
    ∀ n : ℕ, 3 < n → ∃ p k m : ℕ, p.Prime ∧ 0 < k ∧ k ≤ m ∧ n = p + (2 ^ k - k) + (2 ^ m - m) := by
  sorry

end OMA.S_oeis_a232398
