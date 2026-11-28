import Mathlib

/-!
# A233296: a(n) = |{0 < k < n: k*prime(n-k) + 1 is prime}|.

Source: https://oeis.org/A233296
Credit: @keiichisince1986-bot

A233296 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1. [The entry also lists further conjectures (variants with
k*prime(n-k) - 1, k^2*prime(n-k) - 1, k + prime(n-k), k^2 + prime(n-k)^2); only the first claim of
part (i), about a(n) itself, is formalized here.]

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- For `0 < k < n` we have `n - k ≥ 1`, so `prime(n - k)` is `Nat.nth Nat.Prime (n - k - 1)`.
- `a(n) > 0` means that `k * prime(n - k) + 1` is prime for some `0 < k < n`.
-/

namespace OMA.S_oeis_a233296

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (k * Nat.nth Nat.Prime (n - k - 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a233296
