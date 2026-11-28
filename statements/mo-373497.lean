import Mathlib

/-!
# No composite `n = am + 1` with `m ∣ φ(n)` when `a` is below the least prime factor of `m`

Source: https://mathoverflow.net/questions/373497
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `n = am + 1` with `a, m` positive integers, `m > 1`, and let `p` be the least prime divisor of
`m`. Conjecture (asker): if `a < p` and `m ∣ φ(n)`, then `n` is prime.

Conventions:
* `p` is `Nat.minFac m`; `φ` is `Nat.totient`.
-/

namespace OMA.S_mo_373497

/-- If `n = am + 1`, `1 ≤ a < minFac m`, `m > 1` and `m ∣ φ(n)`, then `n` is prime. -/
theorem main : ∀ a m : ℕ, 1 ≤ a → 1 < m → a < Nat.minFac m →
    m ∣ Nat.totient (a * m + 1) → (a * m + 1).Prime := by
  sorry

end OMA.S_mo_373497
