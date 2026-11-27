import Mathlib

/-!
# A072872: a(n) is the smallest positive number k such that n divides 2^k - k.

Source: https://oeis.org/A072872
Credit: @sntntHb

Conjecture (stated on the OEIS page): if `n > 47`, then `a(n) < prime(n)`, where `prime(n)` is the
`n`-th prime (`prime(1) = 2`).

Conventions:
- `prime(n) = Nat.nth Nat.Prime (n - 1)`, since `Nat.nth Nat.Prime` is 0-indexed.
- `2^k ≥ k`, so the natural-number subtraction `2^k - k` is the integer one.
- `a(n)` is the least positive `k` with `n ∣ 2^k - k`. The statement asserts that this least
  value exists (`IsLeast`) and is below `prime(n)`, so no junk value is involved.
-/

namespace OMA.S_oeis_a072872

/-- `k` is a positive number with `n ∣ 2^k - k`. -/
def Good (n k : ℕ) : Prop := 0 < k ∧ n ∣ 2 ^ k - k

theorem main : ∀ n : ℕ, 47 < n →
    ∃ k : ℕ, IsLeast {j : ℕ | Good n j} k ∧ k < Nat.nth Nat.Prime (n - 1) := by
  sorry

end OMA.S_oeis_a072872
