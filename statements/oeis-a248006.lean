import Mathlib

/-!
# OEIS A248006: least m with m + n dividing φ(mn)

Source: https://oeis.org/A248006
Credit: @SudharsanAnimations

`A248006(n)` (for `n ≥ 3`) is the least positive integer `m` such that `m + n` divides `φ(m n)`.
The entry conjectures that for every `n > 2`, `a(n)` exists and `a(n) ≤ n`, and records the proof:
`2n` divides `φ(n²)` for all `n > 2`, so `m = n` is admissible. We state this proved result.

Conventions: "`a(n)` exists and `a(n) ≤ n`" is stated as the existence of an admissible `m` with
`1 ≤ m ≤ n`; this is equivalent, since then the least admissible `m` exists and is at most that
`m`. `φ` is `Nat.totient`.
-/

namespace OMA.S_oeis_a248006

theorem main : ∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ (m + n) ∣ Nat.totient (m * n) := by
  sorry

end OMA.S_oeis_a248006
