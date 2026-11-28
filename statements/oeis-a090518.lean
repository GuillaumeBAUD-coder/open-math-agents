import Mathlib

/-!
# OEIS A090518: no term is zero

Source: https://oeis.org/A090518
Credit: @SudharsanAnimations

`A090517(n)` (for `n ≥ 1`) is the least `k` such that `⌊10^n / k⌋` is prime, and `A090518(n)` is
the prime `⌊10^n / A090517(n)⌋`, or `0` if `A090517(n) = 0`. The OEIS entry conjectures that no
term of `A090518` is zero, and records the proof: `k = 5 · 10^(n-1)` gives `⌊10^n / k⌋ = 2`. We
state this proved result.

Conventions: `⌊10^n / k⌋` is natural-number division; the least such `k` is `Nat.find`, and
`A090517(n)` is set to `0` when no such `k` exists, following the wording of A090518. The sequences
start at `n = 1` (offset 1).
-/

namespace OMA.S_oeis_a090518

open Classical in
/-- `A090517(n)`: the least `k` such that `⌊10^n / k⌋` is prime, or `0` if there is none. -/
noncomputable def A090517 (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, (10 ^ n / k).Prime then Nat.find h else 0

/-- `A090518(n)`: the prime `⌊10^n / A090517(n)⌋`, or `0` if `A090517(n) = 0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if A090517 n = 0 then 0 else 10 ^ n / A090517 n

theorem main : ∀ n : ℕ, 1 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090518
