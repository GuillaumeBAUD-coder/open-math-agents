import Mathlib

/-!
# OEIS A090525: no term is zero

Source: https://oeis.org/A090525
Credit: @SudharsanAnimations

`A090525(n)` (for `n ≥ 2`) is the least `k` such that `⌊n^n / k⌋` is prime, or `0` if there is no
such `k`. The OEIS entry conjectures that no term is zero, and records the proof: if `p` is a
prime factor of `n`, then `k = n^n / p` gives `⌊n^n / k⌋ = p`. We state this proved result.

Conventions: `⌊n^n / k⌋` is natural-number division `n ^ n / k`; the least such `k` is `Nat.find`
(`k = 0` never qualifies, since `n ^ n / 0 = 0`). The sequence starts at `n = 2` (offset 2); for
`n = 1`, `⌊1 / k⌋` is never prime.
-/

namespace OMA.S_oeis_a090525

open Classical in
/-- `A090525(n)`: the least `k` such that `⌊n^n / k⌋` is prime, or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, (n ^ n / k).Prime then Nat.find h else 0

theorem main : ∀ n : ℕ, 2 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090525
