import Mathlib

/-!
# A347768: Permanent of the n X n matrix with (j,k)-entry |j-k+1| (j,k = 1..n).

Source: https://oeis.org/A347768
Credit: @warshanks

`a(n)` is the permanent of the `n × n` integer matrix whose `(j, k)`-entry is `|j - k + 1|`
(`j, k = 1..n`). The entry records one conjecture (Zhi-Wei Sun, see arXiv:2108.07723):

  for any odd prime `p`, `a(p) ≡ 1/2 (mod p)`.

Since `p` is odd, `2` is invertible modulo `p`, and `a(p) ≡ 1/2 (mod p)` means exactly
`2 * a(p) ≡ 1 (mod p)`; `main` states it in that form, over the integers.

Indexing: Lean's `Fin n` runs over `0..n-1` instead of `1..n`. The entry `|j - k + 1|` depends only
on the difference `j - k`, so shifting both indices by one gives the same matrix.
The permanent is Mathlib's `Matrix.permanent`, `∑ σ, ∏ i, M (σ i) i`.
-/

namespace OMA.S_oeis_a347768

/-- The `n × n` integer matrix with `(j, k)`-entry `|j - k + 1|`. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun j k => |(j : ℤ) - (k : ℤ) + 1|

/-- `a n`: the permanent of `M n` (OEIS A347768, offset 1). -/
def a (n : ℕ) : ℤ := (M n).permanent

/-- Zhi-Wei Sun's conjecture in OEIS A347768: for any odd prime `p`, `a(p) ≡ 1/2 (mod p)`,
that is, `2 * a(p) ≡ 1 (mod p)`. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → 2 * a p ≡ 1 [ZMOD p] := by
  sorry

end OMA.S_oeis_a347768
