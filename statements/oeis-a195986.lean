import Mathlib

/-!
# OEIS A195986: the 2-adic valuation of 5^n - 3^n

Source: https://oeis.org/A195986
Credit: @SudharsanAnimations

`A195986(n)` is the exponent of the largest power of `2` dividing `5^n - 3^n`, and `A090740(n)` is
the exponent of `2` in `3^n - 1`. The entry conjectures that `a(n) = 1` if `A090740(n) = 1`, and
`a(n) = A090740(n) + 1` otherwise, and records that this is true: by the lifting-the-exponent
lemma, `a(n) = v₂(n) + 3` for even `n` and `a(n) = 1` for odd `n` (Amiram Eldar). We state this
proved result for `n ≥ 1` (offset `1`).

Conventions: valuations are `padicValNat 2`; subtraction is in `ℕ`, which is exact here since
`5^n > 3^n` and `3^n ≥ 1`.
-/

namespace OMA.S_oeis_a195986

/-- `A195986(n)`: the exponent of the largest power of `2` dividing `5^n - 3^n`. -/
def a (n : ℕ) : ℕ := padicValNat 2 (5 ^ n - 3 ^ n)

/-- `A090740(n)`: the exponent of `2` in `3^n - 1`. -/
def A090740 (n : ℕ) : ℕ := padicValNat 2 (3 ^ n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = if A090740 n = 1 then 1 else A090740 n + 1 := by
  sorry

end OMA.S_oeis_a195986
