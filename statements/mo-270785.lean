import Mathlib

/-!
# Truncated complementary Bell numbers vanish only at `n = 2`

Source: https://mathoverflow.net/questions/270785 (CC BY-SA 4.0).

For `r ≥ 2` let `G_r(x) = exp(-(x + x²/2! + ⋯ + x^r/r!)) = ∑_n B̃_{n,r} x^n/n!`. Question 1: for fixed
`r ≥ 2`, is it true that `B̃_{n,r} = 0` iff `n = 2` (the "index-2 property", Wilf's conjecture being
the case `r = ∞`)?

We state a positive answer to Question 1.

Formalization notes:
* `G_r' = -(1 + x + ⋯ + x^(r-1)/(r-1)!) G_r` gives, coefficientwise, `B̃_{0,r} = 1` and
  `B̃_{n+1,r} = -∑_{k=0}^{min(n, r-1)} C(n,k) B̃_{n-k,r}`; this recurrence determines the integer
  sequence, so we state the property for any `a : ℕ → ℤ` satisfying it.
* For large `r` it reproduces the complementary Bell numbers `1, -1, 0, 1, 1, -2, -9, -9, …`.
* Checked for `r = 2, …, 8` and `n ≤ 300`: the only zero is at `n = 2`.
-/

namespace OMA.S_mo_270785

/-- For `r ≥ 2`, the coefficients of `exp(-(x + ⋯ + x^r/r!))` vanish exactly at `n = 2`. -/
theorem main :
    ∀ (r : ℕ) (hr : 2 ≤ r) (a : ℕ → ℤ) (h0 : a 0 = 1)
      (hrec : ∀ n, a (n + 1) = -∑ k ∈ Finset.range (min n (r - 1) + 1), (n.choose k : ℤ) * a (n - k)),
    ∀ n, a n = 0 ↔ n = 2 := by
  sorry

end OMA.S_mo_270785
