import Mathlib

/-!
# A120069: denominators of partial sums of a series with scaled Catalan numbers

Source: https://oeis.org/A120069
Credit: @sntntHb

A120069 (offset 1) is `a(n) = denominator(r(n))`, where
`r(n) = Sum_{k=1..n} C(k) / 4^(k-1)` and `C(k) = A000108(k)` are the Catalan numbers:
`1, 2, 16, 32, 128, 256, 4096, 8192, ...`.

Formalizes Groux Roland's conjecture (OEIS A120069, Dec 11 2010):
`a(n) = denominator(Catalan(n) / 4^(n-1))`, for every `n >= 1`.
-/

namespace OMA.S_oeis_a120069

/-- The partial sums `r(n) = Sum_{k=1..n} catalan k / 4^(k-1)`. -/
def r (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, (catalan k : ℚ) / 4 ^ (k - 1)

/-- A120069: the denominator of `r(n)`. -/
def a (n : ℕ) : ℕ := (r n).den

/-- Groux Roland's conjecture: `a(n) = denominator(catalan n / 4^(n-1))` for `n >= 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = ((catalan n : ℚ) / 4 ^ (n - 1)).den := by
  sorry

end OMA.S_oeis_a120069
