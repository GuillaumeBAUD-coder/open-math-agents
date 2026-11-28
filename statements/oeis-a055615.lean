import Mathlib

/-!
# A055615: a(n) = n * mu(n), where mu is the Möbius function A008683.

Source: https://oeis.org/A055615
Credit: @tczyzycki

Conjectures (Gerald McGarvey, Sep 26 2004):
`lim_{b -> 1+} ∑_{n = 1}^∞ a(n) * b^(-n) = -12` and
`lim_{b -> 1-} ∑_{n = 1}^∞ a(n) * b^n = -12`,
where `a(n) = n * μ(n)`.

Note: `ArithmeticFunction.moebius 0 = 0`, so `a 0 = 0` and the `tsum` over `n : ℕ` equals the
sum over `n ≥ 1`. The source's parenthetical remark about general `s` is an informal motivation
(with `1 / ζ(-1) = -12`); `main` states the two explicit limit conjectures.
-/

namespace OMA.S_oeis_a055615

/-- `A055615(n) = n * μ(n)` for `n ≥ 1`, and `0` for `n = 0`. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * ArithmeticFunction.moebius n

theorem main :
    Filter.Tendsto
      (fun b : ℝ => ∑' n : ℕ, (a n : ℝ) * b ^ (-(n : ℤ)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (-12 : ℝ)) ∧
    Filter.Tendsto
      (fun b : ℝ => ∑' n : ℕ, (a n : ℝ) * b ^ n)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (-12 : ℝ)) := by
  sorry

end OMA.S_oeis_a055615
