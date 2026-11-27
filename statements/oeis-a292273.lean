import Mathlib

/-!
# A292273: For odd n: a(n) = 0, and for even n: a(n) = -mu(n), where mu is Moebius function (A008683).

Source: https://oeis.org/A292273
Credit: @LAPRAI

Formalizes the conjecture of Mats Granvik (Jul 06 2024): a(n) = Re(A008683(n)*(i^n)).

Conventions: offset 1, so the claim is stated for `n ≥ 1`. `a n` is an integer, `μ` is
`ArithmeticFunction.moebius`, `i` is `Complex.I`, and `Re` is `Complex.re`.
-/

namespace OMA.S_oeis_a292273

/-- `a n = 0` for odd `n`, and `a n = -μ n` for even `n`. -/
def a (n : ℕ) : ℤ :=
  if n % 2 = 1 then 0 else -ArithmeticFunction.moebius n

/-- For every `n ≥ 1`, `a n = Re (μ n * i ^ n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((a n : ℤ) : ℝ) = (((ArithmeticFunction.moebius n : ℤ) : ℂ) * Complex.I ^ n).re := by
  sorry

end OMA.S_oeis_a292273
