import Mathlib

namespace OMA.S_oeis_a272468

/-- Formal power series `sin(X) = ∑_{m ≥ 0} (-1)^m X^(2m+1) / (2m+1)!`. -/
noncomputable def sinPS : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / ((Nat.factorial n : ℕ) : ℚ) else 0

/-- OEIS A272468 conjecture:
Given positive integers `a` and `b`, the coefficient of `x^(2*n) / (2*n)!` is an integer
for all `n ≥ 0` in the power series expansion of
`((sin(a*x) + sin(b*x)) / sin((a + b)*x))^(1 / (a * b))`.
Formally, for any `a b : ℕ` with `0 < a` and `0 < b`, and any `F : PowerSeries ℚ` with
`coeff 0 F = 1` and `F ^ (a * b) * sin((a + b)*X) = sin(a*X) + sin(b*X)`,
for every `n : ℕ`, `(2*n)! * coeff (2*n) F` is an integer. -/
theorem main :
    ∀ (a b : ℕ), 0 < a → 0 < b →
      ∀ (F : PowerSeries ℚ),
        PowerSeries.coeff 0 F = 1 →
        F ^ (a * b) * PowerSeries.rescale ((a + b : ℕ) : ℚ) sinPS =
          PowerSeries.rescale (a : ℚ) sinPS + PowerSeries.rescale (b : ℚ) sinPS →
        ∀ n : ℕ, ∃ z : ℤ,
          ((Nat.factorial (2 * n) : ℕ) : ℚ) * PowerSeries.coeff (2 * n) F = (z : ℚ) := by
  sorry

end OMA.S_oeis_a272468
