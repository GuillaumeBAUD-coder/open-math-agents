import Mathlib

/-!
# A000122 — Plouffe's theta series evaluation at exp(-pi)

Source: https://oeis.org/A000122
Credit: @Andyi955

The OEIS entry A000122 is the expansion of the Jacobi theta function
`theta_3(x) = Sum_{m = -oo..oo} x ^ (m ^ 2)`, so its `n`-th term is the number of integer
solutions of `k ^ 2 = n`. The conjecture recorded there, due to Simon Plouffe, is

`Sum_{k >= 0} a(k) / exp(k * pi) = pi ^ (1/4) / Gamma(3/4)`,

the right-hand side being A175573.

## Encoding

* `thetaCoeff n` is the number of integers `k` with `k ^ 2 = n`; the range `|k| ≤ n` suffices,
  since `k ^ 2 = n` forces `|k| ≤ n`.
* The series is stated as `HasSum` over `ℝ` of the terms `a(k) / exp(k * pi)`, written as
  `a(k) * exp (-(k * pi))`, with the value `pi ^ (1/4) / Gamma(3/4)` from Mathlib's `Real.pi`,
  `Real.exp` and `Real.Gamma`.
-/

namespace OMA.S_oeis_a000122

/-- `thetaCoeff n` is the number of integer solutions of `k ^ 2 = n`, the `n`-th coefficient of
the Jacobi theta function `theta_3`. -/
noncomputable def thetaCoeff (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => k ^ 2 = (n : ℤ))).card

/-- **Plouffe's conjecture (OEIS A000122)**: `Sum_{k >= 0} a(k) / exp(k * pi)` equals
`pi ^ (1/4) / Gamma(3/4)`. -/
theorem main :
    HasSum (fun n : ℕ => (thetaCoeff n : ℝ) * Real.exp (-(n * Real.pi)))
      (Real.pi ^ ((1 : ℝ) / 4) / Real.Gamma (3 / 4)) := by
  sorry

end OMA.S_oeis_a000122
