import Mathlib

namespace OMA.S_oeis_a188458

open PowerSeries

/-- Formal power series `cosh(X) = ∑_{m ≥ 0} X^(2m) / (2m)!`. -/
noncomputable def coshPS : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n % 2 = 0 then (1 : ℚ) / ((Nat.factorial n : ℕ) : ℚ) else 0

/-- Conjecture on OEIS A188458:
Let `a(n)` be the coefficients of the e.g.f. `exp(x) / cosh(2*x)` (so `A_egf * cosh(2*X) = exp(1*X)`),
and let `A_ogf(X) = ∑_{n ≥ 0} (n! * [X^n] A_egf) * X^n` be its o.g.f.
Then `A_ogf(X) = T(0) / (1 - x)` (equivalently `T(0) = (1 - PowerSeries.X) * A_ogf(X)`),
where `T : ℕ → ℚ⟦X⟧` satisfies the continued fraction
`T(k) = 1 - 4*X^2*(k+1)^2 / (4*X^2*(k+1)^2 + (1 - PowerSeries.X)^2 / T(k+1))`
(expressed without division with `T(k)(0) = 1`). -/
theorem main :
    ∀ (T : ℕ → PowerSeries ℚ) (A_egf : PowerSeries ℚ),
      A_egf * PowerSeries.rescale (2 : ℚ) coshPS = PowerSeries.rescale (1 : ℚ) (PowerSeries.exp ℚ) →
      (∀ k, PowerSeries.coeff 0 (T k) = 1) →
      (∀ k,
        (PowerSeries.C (4 * ((k + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * T (k + 1) +
          (1 - PowerSeries.X) ^ 2) * (T k - 1) =
        -(PowerSeries.C (4 * ((k + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * T (k + 1))) →
      T 0 = (1 - PowerSeries.X) *
        PowerSeries.mk (fun n => ((Nat.factorial n : ℕ) : ℚ) * PowerSeries.coeff n A_egf) := by
  sorry

end OMA.S_oeis_a188458
