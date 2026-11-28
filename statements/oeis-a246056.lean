import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a246056

/-- Generating function of OEIS A246056:
`∑_{n≥0} x^n / (1 - 2*x)^(2*n+1) * (∑_{k=0}^n C(n,k)^2 * 2^k * x^k) * (∑_{k=0}^n C(n,k)^2 * 3^k * x^k)`. -/
noncomputable def A246056_series : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      PowerSeries.coeff m
        (PowerSeries.X ^ n * Ring.inverse ((1 - 2 * PowerSeries.X) ^ (2 * n + 1)) *
          (∑ k ∈ Finset.range (n + 1),
            PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 2 ^ k) * PowerSeries.X ^ k) *
          (∑ k ∈ Finset.range (n + 1),
            PowerSeries.C ((Nat.choose n k : ℤ) ^ 2 * 3 ^ k) * PowerSeries.X ^ k))

/-- Predicate for OEIS A005836: natural numbers whose base-3 representation contains no digit 2. -/
def IsNoDigitTwoBase3 (n : ℕ) : Prop :=
  ∀ k : ℕ, (n / 3 ^ k) % 3 ≠ 2

/-- OEIS A246056: Conjecture (Paul D. Hanna, 2014):
`a(n) ≡ 1 (mod 3)` when `n = 2 * A005836(k)` for some `k ≥ 0`, and `a(n) ≡ 0 (mod 3)` otherwise. -/
theorem main :
    ∀ n : ℕ,
      (PowerSeries.coeff n A246056_series % 3 = 1 ↔ Even n ∧ IsNoDigitTwoBase3 (n / 2)) ∧
      (PowerSeries.coeff n A246056_series % 3 = 0 ↔ ¬ (Even n ∧ IsNoDigitTwoBase3 (n / 2))) := by
  sorry

end OMA.S_oeis_a246056
