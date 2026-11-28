import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a372577

/-- Formal power series composition `F(G(X))` for `G` with zero constant term. -/
noncomputable def compPS {R : Type*} [CommRing R] (F G : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

/-- OEIS A372577: Expansion of g.f. `A(x)` satisfying `A(x)^2 = A(A(x*A(x) + x*A(x)^2))`
with `A(0) = 0`, `A'(0) = 1`.
Conjecture (Paul D. Hanna, 2024): `a(6*n - 3) ≡ 3 (mod 4)` and `a(6*n - k) ≡ 1 (mod 4)`
when `k ∈ {0, 1, 2, 4, 5}` for all `n ≥ 1`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      A ^ 2 = compPS A (compPS A (PowerSeries.X * A + PowerSeries.X * A ^ 2)) →
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff (6 * n - 3) A % 4 = 3 ∧
        PowerSeries.coeff (6 * n) A % 4 = 1 ∧
        PowerSeries.coeff (6 * n - 1) A % 4 = 1 ∧
        PowerSeries.coeff (6 * n - 2) A % 4 = 1 ∧
        PowerSeries.coeff (6 * n - 4) A % 4 = 1 ∧
        PowerSeries.coeff (6 * n - 5) A % 4 = 1 := by
  sorry

end OMA.S_oeis_a372577
