import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a389474

/-!
OEIS A389474: G.f. A(x) satisfies A(x^2 + 2*x^3 + 2*A(x)^2) = 3*A(x)^2,
with A(0) = 0 and A'(0) = 1.
Conjecture (3): [x^n] A(x)^2 == 0 (mod 9) for n > 3.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    PowerSeries.constantCoeff A = 0 →
    PowerSeries.coeff 1 A = 1 →
    PowerSeries.subst (PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 2 * A ^ 2) A = 3 * A ^ 2 →
    ∀ n : ℕ, 3 < n → (9 : ℤ) ∣ PowerSeries.coeff n (A ^ 2) := by
  sorry

end OMA.S_oeis_a389474
