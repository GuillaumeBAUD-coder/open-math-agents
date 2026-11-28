import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Denominators in Hanna's quadratic exponential series

Paul D. Hanna's OEIS A174491 lists the denominators in lowest terms of the
coefficients of exp(∑_{m≥1} xᵐ/(m·2^(m²))). The stated formula uses the highest
power of two dividing a positive index. The degree-zero coefficient is one.

Source: https://oeis.org/A174491
Credit: @hiattco
-/

namespace OMA.S_oeis_a174491
open PowerSeries

noncomputable def logSeries : PowerSeries ℚ :=
  mk fun m => if m = 0 then 0 else 1 / ((m : ℚ) * 2 ^ (m ^ 2))

noncomputable def expSeries : PowerSeries ℚ := (PowerSeries.exp ℚ).subst logSeries

theorem main : ∀ n : ℕ, 0 < n →
    (coeff n expSeries).den = 2 ^ (n ^ 2 + padicValNat 2 n) := by
  sorry

end OMA.S_oeis_a174491
