import Mathlib

namespace OMA.S_wp_keating_snaith_conjecture

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

/-- The arithmetic Euler product. The Pochhammer expression includes the
continuous value at k = 0 of the gamma quotient. -/
noncomputable def arithmeticFactor (k : ℝ) : ℝ :=
  ∏' p : Nat.Primes,
    let q : ℝ := (p : ℕ)
    (1 - 1 / q) ^ (k ^ 2) *
      ∑' m : ℕ, ((ascPochhammer ℝ m).eval k / (m.factorial : ℝ)) ^ 2 / q ^ m

/-- The real logarithm of the Barnes G-function at 1 + z, for z greater than -1. -/
noncomputable def logBarnesOnePlus (z : ℝ) : ℝ :=
  z / 2 * Real.log (2 * Real.pi) -
    (z + (1 + Real.eulerMascheroniConstant) * z ^ 2) / 2 +
    ∑' j : ℕ,
      let n : ℝ := (j + 1 : ℕ)
      n * Real.log (1 + z / n) - z + z ^ 2 / (2 * n)

/-- The unnormalized moment of the absolute zeta value on the critical line. -/
noncomputable def moment (k T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc 0 T,
    ENNReal.ofReal (‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ (2 * k))

/-- The Keating–Snaith moment conjecture for every real order above minus one half. -/
theorem main :
    ∀ k : ℝ, -(1 / 2 : ℝ) < k →
      let C := arithmeticFactor k * Real.exp
        (2 * logBarnesOnePlus k - logBarnesOnePlus (2 * k))
      Tendsto (fun T : ℝ =>
        moment k T / ENNReal.ofReal (T * C * Real.log T ^ (k ^ 2))) atTop (𝓝 1) := by
  sorry

end OMA.S_wp_keating_snaith_conjecture
