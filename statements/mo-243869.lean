import Mathlib

/-!
# Strict convexity of the logarithm of a polynomial at an exponential

Source: user94803, https://mathoverflow.net/questions/243869 (CC BY-SA 3.0).
Credit: @connoranderson.

Strict convexity is understood on the real line as in the source. The answer
is negative even for a monic sextic with integer coefficients.
-/

namespace OMA.S_mo_243869

noncomputable def profile (f : Polynomial ℝ) (x : ℝ) : ℝ := Real.log (f.eval (Real.exp x))

theorem main : ¬ ∀ f : Polynomial ℝ, f.Monic → (∀ t : ℝ, 0 ≤ t → 0 < f.eval t) →
    StrictConvexOn ℝ Set.univ (profile f) → ∀ x : ℝ, 0 < deriv (deriv (profile f)) x := by
  sorry

end OMA.S_mo_243869
