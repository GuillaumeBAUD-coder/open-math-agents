import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Hanna's two congruence conjectures for the inverse series A393858

Source: https://oeis.org/A393858
Credit: @anmolspace

Paul D. Hanna defines A by A(x - x*A(6*x)/6) = x, with A starting at x.
Write A = xB. Then A(6*x)/6 = x*B(6*x), so the equation below has
integer coefficients and uses ordinary formal substitution.
-/

namespace OMA.S_oeis_a393858

open PowerSeries

/-- The normalized generating series from the OEIS definition. -/
def Defines (A : PowerSeries ℤ) : Prop :=
  ∃ B : PowerSeries ℤ, A = X*B ∧ B.constantCoeff = 1 ∧
    A.subst (X-X^2*rescale 6 B) = X

/-- The integral series exists. At positive indices its coefficients are
odd exactly at powers of two, and they are all congruent to one modulo seven. -/
theorem main : (∃ A, Defines A) ∧
    ∀ A, Defines A → ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧ coeff n A % 7 = 1 := by
  sorry

end OMA.S_oeis_a393858
