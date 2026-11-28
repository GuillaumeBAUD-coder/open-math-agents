import Mathlib

/-!
# Density of values of polynomials in two variables

Source: https://mathoverflow.net/questions/45511/density-of-values-of-polynomials-in-two-variables
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_45511

open Filter

def evalAtIntegers (f : MvPolynomial (Fin 2) ℚ) (x y : ℤ) : ℚ :=
  MvPolynomial.eval ![(x : ℚ), (y : ℚ)] f

noncomputable def valueCount (f : MvPolynomial (Fin 2) ℚ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (n + 1)).filter
    (fun k => ∃ x y : ℤ, evalAtIntegers f x y = (k : ℚ))).card

theorem main (f : MvPolynomial (Fin 2) ℚ)
    (hf : ∀ x y : ℤ, ∃ k : ℕ, evalAtIntegers f x y = (k : ℚ)) :
    Asymptotics.IsBigO atTop (fun n : ℕ => (valueCount f n : ℝ))
      (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end OMA.S_mo_45511
