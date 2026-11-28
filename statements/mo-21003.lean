import Mathlib

/-!
# Polynomial bijection from rational pairs to rationals

Source: https://mathoverflow.net/questions/21003/polynomial-bijection-from-mathbb-q-times-mathbb-q-to-mathbb-q
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_21003

theorem main :
    ∃ f : MvPolynomial (Fin 2) ℚ,
      Function.Bijective
        (fun xy : ℚ × ℚ => MvPolynomial.eval ![xy.1, xy.2] f) := by
  sorry

end OMA.S_mo_21003
