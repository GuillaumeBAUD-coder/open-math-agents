import Mathlib

/-!
# Lindelöf hypothesis

For every positive real exponent ε, the Riemann zeta function on the
critical line grows as little-o of t to the power ε as real t tends to
positive infinity.

Source: https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis
Credit: @senamakel
-/

namespace OMA.S_wp_lindelof_hypothesis_that_for_all_varepsilon_0_zeta_1_2_it_o_t_varepsilon

open Complex Filter Asymptotics

theorem main : ∀ ε : ℝ, 0 < ε →
    (fun t : ℝ => riemannZeta (1 / 2 + (t : ℂ) * I)) =o[atTop]
      (fun t : ℝ => t ^ ε) := by
  sorry

end OMA.S_wp_lindelof_hypothesis_that_for_all_varepsilon_0_zeta_1_2_it_o_t_varepsilon
