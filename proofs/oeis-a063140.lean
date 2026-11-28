import OMAStatements.S_oeis_a063140

-- Problem: A063140: Dimension of the space of weight 2n cusp forms for Gamma_0( 72 ).
-- Upstream: formal-conjectures statements/oeis-a063140.lean:0 (declaration OMA.S_oeis_a063140.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The coefficient of x^n in 4 exp(x) (6x - 5) is 24/(n-1)! - 20/n! = (24n - 20)/n! for n ≥ 1 and -20
for n = 0. Adding 20 + x gives 0 at n = 0, 5 at n = 1 and (24n - 20)/n! for n ≥ 2. -/

namespace A063140Aux

open OMA.S_oeis_a063140 PowerSeries

theorem a0 : a 0 = 0 := by simp [a]

theorem a1 : a 1 = 5 := by simp [a]

theorem a_big (m : ℕ) : a (m + 2) = 24 * (m : ℤ) + 28 := by
  have h0 : ¬ (m + 2 = 0) := by omega
  have h1 : ¬ (m + 2 = 1) := by omega
  simp [a, h1]
  ring

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
    (1 : ℚ⟦X⟧) * C 20 + (1 : ℚ⟦X⟧) * X * C 1 + PowerSeries.exp ℚ * X * C 24 +
      PowerSeries.exp ℚ * C (-20) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0, PowerSeries.coeff_exp]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_mk]
      simp [a1, PowerSeries.coeff_exp]
      norm_num
    | succ m =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X,
        PowerSeries.coeff_mk]
      have hb := a_big m
      have hq : ((a (m + 2) : ℤ) : ℚ) = 24 * (m : ℚ) + 28 := by exact_mod_cast hb
      simp [PowerSeries.coeff_exp, PowerSeries.coeff_one, hq]
      have e : ((m + 1 + 1).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ (m + 1)]
        push_cast
        ring
      have hf : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
      have h2 : (m : ℚ) + 2 ≠ 0 := by positivity
      rw [e]
      field_simp
      ring

end A063140Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a063140.main := by
  have h := A063140Aux.gfC
  rw [h]
  simp only [map_ofNat, map_neg, map_one]
  ring
