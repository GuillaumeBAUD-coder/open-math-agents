import OMAStatements.S_oeis_a081567
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Binet (Real.coe_fib_eq) and the binomial theorem: a(n) = (phi(phi+2)^n - psi(psi+2)^n)/sqrt5 and b(m+1) = (phi^2(phi^2+1)^m - psi^2(psi^2+1)^m)/sqrt5; with phi^2 = phi+1 the identity a(m+1) = 2a(m) + b(m+1) is linear_combination.

namespace OMA.P_oeis_a081567

open OMA.S_oeis_a081567 Real

lemma a_real (n : ℕ) : (a n : ℝ) =
    (goldenRatio * (goldenRatio + 2) ^ n - goldenConj * (goldenConj + 2) ^ n) / √5 := by
  unfold a
  push_cast
  simp only [Real.coe_fib_eq, add_pow]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  generalize goldenRatio = p
  generalize goldenConj = q
  ring

lemma b_real (m : ℕ) : (b (m + 1) : ℝ) =
    (goldenRatio ^ 2 * (goldenRatio ^ 2 + 1) ^ m - goldenConj ^ 2 * (goldenConj ^ 2 + 1) ^ m) / √5 := by
  unfold b
  push_cast
  simp only [Real.coe_fib_eq, add_pow, Nat.add_sub_cancel]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_pow, mul_one]
  generalize goldenRatio = p
  generalize goldenConj = q
  ring

end OMA.P_oeis_a081567

theorem OMA.solution : type_of% @OMA.S_oeis_a081567.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega]
  have h : ((OMA.S_oeis_a081567.a (m + 1) : ℕ) : ℝ) =
      ((2 * OMA.S_oeis_a081567.a m + OMA.S_oeis_a081567.b (m + 1) : ℕ) : ℝ) := by
    push_cast
    rw [OMA.P_oeis_a081567.a_real, OMA.P_oeis_a081567.a_real, OMA.P_oeis_a081567.b_real]
    have g1 : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    have g2 : Real.goldenConj ^ 2 = Real.goldenConj + 1 := Real.goldenConj_sq
    rw [g1, g2]
    have h5 : (√5 : ℝ) ≠ 0 := by positivity
    generalize Real.goldenRatio = p at g1 ⊢
    generalize Real.goldenConj = q at g2 ⊢
    field_simp
    linear_combination (2 + p) ^ m * g1 - (2 + q) ^ m * g2
  exact_mod_cast h
