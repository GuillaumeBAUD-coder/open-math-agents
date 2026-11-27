import OMAStatements.S_mo_308189
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_308189.main) := by
  intro h
  have hdeg : (Polynomial.X + Polynomial.C (2 : ℂ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C 2
  have hc0 : (Polynomial.X + Polynomial.C (2 : ℂ)).coeff 0 = 2 := by simp
  obtain ⟨M, hM, hall⟩ := h (Polynomial.X + Polynomial.C (2 : ℂ)) (by rw [hdeg]) (by
    intro w hw h0
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h0
    have hw2 : w = -2 := by linear_combination h0
    rw [hw2] at hw
    norm_num at hw)
  obtain ⟨w, hw, hMw⟩ := hM.1
  have hM3 : M ≤ 3 := by
    rw [← hMw, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    calc ‖w + 2‖ ≤ ‖w‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = 3 := by rw [hw]; norm_num
  have hrb : OMA.S_mo_308189.rotationBound (Polynomial.X + Polynomial.C (2 : ℂ)) = 2 / 3 := by
    unfold OMA.S_mo_308189.rotationBound
    rw [hdeg, hc0]
    norm_num
  have h1 := hall 1 (-1) (by simp) (by simp)
  rw [hrb] at h1
  have hval : (1 : ℂ) * (-1) * (Polynomial.derivative (Polynomial.X + Polynomial.C (2 : ℂ))).eval (-1)
      + (-1) * (Polynomial.derivative (Polynomial.X + Polynomial.C (2 : ℂ))).eval (-1)
      - ((2 / 3 : ℝ) : ℂ) * (Polynomial.X + Polynomial.C (2 : ℂ)).eval (-1) = ((-(8 / 3) : ℝ) : ℂ) := by
    simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_zero]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at h1
  have habs : |(-(8 / 3) : ℝ)| = 8 / 3 := by
    rw [abs_neg]; exact abs_of_pos (by norm_num)
  rw [habs] at h1
  linarith
