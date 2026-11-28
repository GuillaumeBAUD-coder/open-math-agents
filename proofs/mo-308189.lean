import OMAStatements.S_mo_308189
import Mathlib

/-!
A shorter version of @justusklocke-cloud's disproof in PR #9830, retaining the
polynomial X + 2. Standard polynomial evaluation and norm simplification replace
its explicit complex evaluation and absolute-value certificates.
Source: https://mathoverflow.net/questions/308189
-/

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
  norm_num [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h1
  linarith
