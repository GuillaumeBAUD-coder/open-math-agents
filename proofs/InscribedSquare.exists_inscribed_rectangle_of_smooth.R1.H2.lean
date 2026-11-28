import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1
import Mathlib

open scoped ComplexConjugate

theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1.H2 := by
  intro r hr
  let w : ℂ := (r : ℂ) * Complex.I
  have hw : w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') Complex.I_ne_zero
  have hd : 1 + w ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp [w, Complex.mul_re] at hRe
  let ζ := (1 - w) / (1 + w)
  have hconj : conj (1 + w) = 1 - w := by
    simp [w, sub_eq_add_neg]
  have hnorm : ‖ζ‖ = 1 := by
    rw [show ζ = (1 - w)/(1 + w) from rfl, norm_div, ← hconj, Complex.norm_conj]
    exact div_self (norm_ne_zero_iff.mpr hd)
  have hplus : 1 + ζ = 2 / (1 + w) := by
    dsimp [ζ]
    field_simp [hd]
    ring
  have hminus : 1 - ζ = (2*w) / (1 + w) := by
    dsimp [ζ]
    field_simp [hd]
    ring
  have hwn : ‖w‖ = r := by simp [w, abs_of_pos hr]
  refine ⟨ζ, hnorm, ?_, ?_, ?_⟩
  · rw [hminus]
    exact div_ne_zero (mul_ne_zero (by norm_num) hw) hd
  · rw [hplus]
    exact div_ne_zero (by norm_num) hd
  · rw [hminus, hplus, norm_div, norm_div, norm_mul, hwn]
    ring