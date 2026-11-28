import OMAStatements.S_mo_219776
import Mathlib

open Set

open OMA.S_mo_219776



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_219776.main) := by
  intro h
  let H (y : ℝ) := 1 + y
  let F (x : ℝ) := x ^ 2 + 2 * x
  let G (y : ℝ) := (1 + y) ^ 2
  have hH : ContinuousOn H (Icc 0 1) := by unfold H; fun_prop
  have hF : ContinuousOn F (Icc 0 1) := by unfold F; fun_prop
  have hMono : MonotoneOn F (Icc 0 1) := by
    intro x hx y hy hxy
    have hm := mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx.1 hy.1)
    dsimp [F]
    nlinarith
  obtain ⟨c, hc⟩ := h 1 zero_lt_one H F G hH
    ⟨1, by norm_num, by norm_num [H]⟩ hF hMono (by norm_num [F])
    (by intros; dsimp [F, G, H]; ring)
  have h₁ := hc 1 (by norm_num)
  have h₂ := hc (1 / 2) (by norm_num)
  norm_num [F] at h₁ h₂
  linarith
