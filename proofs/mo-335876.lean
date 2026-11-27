import OMAStatements.S_mo_335876
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_335876.main) := by
  intro h
  have hmin : IsLocalMin (fun y : ℝ => |y|) 0 := by
    apply Filter.Eventually.of_forall
    intro y
    simp
  have hd : OMA.S_mo_335876.hasDirectionalDerivative (fun y : ℝ => |y|) 0 1 1 := by
    unfold OMA.S_mo_335876.hasDirectionalDerivative
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp [abs_of_pos ht', ht'.ne']
  have := h ℝ (fun y : ℝ => |y|) 0 hmin 1 1 hd
  norm_num at this
