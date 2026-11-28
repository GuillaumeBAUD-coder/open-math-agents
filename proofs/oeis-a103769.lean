import OMAStatements.S_oeis_a103769
import Mathlib

namespace OMA.P103769

open OMA.S_oeis_a103769

lemma v0 : a 0 = 1 := by decide

lemma v1 : a 1 = 4 := by decide

lemma v2 : a 2 = 21 := by decide

lemma v3 : a 3 = 123 := by decide

lemma v4 : a 4 = 757 := by decide

end OMA.P103769

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103769.main) := by
  intro h
  have h4 := h 4 (by norm_num)
  norm_num [OMA.P103769.v0, OMA.P103769.v1, OMA.P103769.v2, OMA.P103769.v3, OMA.P103769.v4] at h4
