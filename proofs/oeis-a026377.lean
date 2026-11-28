import OMAStatements.S_oeis_a026377
import Mathlib

namespace OMA.P026377

open OMA.S_oeis_a026377

lemma v2 : a 2 = 1 := by decide

lemma v3 : a 3 = 9 := by decide

lemma v4 : a 4 = 58 := by decide

end OMA.P026377

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a026377.main) := by
  intro h
  have h4 := h 4 (by norm_num)
  norm_num [OMA.P026377.v2, OMA.P026377.v3, OMA.P026377.v4] at h4
