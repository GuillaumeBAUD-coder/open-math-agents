import OMAStatements.S_oeis_a267588
import Mathlib

namespace A267588Aux

open OMA.S_oeis_a267588 in
lemma a3 : a 3 = 1010 := by decide

open OMA.S_oeis_a267588 in
lemma a4 : a 4 = 10100 := by decide

open OMA.S_oeis_a267588 in
lemma a5 : a 5 = 101001 := by decide

end A267588Aux

open OMA.S_oeis_a267588 A267588Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267588.main) := by
  intro h
  have h5 := h.1 5 (by norm_num)
  norm_num [a3, a4, a5] at h5
