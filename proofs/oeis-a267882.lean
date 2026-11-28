import OMAStatements.S_oeis_a267882
import Mathlib

namespace A267882Aux

open OMA.S_oeis_a267882 in
lemma a2 : a 2 = 4 := by decide

open OMA.S_oeis_a267882 in
lemma a3 : a 3 = 10 := by decide

open OMA.S_oeis_a267882 in
lemma a4 : a 4 = 19 := by decide

open OMA.S_oeis_a267882 in
lemma a5 : a 5 = 30 := by decide

end A267882Aux

open OMA.S_oeis_a267882 A267882Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267882.main) := by
  intro h
  have h5 := h.1 5 (by norm_num)
  rw [show (5 : ℕ) - 1 = 4 from rfl, show (5 : ℕ) - 2 = 3 from rfl,
    show (5 : ℕ) - 3 = 2 from rfl, a5, a4, a3, a2] at h5
  norm_num at h5
