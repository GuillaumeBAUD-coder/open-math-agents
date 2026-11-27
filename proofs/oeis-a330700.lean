import OMAStatements.S_oeis_a330700
import Mathlib

/-!
The statement fails at n = 2: M(2) = [[1, 2], [2, 4]] has the single principal 2-minor
1 * 4 - 2 * 2 = 0, while a(2) = 1 * 2 * 15 / 6 = 5.
-/

namespace R330700
open OMA.S_oeis_a330700

theorem a_two : a 2 = 5 := by
  unfold a
  norm_num

theorem e2_two : e2 (M 2) = 0 := by
  unfold e2 M
  simp [Fin.sum_univ_two]

end R330700

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a330700.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [R330700.a_two, R330700.e2_two] at h2
  norm_num at h2
