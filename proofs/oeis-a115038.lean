import OMAStatements.S_oeis_a115038
import Mathlib

namespace OMA.S_oeis_a115038
end OMA.S_oeis_a115038

theorem OMA.solution : type_of% @OMA.S_oeis_a115038.main := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | ⟨k, hk⟩
  · exact ⟨5, 3, 3, by norm_num, by norm_num⟩
  · refine ⟨k, k + 1, 2, le_refl _, ?_⟩
    subst hk
    ring
