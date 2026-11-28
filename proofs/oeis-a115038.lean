import OMAStatements.S_oeis_a115038
import Mathlib

/-!
# A115038: `x² + p` is a perfect power for a suitable `x`

For an odd prime `p = 2k + 1` take `x = k`: `k² + (2k + 1) = (k + 1)²`.
For `p = 2` take `x = 5`: `5² + 2 = 27 = 3³`.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a115038.main := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | ⟨k, hk⟩
  · exact ⟨5, 3, 3, by norm_num, by norm_num⟩
  · exact ⟨k, k + 1, 2, le_rfl, by rw [hk]; ring⟩
