import OMAStatements.S_oeis_a375231
import Mathlib

/-!
# A375231: the permanent formula fails at `n = 1`

For `n = 1` (odd) the sequence value is `balanced 1 = (1 descFactorial 0)² + (1 descFactorial 1)²
= 1 + 1 = 2`. The checker matrix of size `1` is the `1 × 1` matrix `[1]`, whose permanent is `1`.
-/

namespace OMA.S_oeis_a375231

/-- The sequence value at `n = 1` is `2`. -/
lemma a_one : a 1 = 2 := by decide

/-- The `1 × 1` checker matrix has permanent `1` (its single entry). -/
lemma perm_one : (checker 1).permanent = 1 := by
  rw [Matrix.permanent]
  -- there is exactly one permutation of `Fin 1`, and the diagonal entry is `1`
  simp [checker]
  decide

end OMA.S_oeis_a375231

open OMA.S_oeis_a375231 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a375231.main) := by
  intro h
  have h1 := h 1
  rw [a_one, perm_one] at h1
  -- 2 = 1 is false
  omega
