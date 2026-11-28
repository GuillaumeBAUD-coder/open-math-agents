import OMAStatements.S_oeis_a227784
import Mathlib

/-!
# OEIS A227784: the first claim fails at `n = 9`

`9 % 16 = 9`, so the statement asserts that `15` fourth powers are needed to represent `-1`
modulo `9`. But `1⁴ + 2⁴ = 17 ≡ -1 (mod 9)`, so two fourth powers suffice and `a(9) ≤ 2`.
(The value `15` belongs to `n = 16`, not to `n ≡ 9 (mod 16)`.)
-/

open OMA.S_oeis_a227784

namespace OMA.A227784

/-- `1⁴ + 2⁴ = -1` in `ZMod 9`, so `a(9) ≤ 2`. -/
lemma a_nine_le : a 9 ≤ 2 := by
  apply Nat.sInf_le
  refine ⟨![1, 2], ?_⟩
  decide

end OMA.A227784

open OMA.A227784 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227784.main) := by
  intro h
  have h9 : a 9 = 15 := (h 9 (by norm_num)).1 (by norm_num)
  have := a_nine_le
  omega
