import OMAStatements.S_oeis_a112726
import Mathlib

/-!
# A112726: the conjectured formula a(n) = 10^(3^(n-2)) - 1 fails at n = 5

The statement is false, so this file proves its negation with an explicit counterexample.

For n = 5 the formula would give a(5) = 10^27 - 1. But m = 4899999987 is positive, it is a
multiple of 3^5 = 243 (4899999987 = 243 * 20164609), and its reverse 7899999984 is also a
multiple of 243 (7899999984 = 243 * 32510288). Since a(5) is the least such m, this gives
a(5) ≤ 4899999987, which is smaller than 10^27 - 1. This agrees with the remark in the entry
that the conjecture is rejected for n > 4.
-/

namespace OMA.P112726

open OMA.S_oeis_a112726

/-- The reverse of the witness. -/
theorem rev_w : rev 4899999987 = 7899999984 := by
  norm_num [rev, Nat.ofDigits_cons, Nat.ofDigits_nil]

/-- The witness lies in the set defining a(5), so a(5) is at most the witness. -/
theorem a5_le : a 5 ≤ 4899999987 := by
  unfold a
  apply Nat.sInf_le
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [rev_w]
  norm_num

end OMA.P112726

/-- The formula fails at n = 5: a(5) ≤ 4899999987 < 10^27 - 1. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a112726.main) := by
  intro h
  have h5 := h 5 (by norm_num)
  have hle := OMA.P112726.a5_le
  rw [h5] at hle
  norm_num at hle
