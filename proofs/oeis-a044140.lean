import OMAStatements.S_oeis_a044140
import Mathlib

namespace OMA.S_oeis_a044140

instance : DecidablePred Has02 := fun m => by unfold Has02; infer_instance
instance : DecidablePred IsTerm := fun k => by unfold IsTerm; infer_instance

lemma e {n k : ℕ} (h : Nat.count IsTerm k = n ∧ IsTerm k) : a (n + 1) = k := by
  rw [a, Nat.add_sub_cancel, ← h.1, Nat.nth_count h.2]

end OMA.S_oeis_a044140

open OMA.S_oeis_a044140 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a044140.main) := fun h => by
  have := h 58 (by norm_num)
  rw [e (n := 57) (k := 2499) (by decide +kernel), show 58 - 1 = 56 + 1 from rfl, e (k := 2452) (by decide +kernel),
    show 58 - 8 = 49 + 1 from rfl, e (k := 2158) (by decide +kernel), show 58 - 9 = 48 + 1 from rfl,
    e (k := 2109) (by decide +kernel)] at this
  norm_num at this
