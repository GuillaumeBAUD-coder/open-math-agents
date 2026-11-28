import OMAStatements.S_oeis_a051397
import Mathlib

open OMA.S_oeis_a051397 in
theorem OMA.solution : type_of% @OMA.S_oeis_a051397.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel, a,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring
