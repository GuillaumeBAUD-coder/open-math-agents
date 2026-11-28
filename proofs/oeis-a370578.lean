import OMAStatements.S_oeis_a370578
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Push

-- Credit: @CubeJerry

namespace OMA.A370578Proof

private theorem witness_dvd (k : ℕ)
    (h : (3 : ZMod (k + 1)) ^ k = -1) : k + 1 ∣ Nat.pow 3 k + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  rw [Nat.pow_eq]
  push_cast
  rw [h]
  exact neg_add_cancel 1

end OMA.A370578Proof

-- The cases 49 and 61 use new witnesses found by an order-constrained prime-product search.
-- The other seven witnesses occur in the OEIS data table, authored by Viliam Furik.
theorem OMA.solution : type_of% @OMA.S_oeis_a370578.main := by
  intro r hr
  change ∃ k : ℕ, 0 < k ∧ (k + 1) ∣ Nat.pow 3 k + 1 ∧ k % 72 = r
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, OMA.A370578Proof.witness_dvd 1 (by reduce_mod_char), by decide⟩
  · exact ⟨3, by decide, OMA.A370578Proof.witness_dvd 3 (by reduce_mod_char), by decide⟩
  · exact ⟨5362888765, by decide,
      OMA.A370578Proof.witness_dvd 5362888765 (by reduce_mod_char), by decide⟩
  · exact ⟨193264225, by decide,
      OMA.A370578Proof.witness_dvd 193264225 (by reduce_mod_char), by decide⟩
  · exact ⟨27, by decide, OMA.A370578Proof.witness_dvd 27 (by reduce_mod_char), by decide⟩
  · exact ⟨325963347733, by decide,
      OMA.A370578Proof.witness_dvd 325963347733 (by reduce_mod_char), by decide⟩
  · exact ⟨8167178619985, by decide,
      OMA.A370578Proof.witness_dvd 8167178619985 (by reduce_mod_char), by decide⟩
  · exact ⟨490371, by decide,
      OMA.A370578Proof.witness_dvd 490371 (by reduce_mod_char), by decide⟩
  · exact ⟨1623553334183365, by decide,
      OMA.A370578Proof.witness_dvd 1623553334183365 (by reduce_mod_char), by decide⟩
