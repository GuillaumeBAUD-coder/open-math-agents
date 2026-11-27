import OMAStatements.S_oeis_a290650
import Mathlib.Tactic

open OMA.S_oeis_a290650

namespace OMA.A290650

lemma term_pos (i : ℕ) : 0 < term i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [term]
    split
    · omega
    · positivity

end OMA.A290650

theorem OMA.solution : type_of% @OMA.S_oeis_a290650.main := by
  classical
  intro B
  let P (m : ℕ) := ∃ i, B ≤ i ∧ term i = m
  have hex : ∃ m, P m := ⟨term B, B, le_rfl, rfl⟩
  obtain ⟨i, hi, hmin⟩ := Nat.find_spec hex
  have hpos := OMA.A290650.term_pos i
  have hodd : term i % 2 ≠ 0 := by
    intro heven
    have hnext : Nat.find hex ≤ term (i+1) :=
      Nat.find_min' hex (show P (term (i+1)) from ⟨i+1, by omega, rfl⟩)
    rw [term, if_pos heven] at hnext
    omega
  refine ⟨i+1, ?_⟩
  rw [term, if_neg hodd]
  nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)]
