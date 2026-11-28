import OMAStatements.S_oeis_a025756
import Mathlib

open OMA.S_oeis_a025756 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025756.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have t (r : ℚ) (j : ℕ) : ((j:ℚ)+1) * Ring.choose r (j+1) = (r - j) * Ring.choose r j := by
    have h := Ring.choose_smul_choose r (Nat.le_succ j)
    simp at h
    linarith
  have a2 := t (2/3) (k+2)
  have a1 := t (2/3) (k+1)
  have b2 := t (1/3) (k+2)
  have b1 := t (1/3) (k+1)
  simp [a, d, term, Finset.sum_range_succ, add_assoc] at a1 a2 b1 b2 ⊢
  linear_combination (1/3 : ℚ) * ((k+2) * (-9)^(k+3) * a2 + (-9) * (2/3+k) * (-9)^(k+2) * a1) +
    (-2/3 : ℚ) * ((k+2) * (-9)^(k+3) * b2 + (-9) * (1/3+k) * (-9)^(k+2) * b1)
