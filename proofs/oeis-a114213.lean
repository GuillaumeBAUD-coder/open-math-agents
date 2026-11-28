import OMAStatements.S_oeis_a114213
import Mathlib

open OMA.S_oeis_a114213

private theorem firstColumn (n : ℕ) : entry n 0 = 1 := by
  simp only [entry, Nat.zero_le, if_true, Nat.sub_zero]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro j _ hj
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a114213.main := by
  intro n
  have ht : (corner n).IsLowerTriangular := by
    intro i j hij
    have h : i < j := hij
    simp [corner, entry, not_le_of_gt h]
  have hd : (corner n).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ ht]
    simp [corner, entry]
  have hi := Matrix.nonsing_inv_mul (corner n) (hd ▸ isUnit_one)
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ => M (Fin.last n) 0) hi
  simp only [Matrix.mul_apply, corner, Matrix.of_apply, Fin.val_zero, firstColumn, Nat.cast_one, mul_one] at h
  change (∑ j, (corner n)⁻¹ (Fin.last n) j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (Fin.last n) 0 at h
  rw [h, Matrix.one_apply]
  cases n <;> simp
