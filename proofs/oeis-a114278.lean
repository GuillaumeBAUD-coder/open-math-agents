import OMAStatements.S_oeis_a114278
import Mathlib

open OMA.S_oeis_a114278

private theorem firstColumn (n : ℕ) : entry n 0 = 1 := by
  simp [entry]

private theorem aboveDiagonal {n k : ℕ} (h : n < k) : entry n k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [Nat.choose_eq_zero_of_lt (show n - j < k by omega), mul_zero]

private theorem diagonal (n : ℕ) : entry n n = 1 := by
  unfold entry
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj h
    have hj' := Finset.mem_range.mp hj
    rw [Nat.choose_eq_zero_of_lt (show n - j < n by omega), mul_zero]
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a114278.main := by
  intro n
  have ht : (corner n).IsLowerTriangular := by
    intro i j hij
    have h : i < j := hij
    simp [corner, aboveDiagonal h]
  have hd : (corner n).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ ht]
    simp [corner, diagonal]
  have hi := Matrix.nonsing_inv_mul (corner n) (hd ▸ isUnit_one)
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ => M (Fin.last n) 0) hi
  simp only [Matrix.mul_apply, corner, Matrix.of_apply, Fin.val_zero, firstColumn, Nat.cast_one, mul_one] at h
  change (∑ j, (corner n)⁻¹ (Fin.last n) j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (Fin.last n) 0 at h
  rw [h, Matrix.one_apply]
  cases n <;> simp
