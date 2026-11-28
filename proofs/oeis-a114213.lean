import OMAStatements.S_oeis_a114213
import Mathlib.Tactic

open OMA.S_oeis_a114213 Finset Matrix

namespace GeneralizedPascal

private lemma firstColumn (n : ℕ) : entry n 0 = 1 := by
  simp only [entry, Nat.zero_le, if_true, Nat.sub_zero]
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    have hpos : 0 < j := Nat.pos_of_ne_zero hj
    simp [Nat.choose_eq_zero_of_lt hpos]
  · simp

private lemma diagonal (k : ℕ) : entry k k = 1 := by simp [entry]

private lemma det_corner (n : ℕ) : (corner n).det = 1 := by
  have lower : (corner n).IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    change (entry i.val j.val : ℚ) = 0
    simp [entry, Nat.not_le.mpr hij]
  rw [det_of_isLowerTriangular _ lower]
  simp [corner, diagonal]

end GeneralizedPascal

theorem OMA.solution : type_of% @OMA.S_oeis_a114213.main := by
  intro n
  have u : IsUnit (corner n).det := by rw [GeneralizedPascal.det_corner]; exact isUnit_one
  have h := congrArg (fun m : Matrix (Fin (n+1)) (Fin (n+1)) ℚ => m (Fin.last n) 0)
    (nonsing_inv_mul (corner n) u)
  change ∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j * (corner n) j 0 =
    (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (Fin.last n) 0 at h
  have first (j : Fin (n+1)) : corner n j 0 = 1 := by
    simp [corner, GeneralizedPascal.firstColumn]
  simp only [first, mul_one, Matrix.one_apply] at h
  rw [h]
  cases n with
  | zero => simp
  | succ n => simp [Fin.ext_iff]
