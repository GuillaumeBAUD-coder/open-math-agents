import OMAStatements.S_oeis_a115526
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a115526

theorem a115526_zeros_two_mul (m : ℕ) (hm : 0 < m) : zeros (2 * m) = zeros m + 1 := by
  unfold zeros
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [h1, h2, List.count_cons_self]

theorem a115526_zeros_two_mul_add_one (m : ℕ) : zeros (2 * m + 1) = zeros m := by
  unfold zeros
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, List.count_cons_of_ne (by norm_num)]

theorem a115526_step (i : ℕ) (hi : 0 < i) :
    sign i * ((zeros (i + 2) : ℚ) - (zeros (earlier i + 2) : ℚ)) = 1 := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · have hk : 0 < k := by omega
    have e1 : earlier (2 * k) = k - 1 := by unfold earlier; simp
    have e2 : 2 * k + 2 = 2 * (k + 1) := by ring
    have e3 : k - 1 + 2 = k + 1 := by omega
    have s : sign (2 * k) = 1 := by unfold sign; simp
    rw [e1, e2, e3, s, a115526_zeros_two_mul _ (by omega)]
    push_cast; ring
  · have e1 : earlier (2 * k + 1) = 2 * k := by unfold earlier; simp
    have e2 : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
    have e3 : 2 * k + 2 = 2 * (k + 1) := by ring
    have s : sign (2 * k + 1) = -1 := by unfold sign; simp
    rw [e1, e2, e3, s, a115526_zeros_two_mul_add_one, a115526_zeros_two_mul _ (by omega)]
    push_cast; ring

theorem a115526_lower (n : ℕ) : (corner n).IsLowerTriangular := by
  intro i j hij
  simp only [corner, Matrix.of_apply]
  have hij' : i < j := hij
  have h1 : ¬ j = i := by intro h; rw [h] at hij'; exact lt_irrefl _ hij'
  rw [if_neg h1]
  split_ifs with h2 h3
  · exfalso
    have : (earlierCol i).val < i.val := by
      simp only [earlierCol, earlier]; split <;> omega
    rw [← h3] at this
    have : j.val < i.val := this
    exact absurd hij' (not_lt.mpr (le_of_lt this))
  · simp
  · simp

theorem a115526_det (n : ℕ) : IsUnit (corner n).det := by
  rw [Matrix.det_of_isLowerTriangular _ (a115526_lower n)]
  apply IsUnit.mk0
  rw [Finset.prod_ne_zero_iff]
  intro i _
  simp only [corner, Matrix.of_apply, if_true]
  have hlt : (earlierCol i).val < i.val ∨ i.val = 0 := by
    simp only [earlierCol, earlier]; split <;> omega
  have h0 : (if 0 < i.val then (if i = earlierCol i then sign i.val else 0) else 0) = 0 := by
    split_ifs with a b
    · exfalso; rw [← b] at hlt; omega
    · rfl
    · rfl
  rw [h0, sub_zero]
  unfold sign
  split_ifs <;> norm_num

theorem a115526_mulVec (n : ℕ) :
    (corner n).mulVec (fun i => (zeros (i.val + 2) : ℚ)) = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, corner, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ i]
  by_cases hi : 0 < i.val
  · simp only [hi, if_true]
    rw [Finset.sum_ite_eq' Finset.univ (earlierCol i)]
    simp only [Finset.mem_univ, if_true]
    rw [← mul_sub]
    have := a115526_step i.val hi
    simpa [earlierCol] using this
  · simp only [hi, if_false, Finset.sum_const_zero, sub_zero, Finset.mem_univ, if_true]
    have hi0 : i.val = 0 := by omega
    rw [hi0]
    unfold sign zeros
    norm_num

theorem a115526_main : ∀ n : ℕ,
    (∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j) = (zeros (n+2) : ℚ) := by
  intro n
  have key : (corner n)⁻¹.mulVec (fun _ => (1 : ℚ)) = fun i => (zeros (i.val + 2) : ℚ) := by
    rw [← a115526_mulVec n, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (a115526_det n),
      Matrix.one_mulVec]
  have h := congrFun key (Fin.last n)
  simpa [Matrix.mulVec, dotProduct] using h

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a115526.main := OMA.Helpers.a115526_main
