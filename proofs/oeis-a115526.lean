import OMAStatements.S_oeis_a115526

open Matrix

namespace BC4G

open OMA.S_oeis_a115526

def fv (n : ℕ) : Fin (n + 1) → ℚ := fun j => (zeros (j.val + 2) : ℚ)

theorem corner_apply {n : ℕ} (i j : Fin (n + 1)) : corner n i j =
    (if j = i then sign i.val else 0) -
    (if 0 < i.val then (if j = earlierCol i then sign i.val else 0) else 0) := rfl

theorem earlierCol_val {n : ℕ} (i : Fin (n + 1)) : (earlierCol i).val = earlier i.val := rfl

theorem earlier_lt (r : ℕ) (hr : 0 < r) : earlier r < r := by
  unfold earlier
  split <;> omega

theorem earlier_le (r : ℕ) : earlier r ≤ r := by
  unfold earlier
  split <;> omega

theorem sign_ne (r : ℕ) : sign r ≠ 0 := by
  unfold sign
  split <;> norm_num

theorem zeros_even (m : ℕ) (hm : 0 < m) : zeros (2 * m) = zeros m + 1 := by
  unfold zeros
  rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * m)]
  rw [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
  simp

theorem zeros_odd (m : ℕ) : zeros (2 * m + 1) = zeros m := by
  unfold zeros
  rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * m + 1)]
  rw [show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
  simp

theorem zeros_two : zeros 2 = 1 := by
  have h1 : zeros 2 = zeros 1 + 1 := zeros_even 1 (by norm_num)
  have h2 : zeros 1 = zeros 0 := zeros_odd 0
  have h3 : zeros 0 = 0 := by
    unfold zeros
    simp
  omega

theorem step (r : ℕ) (hr : 0 < r) :
    sign r * ((zeros (r + 2) : ℚ) - (zeros (earlier r + 2) : ℚ)) = 1 := by
  rcases Nat.even_or_odd' r with ⟨k, hk | hk⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk
    have he : earlier (2 * (k' + 1)) = k' := by
      unfold earlier
      rw [if_pos (show 2 * (k' + 1) % 2 = 0 by omega)]
      omega
    have hs : sign (2 * (k' + 1)) = 1 := by
      unfold sign
      rw [if_pos (show 2 * (k' + 1) % 2 = 0 by omega)]
    rw [he, hs, show 2 * (k' + 1) + 2 = 2 * (k' + 2) by ring, zeros_even (k' + 2) (by omega)]
    push_cast
    ring
  · subst hk
    have he : earlier (2 * k + 1) = 2 * k := by
      unfold earlier
      rw [if_neg (show ¬ ((2 * k + 1) % 2 = 0) by omega)]
      omega
    have hs : sign (2 * k + 1) = -1 := by
      unfold sign
      rw [if_neg (show ¬ ((2 * k + 1) % 2 = 0) by omega)]
    rw [he, hs, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, show 2 * k + 2 = 2 * (k + 1) by ring,
      zeros_odd, zeros_even (k + 1) (by omega)]
    push_cast
    ring

theorem earlierCol_ne {n : ℕ} (i : Fin (n + 1)) (hi : 0 < i.val) : earlierCol i ≠ i := by
  intro h
  have h2 : (earlierCol i).val = i.val := congrArg Fin.val h
  have h3 := earlier_lt i.val hi
  rw [earlierCol_val] at h2
  omega

theorem sum_single {n : ℕ} (a : Fin (n + 1)) (c : ℚ) :
    (∑ x : Fin (n + 1), (if x = a then c else 0) * fv n x) = c * fv n a := by
  rw [Finset.sum_eq_single a]
  · rw [if_pos (show a = a from rfl)]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem mulVec_fv (n : ℕ) : corner n *ᵥ fv n = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  by_cases hi : 0 < i.val
  · have hrow : ∀ x : Fin (n + 1), corner n i x * fv n x =
        (if x = i then sign i.val else 0) * fv n x -
        (if x = earlierCol i then sign i.val else 0) * fv n x := by
      intro x
      rw [corner_apply, if_pos hi, sub_mul]
    simp only [hrow]
    rw [Finset.sum_sub_distrib, sum_single, sum_single, ← mul_sub]
    exact step i.val hi
  · have hi0 : i.val = 0 := by omega
    have hrow : ∀ x : Fin (n + 1), corner n i x * fv n x =
        (if x = i then sign i.val else 0) * fv n x := by
      intro x
      rw [corner_apply, if_neg hi, sub_zero]
    simp only [hrow]
    rw [sum_single]
    have hz : zeros (i.val + 2) = 1 := by
      rw [hi0]
      exact zeros_two
    have hs : sign i.val = 1 := by
      rw [hi0]
      unfold sign
      simp
    simp only [fv]
    rw [hz, hs]
    norm_num

theorem corner_diag {n : ℕ} (i : Fin (n + 1)) : corner n i i = sign i.val := by
  rw [corner_apply, if_pos (show i = i from rfl)]
  by_cases hi : 0 < i.val
  · rw [if_pos hi, if_neg (show ¬ (i = earlierCol i) from Ne.symm (earlierCol_ne i hi)), sub_zero]
  · rw [if_neg hi, sub_zero]

theorem corner_det_ne (n : ℕ) : (corner n).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular (corner n)]
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [corner_diag]
    exact sign_ne i.val
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hlt' : i.val < j.val := hlt
    have hne1 : ¬ (j = i) := by
      intro h
      have h2 : j.val = i.val := congrArg Fin.val h
      omega
    have hne2 : ¬ (j = earlierCol i) := by
      intro h
      have h2 : j.val = (earlierCol i).val := congrArg Fin.val h
      rw [earlierCol_val] at h2
      have h3 := earlier_le i.val
      omega
    rw [corner_apply, if_neg hne1, if_neg hne2, ite_self, sub_self]

end BC4G

theorem OMA.solution : type_of% @OMA.S_oeis_a115526.main := by
  intro n
  have hdet : IsUnit (OMA.S_oeis_a115526.corner n).det :=
    isUnit_iff_ne_zero.mpr (BC4G.corner_det_ne n)
  have hinv : (OMA.S_oeis_a115526.corner n)⁻¹ * OMA.S_oeis_a115526.corner n = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have key : (OMA.S_oeis_a115526.corner n)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = BC4G.fv n := by
    rw [← BC4G.mulVec_fv n, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h := congrFun key (Fin.last n)
  simp only [Matrix.mulVec, dotProduct, mul_one, BC4G.fv, Fin.val_last] at h
  exact h
