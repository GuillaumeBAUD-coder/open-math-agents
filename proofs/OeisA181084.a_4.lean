import FormalConjectures.OEIS.«181084»

namespace OMA.A181084_a4

open PowerSeries OeisA181084

noncomputable abbrev L : ℚ⟦X⟧ := hannaLog fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0

lemma L0 : coeff 0 L = 0 := by
  simp [L, hannaLog, coeff_mk]

lemma L1 : coeff 1 L = 1 := by
  simp [L, hannaLog, coeff_mk]

lemma L2 : coeff 2 L = 3 / 2 := by
  simp [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  norm_num

lemma L3 : coeff 3 L = 25 / 3 := by
  simp [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  norm_num

lemma L4 : coeff 4 L = 327 / 4 := by
  simp [L, hannaLog, coeff_mk, Finset.sum_Icc_succ_top]
  norm_num

lemma hX : (X : ℚ⟦X⟧) ∣ L := by
  rw [X_dvd_iff]
  simpa using L0

lemma low (d k : ℕ) (hd : k < d) : coeff k (L ^ d) = 0 := by
  have h : (X : ℚ⟦X⟧) ^ d ∣ L ^ d := pow_dvd_pow_of_dvd hX d
  rw [X_pow_dvd_iff] at h
  exact h k hd

lemma pw (d n : ℕ) : coeff n (L ^ (d + 1)) =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 (L ^ d) * coeff p.2 L := by
  rw [pow_succ, coeff_mul]

lemma Q22 : coeff 2 (L ^ 2) = 1 := by
  rw [pw 1 2]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2]

lemma Q23 : coeff 3 (L ^ 2) = 3 := by
  rw [pw 1 3]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2, L3]

lemma Q24 : coeff 4 (L ^ 2) = 227 / 12 := by
  rw [pw 1 4]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2, L3, L4]
  norm_num

lemma Q33 : coeff 3 (L ^ 3) = 1 := by
  rw [pw 2 3]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2, L3, Q22, low 2 0, low 2 1]

lemma Q34 : coeff 4 (L ^ 3) = 9 / 2 := by
  rw [pw 2 4]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2, L3, L4, Q22, Q23, low 2 0, low 2 1]
  norm_num

lemma Q44 : coeff 4 (L ^ 4) = 1 := by
  rw [pw 3 4]
  simp [Finset.Nat.antidiagonal_succ, L0, L1, L2, L3, L4, Q33, low 3 0, low 3 1, low 3 2]

end OMA.A181084_a4

open PowerSeries OMA.A181084_a4 in
theorem OMA.solution : type_of% @OeisA181084.a_4 := by
  have hs : HasSubst L := HasSubst.of_constantCoeff_zero' (by simpa using L0)
  show coeff 4 (subst L (exp ℚ)) = 92
  rw [coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (4 + 1))]
  · simp [Finset.sum_range_succ, coeff_exp, L1, L2, L3, L4, Q22, Q23, Q24, Q33, Q34, Q44, low 2 0, low 2 1, low 3 0, low 3 1, low 3 2, low 4 0, low 4 1, low 4 2, low 4 3]
    norm_num
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hd (by rw [low d 4 (by omega), smul_zero])
