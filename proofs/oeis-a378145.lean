import OMAStatements.S_oeis_a378145
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a378145

noncomputable def yy : PowerSeries ℤ := PowerSeries.X * Cx

lemma hCx : Cx ^ 2 * PowerSeries.X + 1 = Cx := by
  have h := PowerSeries.catalanSeries_sq_mul_X_add_one
  have h2 := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) h
  have e : PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries = Cx := by
    ext n
    simp [Cx, PowerSeries.catalanSeries_coeff]
  simpa [e] using h2

lemma hy : HasSubst yy := by
  apply HasSubst.of_constantCoeff_zero'
  simp [yy]

lemma hCy : Cx * (1 - yy) = 1 := by
  unfold yy
  have := hCx
  linear_combination (-1 : PowerSeries ℤ) * this

lemma coeff_yy_pow_zero (j n : ℕ) (h : n < j) (Q : PowerSeries ℤ) :
    PowerSeries.coeff n (yy ^ j) = 0 := by
  have : (PowerSeries.X : PowerSeries ℤ) ^ j ∣ yy ^ j := by
    unfold yy
    rw [mul_pow]
    exact dvd_mul_right _ _
  rw [PowerSeries.X_pow_dvd_iff] at this
  exact this n h

lemma lemL (n : ℕ) (F Q : PowerSeries ℤ) :
    PowerSeries.coeff n ((F.subst yy : PowerSeries ℤ) * Q) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F * PowerSeries.coeff n (yy ^ d * Q) := by
  have hdvd : (PowerSeries.X : PowerSeries ℤ) ^ (n + 1) ∣
      F - ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F • (PowerSeries.X : PowerSeries ℤ) ^ d := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, hm]
  obtain ⟨H, hH⟩ := hdvd
  have hF : F = ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F • (PowerSeries.X : PowerSeries ℤ) ^ d
      + PowerSeries.X ^ (n + 1) * H := by
    rw [← hH]; ring
  have hs : (F.subst yy : PowerSeries ℤ) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d F • yy ^ d + yy ^ (n + 1) * (H.subst yy : PowerSeries ℤ) := by
    have h1 : (F.subst yy : PowerSeries ℤ) = (substAlgHom hy : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ) F := by
      rw [coe_substAlgHom]
    rw [h1]
    conv_lhs => rw [hF]
    rw [map_add, map_sum, map_mul, map_pow, substAlgHom_X]
    congr 1
    · apply Finset.sum_congr rfl
      intro d _
      rw [map_smul, map_pow, substAlgHom_X]
    · rw [coe_substAlgHom]
  rw [hs, add_mul, map_add, Finset.sum_mul, map_sum]
  have h0 : PowerSeries.coeff n (yy ^ (n + 1) * (H.subst yy : PowerSeries ℤ) * Q) = 0 := by
    have : (PowerSeries.X : PowerSeries ℤ) ^ (n + 1) ∣ yy ^ (n + 1) * (H.subst yy : PowerSeries ℤ) * Q := by
      unfold yy
      rw [mul_pow]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_mul_right _ _) _) _
    rw [PowerSeries.X_pow_dvd_iff] at this
    exact this n (Nat.lt_succ_self n)
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro d _
  rw [smul_mul_assoc, LinearMap.map_smul_of_tower, smul_eq_mul]

lemma T_eq (n j : ℕ) : T n j = PowerSeries.coeff n (yy ^ j * (1 + yy)) := by
  unfold T yy; congr 1; ring

lemma T_zero (n j : ℕ) (h : n < j) : T n j = 0 := by
  rw [T_eq]
  have : (PowerSeries.X : PowerSeries ℤ) ^ j ∣ yy ^ j * (1 + yy) := by
    unfold yy
    rw [mul_pow]
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  rw [PowerSeries.X_pow_dvd_iff] at this
  exact this n h

lemma hs1 : ((PowerSeries.mk 1 : PowerSeries ℤ).subst yy : PowerSeries ℤ) = Cx := by
  have h := PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  have h2 := congrArg (substAlgHom hy : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ) h
  rw [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom] at h2
  have h3 := hCy
  calc ((PowerSeries.mk 1 : PowerSeries ℤ).subst yy : PowerSeries ℤ)
      = ((PowerSeries.mk 1 : PowerSeries ℤ).subst yy : PowerSeries ℤ) * (Cx * (1 - yy)) := by rw [h3, mul_one]
    _ = Cx * (((PowerSeries.mk 1 : PowerSeries ℤ).subst yy : PowerSeries ℤ) * (1 - yy)) := by ring
    _ = Cx := by rw [h2, mul_one]

lemma hspow (F : PowerSeries ℤ) (d : ℕ) :
    ((F ^ d).subst yy : PowerSeries ℤ) = (F.subst yy : PowerSeries ℤ) ^ d := by
  have := subst_pow (a := yy) hy F d
  exact this

lemma part1 (n k d : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range (n - k + 1), ((i + (d + 1) - 1).choose i : ℤ) * T n (i + k) =
        T (n + (d + 1)) ((d + 1) + k) := by
  have key := lemL n ((PowerSeries.mk 1 : PowerSeries ℤ) ^ (d + 1)) (yy ^ k * (1 + yy))
  rw [hspow, hs1] at key
  have hcoef : ∀ i, PowerSeries.coeff i ((PowerSeries.mk 1 : PowerSeries ℤ) ^ (d + 1)) = ((i + (d + 1) - 1).choose i : ℤ) := by
    intro i
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    simp only [PowerSeries.coeff_mk]
    have : i + (d + 1) - 1 = d + i := by omega
    rw [this, Nat.choose_symm_add]
  have hL : ∑ i ∈ Finset.range (n + 1), ((i + (d + 1) - 1).choose i : ℤ) * T n (i + k) =
      PowerSeries.coeff n (Cx ^ (d + 1) * (yy ^ k * (1 + yy))) := by
    rw [key]
    apply Finset.sum_congr rfl
    intro i _
    rw [hcoef, T_eq]
    congr 2
    ring
  have hsub : ∑ i ∈ Finset.range (n - k + 1), ((i + (d + 1) - 1).choose i : ℤ) * T n (i + k) =
      ∑ i ∈ Finset.range (n + 1), ((i + (d + 1) - 1).choose i : ℤ) * T n (i + k) := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i hi hi2
      simp only [Finset.mem_range] at hi hi2
      rw [T_zero n (i + k) (by omega), mul_zero]
  rw [hsub, hL, T_eq]
  have : yy ^ (d + 1 + k) * (1 + yy) = PowerSeries.X ^ (d + 1) * (Cx ^ (d + 1) * (yy ^ k * (1 + yy))) := by
    have e : yy ^ (d + 1 + k) = PowerSeries.X ^ (d + 1) * Cx ^ (d + 1) * yy ^ k := by
      unfold yy; ring
    rw [e]; ring
  rw [this, PowerSeries.coeff_X_pow_mul']
  simp [add_comm n (d + 1)]

lemma part2 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((1 + k / 2 : ℕ) : ℤ) * T n k = (catalan (n + 1) : ℤ) := by
  have key := lemL n (PowerSeries.mk fun k => ((1 + k / 2 : ℕ) : ℤ)) (1 + yy)
  have hF2 : (1 + PowerSeries.X) * (PowerSeries.mk fun k => ((1 + k / 2 : ℕ) : ℤ)) =
      (PowerSeries.mk 1 : PowerSeries ℤ) ^ 2 := by
    ext k
    have e2 : (PowerSeries.mk 1 : PowerSeries ℤ) ^ 2 = PowerSeries.mk fun n => ((1 + n).choose 1 : ℤ) := by
      have := PowerSeries.mk_one_pow_eq_mk_choose_add (S := ℤ) 1
      simpa using this
    rw [e2, add_mul, one_mul, map_add, PowerSeries.coeff_mk]
    cases k with
    | zero => simp
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      simp only [PowerSeries.coeff_mk, Nat.choose_one_right]
      push_cast
      omega
  have h2 := congrArg (substAlgHom hy : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ) hF2
  rw [map_mul, map_add, map_one, substAlgHom_X, map_pow, coe_substAlgHom, hs1] at h2
  have h3 : ((PowerSeries.mk fun k => ((1 + k / 2 : ℕ) : ℤ)).subst yy : PowerSeries ℤ) * (1 + yy) = Cx ^ 2 := by
    rw [mul_comm]; exact h2
  rw [h3] at key
  have hc : PowerSeries.coeff n (Cx ^ 2) = (catalan (n + 1) : ℤ) := by
    have := congrArg (PowerSeries.coeff (n + 1)) hCx
    rw [map_add, PowerSeries.coeff_succ_mul_X] at this
    simp [Cx] at this
    simpa [Cx] using this
  rw [← hc, key]
  apply Finset.sum_congr rfl
  intro k _
  rw [T_eq]
  simp

end OMA.S_oeis_a378145

theorem OMA.solution : type_of% @OMA.S_oeis_a378145.main := by
  refine ⟨?_, fun n => OMA.S_oeis_a378145.part2 n⟩
  intro n k m hk hm
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  exact OMA.S_oeis_a378145.part1 n k d hk


