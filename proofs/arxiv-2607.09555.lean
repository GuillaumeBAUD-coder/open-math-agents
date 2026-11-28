import OMAStatements.S_arxiv_2607_09555
import Mathlib

namespace OMA.P_arxiv_2607_09555

open OMA.S_arxiv_2607_09555

private noncomputable def Cbg : ℝ :=
  ∑' d : ℕ, (d : ℝ) * kappa d

private noncomputable def betaConst : ℝ :=
  1 - kappa 3

private noncomputable def deltaPen (n : ℕ) : ℝ :=
  fRef n - fKS n

private noncomputable def gammaConst : ℝ :=
  1 - 2 * alphaConst / 3

private lemma kappa_zero : kappa 0 = 0 := by
  simp [kappa]

private lemma kappa_one : kappa 1 = 1 := by
  simp [kappa]

private lemma kappa_two : kappa 2 = 1 := by
  simp [kappa]

private lemma kappa_three : kappa 3 = 2 / (2 : ℝ) ^ 6 - 1 / (2 : ℝ) ^ 12 := by
  simp [kappa]

private lemma kappa_nonneg (d : ℕ) : 0 ≤ kappa d := by
  unfold kappa
  split_ifs with h0 h2
  · norm_num
  · norm_num
  · have hd : (2 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      have : 2 ≤ d - 1 := by omega
      exact_mod_cast this
    have hpow : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := by
      have : (2 : ℝ) ^ 6 ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hd 6
      linarith
    have hpos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) ^ 6 := by positivity
    have h12 : ((d - 1 : ℕ) : ℝ) ^ 12 = (((d - 1 : ℕ) : ℝ) ^ 6) ^ 2 := by ring
    rw [h12, sub_nonneg, div_le_div_iff₀ (by positivity) hpos]
    nlinarith

private lemma kappa_le_one (d : ℕ) : kappa d ≤ 1 := by
  unfold kappa
  split_ifs with h0 h2
  · norm_num
  · norm_num
  · have hd : (2 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      have : 2 ≤ d - 1 := by omega
      exact_mod_cast this
    have h6 : (64 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := by
      have : (2 : ℝ) ^ 6 ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hd 6
      linarith
    have h1 : 2 / ((d - 1 : ℕ) : ℝ) ^ 6 ≤ 2 / 64 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h6
    have h2' : (0 : ℝ) ≤ 1 / ((d - 1 : ℕ) : ℝ) ^ 12 := by positivity
    linarith

private lemma kappa_le_kappa_three {d : ℕ} (hd : 3 ≤ d) : kappa d ≤ kappa 3 := by
  have hd0 : d ≠ 0 := by omega
  have hd2 : ¬ d ≤ 2 := by omega
  rw [kappa, if_neg hd0, if_neg hd2, kappa_three]
  set x : ℝ := 1 / ((d - 1 : ℕ) : ℝ) ^ 6
  set y : ℝ := 1 / (2 : ℝ) ^ 6
  have hx0 : 0 ≤ x := by positivity
  have hxy : x ≤ y := by
    have h2le : (2 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      have : 2 ≤ d - 1 := by omega
      exact_mod_cast this
    have h6 : (2 : ℝ) ^ 6 ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) h2le 6
    exact one_div_le_one_div_of_le (by positivity) h6
  have hy1 : y ≤ 1 := by
    change 1 / (2 : ℝ) ^ 6 ≤ 1
    norm_num
  have hsqx : 1 / ((d - 1 : ℕ) : ℝ) ^ 12 = x ^ 2 := by
    simp only [x]
    ring
  have hsqy : 1 / (2 : ℝ) ^ 12 = y ^ 2 := by
    simp only [y]
    ring
  have h2x : 2 / ((d - 1 : ℕ) : ℝ) ^ 6 = 2 * x := by
    simp only [x]
    ring
  have h2y : 2 / (2 : ℝ) ^ 6 = 2 * y := by
    simp only [y]
    ring
  rw [hsqx, hsqy, h2x, h2y]
  nlinarith

private lemma mul_kappa_le (d : ℕ) :
    (d : ℝ) * kappa d ≤ 16 * ((1 : ℝ) / (d : ℝ) ^ 2) := by
  rcases d with _ | _ | _ | m
  · simp [kappa]
  · simp [kappa]
  · simp [kappa]; norm_num
  · set d : ℕ := m + 3
    have hd0 : d ≠ 0 := by omega
    have hd2 : ¬ d ≤ 2 := by omega
    rw [kappa, if_neg hd0, if_neg hd2]
    have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : 1 ≤ d := by omega
      rw [Nat.cast_sub this, Nat.cast_one]
    have hdge3 : (3 : ℝ) ≤ (d : ℝ) := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hhalf : (d : ℝ) / 2 ≤ ((d - 1 : ℕ) : ℝ) := by
      rw [hd1]; linarith
    have hge1 : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      rw [hd1]; linarith
    have hpow3 : ((d : ℝ) / 2) ^ 3 ≤ ((d - 1 : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hhalf 3
    have hpow6 : ((d - 1 : ℕ) : ℝ) ^ 3 ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := by
      have : ((d - 1 : ℕ) : ℝ) ^ 3 * 1 ≤ ((d - 1 : ℕ) : ℝ) ^ 3 * ((d - 1 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hge1) (by positivity)
      linarith [show ((d - 1 : ℕ) : ℝ) ^ 6 = ((d - 1 : ℕ) : ℝ) ^ 3 * ((d - 1 : ℕ) : ℝ) ^ 3 by ring]
    have hbound : (d : ℝ) ^ 3 / 8 ≤ ((d - 1 : ℕ) : ℝ) ^ 6 := by
      have : ((d : ℝ) / 2) ^ 3 = (d : ℝ) ^ 3 / 8 := by ring
      linarith
    have h12 : (0 : ℝ) ≤ 1 / ((d - 1 : ℕ) : ℝ) ^ 12 := by positivity
    have hstep1 : 2 / ((d - 1 : ℕ) : ℝ) ^ 6 - 1 / ((d - 1 : ℕ) : ℝ) ^ 12 ≤
        2 / ((d - 1 : ℕ) : ℝ) ^ 6 := by linarith
    have hstep2 : 2 / ((d - 1 : ℕ) : ℝ) ^ 6 ≤ 2 / ((d : ℝ) ^ 3 / 8) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hbound
    have hstep3 : (d : ℝ) * (2 / ((d : ℝ) ^ 3 / 8)) = 16 * ((1 : ℝ) / (d : ℝ) ^ 2) := by
      have hdpos : (d : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left (hstep1.trans hstep2) (show (0 : ℝ) ≤ (d : ℝ) by positivity)]

private lemma summable_mul_kappa : Summable (fun d : ℕ => (d : ℝ) * kappa d) := by
  have h2 : Summable (fun d : ℕ => 16 * ((1 : ℝ) / (d : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 16
  exact Summable.of_nonneg_of_le
    (fun d => mul_nonneg (Nat.cast_nonneg d) (kappa_nonneg d))
    mul_kappa_le h2

private lemma summable_kappa : Summable kappa := by
  exact Summable.of_nonneg_of_le kappa_nonneg
    (fun d => by
      rcases d with _ | d
      · simp [kappa]
      · have h1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_pos d
        nlinarith [kappa_nonneg (d + 1)])
    summable_mul_kappa

private lemma Cbg_nonneg : 0 ≤ Cbg :=
  tsum_nonneg (fun d => mul_nonneg (Nat.cast_nonneg d) (kappa_nonneg d))

private lemma sigma0_ge_two : 2 ≤ sigma0 := by
  have hsum : ∑ d ∈ Finset.range 3, kappa d ≤ sigma0 :=
    summable_kappa.sum_le_tsum (Finset.range 3) (fun d _ => kappa_nonneg d)
  have h3 : ∑ d ∈ Finset.range 3, kappa d = 2 := by
    simp [Finset.sum_range_succ, kappa_zero, kappa_one, kappa_two]
    norm_num
  linarith

private lemma tail_kappa_le (m : ℕ) (hm : 1 ≤ m) :
    sigma0 - ∑ d ∈ Finset.range m, kappa d ≤ Cbg / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  rw [le_div_iff₀ hmpos]
  have hpart : ∀ K : ℕ,
      (∑ d ∈ Finset.range (K + m), kappa d - ∑ d ∈ Finset.range m, kappa d) * (m : ℝ) ≤ Cbg := by
    intro K
    have hsub : ∑ d ∈ Finset.range (K + m), kappa d - ∑ d ∈ Finset.range m, kappa d =
        ∑ k ∈ Finset.range K, kappa (m + k) := by
      rw [add_comm K m, Finset.sum_range_add]; ring
    rw [hsub, Finset.sum_mul]
    calc ∑ k ∈ Finset.range K, kappa (m + k) * (m : ℝ)
        ≤ ∑ k ∈ Finset.range K, ((m + k : ℕ) : ℝ) * kappa (m + k) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have hle : (m : ℝ) ≤ ((m + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right m k
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hle (kappa_nonneg (m + k))
      _ ≤ ∑ d ∈ Finset.range (K + m), (d : ℝ) * kappa d := by
          rw [add_comm K m, Finset.sum_range_add]
          exact le_add_of_nonneg_left
            (Finset.sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg d) (kappa_nonneg d)))
      _ ≤ Cbg :=
          summable_mul_kappa.sum_le_tsum (Finset.range (K + m))
            (fun d _ => mul_nonneg (Nat.cast_nonneg d) (kappa_nonneg d))
  have htend : Filter.Tendsto (fun K : ℕ =>
      (∑ d ∈ Finset.range (K + m), kappa d - ∑ d ∈ Finset.range m, kappa d) * (m : ℝ))
      Filter.atTop (nhds ((sigma0 - ∑ d ∈ Finset.range m, kappa d) * (m : ℝ))) := by
    have h1 : Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, kappa d) Filter.atTop (nhds sigma0) :=
      summable_kappa.hasSum.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun K : ℕ => ∑ d ∈ Finset.range (K + m), kappa d) Filter.atTop (nhds sigma0) :=
      h1.comp (Filter.tendsto_add_atTop_nat m)
    exact (h2.sub_const _).mul_const (m : ℝ)
  exact le_of_tendsto htend (Filter.Eventually.of_forall hpart)

/-! ### Exact algebraic identities for `layerEnergy` -/

private noncomputable def bgSum (D : ℕ) : ℝ :=
  ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
    kappa (j.val - i.val)

private noncomputable def fieldAt (D : ℕ) (k : Fin D) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin D => k.val < j.val), kappa (j.val - k.val)) +
  (∑ i ∈ Finset.univ.filter (fun i : Fin D => i.val < k.val), kappa (k.val - i.val))

private lemma bgSum_eq (D : ℕ) :
    bgSum D = ∑ d ∈ Finset.range D, ((D - d : ℕ) : ℝ) * kappa d := by
  induction D with
  | zero => simp [bgSum]
  | succ D ih =>
    unfold bgSum
    rw [Fin.sum_univ_castSucc]
    have hlast :
        ∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => (Fin.last D).val < j.val),
          kappa (j.val - (Fin.last D).val) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last] at hj
      omega
    rw [hlast, add_zero]
    have hinner : ∀ i : Fin D,
        (∑ j ∈ Finset.univ.filter (fun j : Fin (D + 1) => i.castSucc.val < j.val),
          kappa (j.val - i.castSucc.val)) =
        (∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
          kappa (j.val - i.val)) + kappa (D - i.val) := by
      intro i
      rw [Finset.sum_filter, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, i.isLt, ↓reduceIte]
      rw [← Finset.sum_filter]
    simp_rw [hinner, Finset.sum_add_distrib]
    change bgSum D + ∑ i : Fin D, kappa (D - i.val) = _
    rw [ih]
    have hbij : ∑ i : Fin D, kappa (D - i.val) = ∑ d ∈ Finset.range (D + 1), kappa d := by
      rw [Finset.sum_range_succ']
      rw [kappa_zero, add_zero]
      rw [Fin.sum_univ_eq_sum_range (fun k => kappa (D - k)) D]
      refine Finset.sum_bij (fun k _ => D - 1 - k) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro a ha b hb hab
        simp only [Finset.mem_range] at ha hb
        omega
      · intro d hd
        simp only [Finset.mem_range] at hd
        refine ⟨D - 1 - d, by simp; omega, by omega⟩
      · intro k hk
        simp only [Finset.mem_range] at hk
        congr 1; omega
    rw [hbij, Finset.sum_range_succ (f := fun d => ((D + 1 - d : ℕ) : ℝ) * kappa d)]
    rw [Finset.sum_range_succ (f := kappa)]
    have hD1 : ((D + 1 - D : ℕ) : ℝ) * kappa D = kappa D := by
      have : D + 1 - D = 1 := by omega
      rw [this]; simp
    rw [hD1]
    have hcombine :
        (∑ d ∈ Finset.range D, ((D - d : ℕ) : ℝ) * kappa d) +
        (∑ d ∈ Finset.range D, kappa d) =
        ∑ d ∈ Finset.range D, ((D + 1 - d : ℕ) : ℝ) * kappa d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun d hd => ?_)
      simp only [Finset.mem_range] at hd
      have hsub : ((D + 1 - d : ℕ) : ℝ) = ((D - d : ℕ) : ℝ) + 1 := by
        have : D + 1 - d = (D - d) + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_one]
      rw [hsub]; ring
    linarith

private lemma bgSum_le (D : ℕ) : bgSum D ≤ (D : ℝ) * sigma0 := by
  rw [bgSum_eq]
  have h1 : ∑ d ∈ Finset.range D, ((D - d : ℕ) : ℝ) * kappa d ≤
      ∑ d ∈ Finset.range D, (D : ℝ) * kappa d := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hle : ((D - d : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.sub_le D d
    exact mul_le_mul_of_nonneg_right hle (kappa_nonneg d)
  rw [← Finset.mul_sum] at h1
  have h2 : ∑ d ∈ Finset.range D, kappa d ≤ sigma0 :=
    summable_kappa.sum_le_tsum (Finset.range D) (fun d _ => kappa_nonneg d)
  nlinarith

private lemma bgSum_ge (D : ℕ) (hD : 1 ≤ D) :
    (D : ℝ) * sigma0 - 2 * Cbg ≤ bgSum D := by
  rw [bgSum_eq]
  have hrew : ∑ d ∈ Finset.range D, ((D - d : ℕ) : ℝ) * kappa d =
      (D : ℝ) * (∑ d ∈ Finset.range D, kappa d) -
      ∑ d ∈ Finset.range D, (d : ℝ) * kappa d := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_range] at hd
    rw [Nat.cast_sub (le_of_lt hd)]
    ring
  rw [hrew]
  have htail := tail_kappa_le D hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hmul : (D : ℝ) * (sigma0 - ∑ d ∈ Finset.range D, kappa d) ≤ Cbg := by
    have := mul_le_mul_of_nonneg_left htail (le_of_lt hDpos)
    rwa [mul_div_cancel₀ _ (ne_of_gt hDpos)] at this
  have hC : ∑ d ∈ Finset.range D, (d : ℝ) * kappa d ≤ Cbg :=
    summable_mul_kappa.sum_le_tsum (Finset.range D)
      (fun d _ => mul_nonneg (Nat.cast_nonneg d) (kappa_nonneg d))
  linarith

private lemma fieldAt_eq (D : ℕ) (k : Fin D) :
    fieldAt D k =
      (∑ d ∈ Finset.range (D - k.val), kappa d) +
      (∑ d ∈ Finset.range (k.val + 1), kappa d) := by
  unfold fieldAt
  congr 1
  · rw [show D - k.val = (D - 1 - k.val) + 1 by omega]
    rw [Finset.sum_range_succ', kappa_zero, add_zero]
    refine Finset.sum_bij (fun j _ => j.val - k.val - 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      ext; omega
    · intro d hd
      simp only [Finset.mem_range] at hd
      refine ⟨⟨k.val + d + 1, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · dsimp; omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; omega
  · rw [Finset.sum_range_succ', kappa_zero, add_zero]
    refine Finset.sum_bij (fun i _ => k.val - i.val - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_range]; omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      ext; omega
    · intro d hd
      simp only [Finset.mem_range] at hd
      refine ⟨⟨k.val - 1 - d, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · dsimp; omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      congr 1; omega

private lemma fieldAt_le (D : ℕ) (k : Fin D) : fieldAt D k ≤ 2 * sigma0 := by
  rw [fieldAt_eq]
  have h1 := summable_kappa.sum_le_tsum (Finset.range (D - k.val)) (fun d _ => kappa_nonneg d)
  have h2 := summable_kappa.sum_le_tsum (Finset.range (k.val + 1)) (fun d _ => kappa_nonneg d)
  unfold sigma0
  linarith

private lemma fieldAt_ge (D : ℕ) (k : Fin D) (m : ℕ) (hm : 1 ≤ m)
    (hm1 : m ≤ D - k.val) (hm2 : m ≤ k.val + 1) :
    2 * sigma0 - 2 * Cbg / (m : ℝ) ≤ fieldAt D k := by
  rw [fieldAt_eq]
  have hmono1 : ∑ d ∈ Finset.range m, kappa d ≤ ∑ d ∈ Finset.range (D - k.val), kappa d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm1) (fun d _ _ => kappa_nonneg d)
  have hmono2 : ∑ d ∈ Finset.range m, kappa d ≤ ∑ d ∈ Finset.range (k.val + 1), kappa d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm2) (fun d _ _ => kappa_nonneg d)
  have htail := tail_kappa_le m hm
  have hdiv : 2 * Cbg / (m : ℝ) = 2 * (Cbg / (m : ℝ)) := by ring
  linarith

private lemma sum_pairs_linear {D : ℕ} (e : Fin D → ℝ) :
    (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
      kappa (j.val - i.val) * (e i + e j)) =
    ∑ k : Fin D, e k * fieldAt D k := by
  have hsplit :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * (e i + e j)) =
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e i) +
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e j) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  have hpart1 :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e i) =
      ∑ k : Fin D, e k * (∑ j ∈ Finset.univ.filter (fun j : Fin D => k.val < j.val),
        kappa (j.val - k.val)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hpart2 :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e j) =
      ∑ k : Fin D, e k * (∑ i ∈ Finset.univ.filter (fun i : Fin D => i.val < k.val),
        kappa (k.val - i.val)) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> ring
  rw [hpart1, hpart2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold fieldAt; ring

private lemma sum_sq_add_two_pairs {D : ℕ} (e : Fin D → ℝ) :
    (∑ k : Fin D, e k) ^ 2 =
      (∑ k : Fin D, (e k) ^ 2) +
      2 * ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val), e i * e j := by
  have hsq : (∑ k : Fin D, e k) ^ 2 = ∑ i : Fin D, ∑ j : Fin D, e i * e j := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hsq]
  have hsplit : ∀ i : Fin D,
      (∑ j : Fin D, e i * e j) =
      (e i) ^ 2 +
      (∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val), e i * e j) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val), e i * e j) := by
    intro i
    have hlt : ∑ j : Fin D, e i * e j =
        ∑ j : Fin D, ((if j = i then e i * e j else 0) +
          (if i.val < j.val then e i * e j else 0) +
          (if j.val < i.val then e i * e j else 0)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases lt_trichotomy i.val j.val with h | h | h
      · have hne : j ≠ i := fun h' => by subst h'; exact lt_irrefl _ h
        have hnot : ¬ j.val < i.val := not_lt.mpr (le_of_lt h)
        simp [hne, h, hnot]
      · have heq : j = i := Fin.ext h.symm
        simp [heq]
      · have hne : j ≠ i := fun h' => by subst h'; exact lt_irrefl _ h
        have hnot : ¬ i.val < j.val := not_lt.mpr (le_of_lt h)
        simp [hne, h, hnot]
    rw [hlt, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.sum_filter, sq]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hsym :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val), e i * e j) =
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val), e i * e j) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    split_ifs <;> ring
  rw [hsym]; ring

private lemma layerEnergy_fKS_decomp {N D : ℕ} (p : Fin D → ℕ) (hp : IsValidProfile N D p) :
    let e : Fin D → ℝ := fun k => ((p k - 1 : ℕ) : ℝ)
    let E : ℝ := ∑ k : Fin D, e k
    layerEnergy fKS p =
      -bgSum D - E / 2 - E ^ 2 / 2 - (∑ k : Fin D, e k * fieldAt D k) +
      ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        (1 - kappa (j.val - i.val)) * e i * e j := by
  intro e E
  have hpk : ∀ k : Fin D, (p k : ℝ) = 1 + e k := by
    intro k
    have h1 := hp.1 k
    simp only [e]
    rw [Nat.cast_sub h1, Nat.cast_one]
    ring
  have hf : ∀ k : Fin D, fKS (p k) = -(e k + (e k) ^ 2) / 2 := by
    intro k
    unfold fKS
    have h1 := hp.1 k
    have hcast : ((p k * (p k - 1) : ℕ) : ℝ) = (p k : ℝ) * ((p k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
    rw [hcast, hpk k]
    dsimp only [e]
    ring
  unfold layerEnergy
  simp_rw [hf]
  have hsumf : ∑ k : Fin D, -(e k + (e k) ^ 2) / 2 =
      -E / 2 - (∑ k : Fin D, (e k) ^ 2) / 2 := by
    dsimp only [E]
    have hterm : ∀ k : Fin D, -(e k + (e k) ^ 2) / 2 = -(e k) / 2 - (e k) ^ 2 / 2 := fun k => by ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_neg_distrib]
  have hpair :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * (p i : ℝ) * (p j : ℝ)) =
      bgSum D + (∑ k : Fin D, e k * fieldAt D k) +
      ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e i * e j := by
    have hexp : ∀ i j : Fin D,
        kappa (j.val - i.val) * (p i : ℝ) * (p j : ℝ) =
        kappa (j.val - i.val) +
        kappa (j.val - i.val) * (e i + e j) +
        kappa (j.val - i.val) * e i * e j := by
      intro i j
      rw [hpk i, hpk j]
      ring
    simp_rw [hexp, Finset.sum_add_distrib]
    rw [sum_pairs_linear e]
    rfl
  have hq :
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        (1 - kappa (j.val - i.val)) * e i * e j) =
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val), e i * e j) -
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        kappa (j.val - i.val) * e i * e j) := by
    simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  have hsq := sum_sq_add_two_pairs e
  dsimp only [E] at hsumf ⊢
  linarith

private lemma surplus_sum_eq {N D : ℕ} (p : Fin D → ℕ) (hp : IsValidProfile N D p) :
    (∑ k : Fin D, ((p k - 1 : ℕ) : ℝ)) = (N : ℝ) - (D : ℝ) := by
  have hsum : ∑ k : Fin D, (p k : ℝ) = (N : ℝ) := by
    exact_mod_cast hp.2
  have h1 : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) = ∑ k : Fin D, ((p k : ℝ) - 1) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.cast_sub (hp.1 k), Nat.cast_one]
  rw [h1, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-! ### Per-layer penalty bounds and residue-class refinement bound -/

private lemma alphaConst_pos : 0 < alphaConst := by
  unfold alphaConst V6star; norm_num

private lemma two_alpha_le_beta : 2 * alphaConst ≤ betaConst := by
  unfold alphaConst betaConst V6star
  rw [kappa_three]
  norm_num

private lemma gammaConst_pos : 0 < gammaConst := by
  unfold gammaConst alphaConst V6star; norm_num

private lemma deltaPen_lower (n : ℕ) :
    alphaConst * (((n : ℝ) - 4) ^ 2 - 0) ≤ deltaPen n ∨ n ≤ 4 := by
  by_cases h4 : n ≤ 4
  · exact Or.inr h4
  · left
    push Not at h4
    unfold deltaPen fRef fKS alphaConst V5star V6star
    rcases n with _ | _ | _ | _ | _ | _ | _ | m
    · omega
    · omega
    · omega
    · omega
    · omega
    · norm_num
    · norm_num
    · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hcast : (((m + 7) * (m + 7 - 1) : ℕ) : ℝ) = ((m : ℝ) + 7) * ((m : ℝ) + 6) := by
        have : m + 7 - 1 = m + 6 := by omega
        rw [this, Nat.cast_mul]; push_cast; ring
      rw [hcast]
      push_cast
      nlinarith

private lemma deltaPen_ge_quad (e : ℕ) :
    alphaConst * ((e : ℝ) ^ 2 - 6 * (e : ℝ)) ≤ deltaPen (e + 1) := by
  rcases deltaPen_lower (e + 1) with h | h
  · have hcast : ((e + 1 : ℕ) : ℝ) = (e : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    have hge : (e : ℝ) ^ 2 - 6 * (e : ℝ) ≤ ((e : ℝ) + 1 - 4) ^ 2 - 0 := by nlinarith
    have ha := alphaConst_pos
    nlinarith
  · have he3 : e ≤ 3 := by omega
    have h0 : deltaPen (e + 1) = 0 := by
      unfold deltaPen fRef fKS
      interval_cases e <;> norm_num
    rw [h0]
    have he : (e : ℝ) ≤ 3 := by exact_mod_cast he3
    have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
    have ha := alphaConst_pos
    have hneg : (e : ℝ) ^ 2 - 6 * (e : ℝ) ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hneg

private lemma fRef_ge_seven {n : ℕ} (hn : 7 ≤ n) :
    fRef n = ((n * (n - 1) : ℕ) : ℝ) / 30 * V6star := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rfl

private lemma deltaPen_upper (n : ℕ) :
    deltaPen n ≤ alphaConst * ((n * (n - 1) : ℕ) : ℝ) := by
  by_cases hn : 7 ≤ n
  · unfold deltaPen
    rw [fRef_ge_seven hn]
    unfold fKS alphaConst
    ring_nf
    exact le_refl _
  · interval_cases n <;> unfold deltaPen fRef fKS alphaConst V5star V6star <;> norm_num

private lemma layerEnergy_fKS_lower {N D : ℕ} (p : Fin D → ℕ) (hp : IsValidProfile N D p) :
    let e : ℝ := (N : ℝ) - (D : ℝ);
    -sigma0 * (N : ℝ) - e ^ 2 / 2 - (1 / 2 + sigma0) * e ≤ layerEnergy fKS p := by
  intro e
  have hdec := layerEnergy_fKS_decomp p hp
  dsimp only at hdec
  have hsum : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) = e := surplus_sum_eq p hp
  rw [hsum] at hdec
  have hbg := bgSum_le D
  have hfield : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * fieldAt D k ≤ 2 * sigma0 * e := by
    calc ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * fieldAt D k
        ≤ ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * (2 * sigma0) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul_of_nonneg_left (fieldAt_le D k) (Nat.cast_nonneg _)
      _ = (∑ k : Fin D, ((p k - 1 : ℕ) : ℝ)) * (2 * sigma0) := by rw [Finset.sum_mul]
      _ = 2 * sigma0 * e := by rw [hsum]; ring
  have hrem : 0 ≤ ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
      (1 - kappa (j.val - i.val)) * ((p i - 1 : ℕ) : ℝ) * ((p j - 1 : ℕ) : ℝ) := by
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
    have hk : 0 ≤ 1 - kappa (j.val - i.val) := by linarith [kappa_le_one (j.val - i.val)]
    exact mul_nonneg (mul_nonneg hk (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hND : (D : ℝ) = (N : ℝ) - e := by simp only [e]; ring
  nlinarith

private lemma layerEnergy_fRef_lower {N D : ℕ} (p : Fin D → ℕ) (hp : IsValidProfile N D p) :
    let e : ℝ := (N : ℝ) - (D : ℝ);
    -sigma0 * (N : ℝ) - gammaConst * e ^ 2 / 2 -
      (1 / 2 + sigma0 + 6 * alphaConst) * e ≤ layerEnergy fRef p := by
  intro e
  set ev : Fin D → ℝ := fun k => ((p k - 1 : ℕ) : ℝ)
  have hsum : ∑ k : Fin D, ev k = e := surplus_sum_eq p hp
  have hdiff : layerEnergy fRef p = layerEnergy fKS p + ∑ k : Fin D, deltaPen (p k) := by
    unfold layerEnergy deltaPen
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  have hdec := layerEnergy_fKS_decomp p hp
  dsimp only at hdec
  change layerEnergy fKS p = -bgSum D - (∑ k, ev k) / 2 - (∑ k, ev k) ^ 2 / 2 -
    (∑ k, ev k * fieldAt D k) +
    ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
      (1 - kappa (j.val - i.val)) * ev i * ev j at hdec
  rw [hsum] at hdec
  have hbg := bgSum_le D
  have hfield : ∑ k : Fin D, ev k * fieldAt D k ≤ 2 * sigma0 * e := by
    calc ∑ k : Fin D, ev k * fieldAt D k
        ≤ ∑ k : Fin D, ev k * (2 * sigma0) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul_of_nonneg_left (fieldAt_le D k) (Nat.cast_nonneg _)
      _ = (∑ k : Fin D, ev k) * (2 * sigma0) := by rw [Finset.sum_mul]
      _ = 2 * sigma0 * e := by rw [hsum]; ring
  -- Residue classes mod 3
  let C (r : Fin 3) : Finset (Fin D) := Finset.univ.filter (fun k : Fin D => k.val % 3 = r.val)
  let S (r : Fin 3) : ℝ := ∑ k ∈ C r, ev k
  let T (r : Fin 3) : ℝ := ∑ k ∈ C r, (ev k) ^ 2
  have hpartS : S 0 + S 1 + S 2 = e := by
    rw [← hsum]
    have hdisj : ∑ r : Fin 3, S r = ∑ k : Fin D, ev k := by
      simp only [S, C, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hmod : k.val % 3 < 3 := Nat.mod_lt _ (by omega)
      rw [Finset.sum_eq_single ⟨k.val % 3, hmod⟩]
      · simp
      · intro r _ hne
        have : k.val % 3 ≠ r.val := fun h => hne (Fin.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hdisj, Fin.sum_univ_three]
  have hpartT : T 0 + T 1 + T 2 = ∑ k : Fin D, (ev k) ^ 2 := by
    have hdisj : ∑ r : Fin 3, T r = ∑ k : Fin D, (ev k) ^ 2 := by
      simp only [T, C, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hmod : k.val % 3 < 3 := Nat.mod_lt _ (by omega)
      rw [Finset.sum_eq_single ⟨k.val % 3, hmod⟩]
      · simp
      · intro r _ hne
        have : k.val % 3 ≠ r.val := fun h => hne (Fin.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hdisj, Fin.sum_univ_three]
  -- Pair bound on each residue class
  have hres_pair : ∀ r : Fin 3,
      (S r) ^ 2 - T r = 2 * ∑ i ∈ C r,
        ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j := by
    intro r
    have hsq : (S r) ^ 2 = ∑ i ∈ C r, ∑ j ∈ C r, ev i * ev j := by
      dsimp only [S]
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
    rw [hsq]
    have hsp : ∀ i ∈ C r,
        (∑ j ∈ C r, ev i * ev j) =
        (ev i) ^ 2 +
        (∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j) +
        (∑ j ∈ (C r).filter (fun j : Fin D => j.val < i.val), ev i * ev j) := by
      intro i hi
      have htri : ∑ j ∈ C r, ev i * ev j =
          ∑ j ∈ C r, ((if j = i then ev i * ev j else 0) +
            (if i.val < j.val then ev i * ev j else 0) +
            (if j.val < i.val then ev i * ev j else 0)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rcases lt_trichotomy i.val j.val with h | h | h
        · have hne : j ≠ i := fun h' => by subst h'; exact lt_irrefl _ h
          have hnot : ¬ j.val < i.val := not_lt.mpr (le_of_lt h)
          simp [hne, h, hnot]
        · have heq : j = i := Fin.ext h.symm
          simp [heq]
        · have hne : j ≠ i := fun h' => by subst h'; exact lt_irrefl _ h
          have hnot : ¬ i.val < j.val := not_lt.mpr (le_of_lt h)
          simp [hne, h, hnot]
      rw [htri, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', hi, ↓reduceIte, ← Finset.sum_filter, sq]
    rw [Finset.sum_congr rfl hsp, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hsym :
        (∑ i ∈ C r, ∑ j ∈ (C r).filter (fun j : Fin D => j.val < i.val), ev i * ev j) =
        (∑ i ∈ C r, ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
      split_ifs <;> ring
    rw [hsym]; dsimp only [T]; ring
  have hT_le_S2 : ∀ r : Fin 3, T r ≤ (S r) ^ 2 := by
    intro r
    have h := hres_pair r
    have hnn : 0 ≤ ∑ i ∈ C r, ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    linarith
  have hbeta_bound :
      (betaConst / 2) * (((S 0) ^ 2 - T 0) + ((S 1) ^ 2 - T 1) + ((S 2) ^ 2 - T 2)) ≤
      ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        (1 - kappa (j.val - i.val)) * ev i * ev j := by
    have hstep1 :
        betaConst * ∑ r : Fin 3, ∑ i ∈ C r,
          ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j ≤
        ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
          (1 - kappa (j.val - i.val)) * ev i * ev j := by
      rw [Finset.mul_sum]
      have hrew_lhs :
          (∑ r : Fin 3, betaConst * ∑ i ∈ C r,
            ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j) =
          ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
            if i.val % 3 = j.val % 3 then betaConst * ev i * ev j else 0 := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        have hswap : ∀ r : Fin 3,
            (∑ i ∈ C r, ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val),
              betaConst * ev i * ev j) =
            ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
              if i.val % 3 = r.val ∧ j.val % 3 = r.val then betaConst * ev i * ev j else 0 := by
          intro r
          simp only [C, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs with hi
          · refine Finset.sum_congr rfl (fun j _ => ?_)
            split_ifs with hlt hj <;> simp_all
          · symm
            refine Finset.sum_eq_zero (fun j _ => ?_)
            split_ifs with hlt hboth
            · exact absurd hboth.1 hi
            · rfl
            · rfl
        simp_rw [hswap]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hmod : i.val % 3 = j.val % 3
        · rw [if_pos hmod]
          have hlt3 : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
          rw [Finset.sum_eq_single ⟨i.val % 3, hlt3⟩]
          · simp [hmod]
          · intro r _ hne
            have : i.val % 3 ≠ r.val := fun h => hne (Fin.ext h.symm)
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [if_neg hmod]
          refine Finset.sum_eq_zero (fun r _ => ?_)
          have : ¬ (i.val % 3 = r.val ∧ j.val % 3 = r.val) := fun ⟨h1, h2⟩ => hmod (h1.trans h2.symm)
          simp [this]
      rw [hrew_lhs]
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j hj => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      split_ifs with hmod
      · have hge3 : 3 ≤ j.val - i.val := by omega
        have hk : kappa (j.val - i.val) ≤ kappa 3 := kappa_le_kappa_three hge3
        have hbk : betaConst ≤ 1 - kappa (j.val - i.val) := by
          unfold betaConst; linarith
        have henn : 0 ≤ ev i * ev j := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        nlinarith
      · have hk : 0 ≤ 1 - kappa (j.val - i.val) := by linarith [kappa_le_one (j.val - i.val)]
        exact mul_nonneg (mul_nonneg hk (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hsumr :
        (betaConst / 2) * (((S 0) ^ 2 - T 0) + ((S 1) ^ 2 - T 1) + ((S 2) ^ 2 - T 2)) =
        betaConst * ∑ r : Fin 3, ∑ i ∈ C r,
          ∑ j ∈ (C r).filter (fun j : Fin D => i.val < j.val), ev i * ev j := by
      rw [Fin.sum_univ_three, hres_pair 0, hres_pair 1, hres_pair 2]
      ring
    linarith
  have hpen_bound :
      alphaConst * (T 0 + T 1 + T 2 - 6 * e) ≤ ∑ k : Fin D, deltaPen (p k) := by
    rw [hpartT, ← hsum]
    calc alphaConst * (∑ k : Fin D, (ev k) ^ 2 - 6 * ∑ k : Fin D, ev k)
        = ∑ k : Fin D, alphaConst * ((ev k) ^ 2 - 6 * ev k) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ k : Fin D, deltaPen (p k) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have hpk : p k = (p k - 1) + 1 := by have := hp.1 k; omega
          rw [hpk]
          exact deltaPen_ge_quad (p k - 1)
  have hcs : e ^ 2 ≤ 3 * ((S 0) ^ 2 + (S 1) ^ 2 + (S 2) ^ 2) := by
    rw [← hpartS]; nlinarith [sq_nonneg (S 0 - S 1), sq_nonneg (S 1 - S 2), sq_nonneg (S 2 - S 0)]
  have hT_le : T 0 + T 1 + T 2 ≤ (S 0) ^ 2 + (S 1) ^ 2 + (S 2) ^ 2 := by
    linarith [hT_le_S2 0, hT_le_S2 1, hT_le_S2 2]
  have hab := two_alpha_le_beta
  have ha := alphaConst_pos
  have hND : (D : ℝ) = (N : ℝ) - e := by simp only [e]; ring
  have hcomb : alphaConst / 3 * e ^ 2 - 6 * alphaConst * e ≤
      (∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
        (1 - kappa (j.val - i.val)) * ev i * ev j) +
      ∑ k : Fin D, deltaPen (p k) := by
    have hstep : (betaConst / 2 - alphaConst) *
        (((S 0) ^ 2 + (S 1) ^ 2 + (S 2) ^ 2) - (T 0 + T 1 + T 2)) ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  unfold gammaConst
  nlinarith

/-! ### Nonempty boundedness of valid-profile energy set & explicit upper-bound profiles -/

private lemma profile_set_bddBelow (f : ℕ → ℝ) (N D : ℕ) :
    BddBelow { E : ℝ | ∃ p : Fin D → ℕ, IsValidProfile N D p ∧ layerEnergy f p = E } := by
  let S : Set (Fin D → Fin (N + 1)) := Set.univ
  have hfin : (Set.image (fun q : Fin D → Fin (N + 1) =>
      layerEnergy f (fun k => (q k).val)) S).Finite :=
    Set.Finite.image _ Set.finite_univ
  refine hfin.bddBelow.mono ?_
  rintro E ⟨p, hp, rfl⟩
  have hle : ∀ k : Fin D, p k < N + 1 := by
    intro k
    have h1 : p k ≤ ∑ j : Fin D, p j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 : ∑ j : Fin D, p j = N := hp.2
    omega
  refine ⟨fun k => ⟨p k, hle k⟩, Set.mem_univ _, rfl⟩

private lemma minLayerEnergy_ge_of_forall {f : ℕ → ℝ} {N D : ℕ} {B : ℝ}
    (hDN : 1 ≤ D) (hle : D ≤ N)
    (hB : ∀ p : Fin D → ℕ, IsValidProfile N D p → B ≤ layerEnergy f p) :
    B ≤ minLayerEnergy f N D := by
  unfold minLayerEnergy
  have hne : { E : ℝ | ∃ p : Fin D → ℕ, IsValidProfile N D p ∧ layerEnergy f p = E }.Nonempty := by
    let p : Fin D → ℕ := fun k => if k.val = 0 then N - D + 1 else 1
    refine ⟨layerEnergy f p, p, ⟨?_, ?_⟩, rfl⟩
    · intro k; dsimp only [p]; split_ifs <;> omega
    · dsimp only [p]
      let z0 : Fin D := ⟨0, by omega⟩
      have h0 : z0 ∈ Finset.univ := Finset.mem_univ _
      rw [← Finset.add_sum_erase _ _ h0]
      have hrest : ∑ k ∈ Finset.univ.erase z0, (if k.val = 0 then N - D + 1 else 1) =
          D - 1 := by
        have hconst : ∀ k ∈ Finset.univ.erase z0,
            (if k.val = 0 then N - D + 1 else 1) = 1 := by
          intro k hk
          have hne : k ≠ z0 := (Finset.mem_erase.mp hk).1
          have hv : k.val ≠ 0 := fun h => hne (Fin.ext h)
          simp [hv]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem h0,
          Finset.card_univ, Fintype.card_fin]
        simp
      rw [hrest]; simp [z0]; omega
  exact le_csInf hne (by rintro E ⟨p, hp, rfl⟩; exact hB p hp)

private lemma minLayerEnergy_le_of_profile {f : ℕ → ℝ} {N D : ℕ}
    (p : Fin D → ℕ) (hp : IsValidProfile N D p) :
    minLayerEnergy f N D ≤ layerEnergy f p :=
  csInf_le (profile_set_bddBelow f N D) ⟨p, hp, rfl⟩

/-- Centered single-layer pile for KS upper bound (`D ≥ 4`, `N - D ≤ D`). -/
private lemma minLayerEnergy_fKS_upper {N D : ℕ} (hD4 : 4 ≤ D) (hDN : D ≤ N) (heD : N - D ≤ D) :
    let e : ℝ := (N : ℝ) - (D : ℝ)
    minLayerEnergy fKS N D ≤
      -sigma0 * (N : ℝ) - e ^ 2 / 2 - (1 / 2 + sigma0) * e + 8 * Cbg := by
  intro e
  set c : Fin D := ⟨D / 2, by omega⟩
  let p : Fin D → ℕ := fun k => if k = c then 1 + (N - D) else 1
  have hp : IsValidProfile N D p := by
    refine ⟨fun k => by dsimp only [p]; split_ifs <;> omega, ?_⟩
    dsimp only [p]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
    have hrest : ∑ k ∈ Finset.univ.erase c, (if k = c then 1 + (N - D) else 1) = D - 1 := by
      have hc : ∀ k ∈ Finset.univ.erase c, (if k = c then 1 + (N - D) else 1) = 1 := by
        intro k hk; simp [(Finset.mem_erase.mp hk).1]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c),
        Finset.card_univ, Fintype.card_fin]
      simp
    rw [hrest]; simp; omega
  refine (minLayerEnergy_le_of_profile p hp).trans ?_
  have hdec := layerEnergy_fKS_decomp p hp
  dsimp only at hdec
  have hsum : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) = e := surplus_sum_eq p hp
  rw [hsum] at hdec
  have hev : ∀ k : Fin D, ((p k - 1 : ℕ) : ℝ) = if k = c then e else 0 := by
    intro k
    dsimp only [p]
    split_ifs with hk
    · simp only [e]
      have : 1 + (N - D) - 1 = N - D := by omega
      rw [this, Nat.cast_sub hDN]
    · simp
  have hrem0 : ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
      (1 - kappa (j.val - i.val)) * ((p i - 1 : ℕ) : ℝ) * ((p j - 1 : ℕ) : ℝ) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j hj => ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hev i, hev j]
    split_ifs with hi hj'
    · subst hi hj'; omega
    · simp
    · simp
    · simp
  have hfield : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * fieldAt D k = e * fieldAt D c := by
    simp_rw [hev]
    rw [Finset.sum_eq_single c]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ c) h
  rw [hrem0, hfield, add_zero] at hdec
  have hbg := bgSum_ge D (by omega)
  have he0 : 0 ≤ e := by
    simp only [e]; linarith [show (D : ℝ) ≤ (N : ℝ) by exact_mod_cast hDN]
  have hm2 : 1 ≤ D / 2 := by omega
  have hfge2 := fieldAt_ge D c (D / 2) hm2 (by dsimp [c]; omega) (by dsimp [c]; omega)
  have he_le_D : e ≤ (D : ℝ) := by
    simp only [e]
    have hcast : ((N - D : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast heD
    rw [Nat.cast_sub hDN] at hcast; exact hcast
  have hD_le_3half : (D : ℝ) ≤ 3 * ((D / 2 : ℕ) : ℝ) := by
    have : D ≤ 3 * (D / 2) := by omega
    exact_mod_cast this
  have hm2pos : (0 : ℝ) < ((D / 2 : ℕ) : ℝ) := by exact_mod_cast hm2
  have he_div : e * (2 * Cbg / ((D / 2 : ℕ) : ℝ)) ≤ 6 * Cbg := by
    rw [mul_div_assoc', div_le_iff₀ hm2pos]
    have hC := Cbg_nonneg
    nlinarith
  have hND : (D : ℝ) = (N : ℝ) - e := by simp only [e]; ring
  nlinarith

/-- Centered 3-layer spread profile for `fRef` upper bound (`D ≥ 12`, `N - D ≤ D`). -/
private lemma minLayerEnergy_fRef_upper {N D : ℕ} (hD12 : 12 ≤ D) (hDN : D ≤ N) (heD : N - D ≤ D) :
    let e : ℝ := (N : ℝ) - (D : ℝ)
    minLayerEnergy fRef N D ≤
      -sigma0 * (N : ℝ) - gammaConst * e ^ 2 / 2 + 10 * Cbg + 3 * alphaConst := by
  intro e
  set s : ℕ := N - D
  set q : ℕ := s / 3
  set r : ℕ := s % 3
  set e0 : ℕ := q
  set e1 : ℕ := q + if 1 ≤ r then 1 else 0
  set e2 : ℕ := q + if 2 ≤ r then 1 else 0
  have hes : e0 + e1 + e2 = s := by
    dsimp only [e0, e1, e2, q, r]; split_ifs <;> omega
  set c : ℕ := D / 2
  set i0 : Fin D := ⟨c - 1, by omega⟩
  set i1 : Fin D := ⟨c, by omega⟩
  set i2 : Fin D := ⟨c + 1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  have h02 : i0 ≠ i2 := by intro h; have := congrArg Fin.val h; dsimp [i0, i2] at this; omega
  have h12 : i1 ≠ i2 := by intro h; have := congrArg Fin.val h; dsimp [i1, i2] at this; omega
  let p : Fin D → ℕ := fun k =>
    if k = i0 then 1 + e0
    else if k = i1 then 1 + e1
    else if k = i2 then 1 + e2
    else 1
  have hp : IsValidProfile N D p := by
    refine ⟨fun k => by dsimp only [p]; split_ifs <;> omega, ?_⟩
    have hsum1 : ∑ k : Fin D, p k = (∑ k : Fin D, 1) + (∑ k : Fin D, (p k - 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      dsimp only [p]; split_ifs <;> omega
    rw [hsum1]
    have hones : ∑ _k : Fin D, (1 : ℕ) = D := by simp
    have hsurp : ∑ k : Fin D, (p k - 1) = e0 + e1 + e2 := by
      let S3 : Finset (Fin D) := {i0, i1, i2}
      rw [← Finset.sum_subset (Finset.subset_univ S3)]
      · simp only [S3]
        rw [Finset.sum_insert (by simp [h01, h02]),
          Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
        dsimp only [p]
        simp [h01.symm, h02.symm, h12.symm]
        omega
      · intro k _ hk
        simp only [S3, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        dsimp only [p]
        simp [hk.1, hk.2.1, hk.2.2]
    rw [hones, hsurp, hes]
    dsimp only [s]; omega
  refine (minLayerEnergy_le_of_profile p hp).trans ?_
  have hdiff : layerEnergy fRef p = layerEnergy fKS p + ∑ k : Fin D, deltaPen (p k) := by
    unfold layerEnergy deltaPen
    simp_rw [Finset.sum_sub_distrib]; ring
  rw [hdiff]
  have hdec := layerEnergy_fKS_decomp p hp
  dsimp only at hdec
  have hsum : ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) = e := surplus_sum_eq p hp
  rw [hsum] at hdec
  -- All surplus pairs are at distance ≤ 2, where κ = 1, so the remainder sum is 0!
  have hrem0 : ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
      (1 - kappa (j.val - i.val)) * ((p i - 1 : ℕ) : ℝ) * ((p j - 1 : ℕ) : ℝ) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j hj => ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hi : i = i0 ∨ i = i1 ∨ i = i2
    · by_cases hj' : j = i0 ∨ j = i1 ∨ j = i2
      · have hdist : j.val - i.val = 1 ∨ j.val - i.val = 2 := by
          rcases hi with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
            dsimp [i0, i1, i2] at hj ⊢ <;> omega
        rcases hdist with h1 | h2
        · rw [h1, kappa_one]; ring
        · rw [h2, kappa_two]; ring
      · push Not at hj'
        have hpj : p j = 1 := by dsimp only [p]; simp [hj'.1, hj'.2.1, hj'.2.2]
        rw [hpj]; simp
    · push Not at hi
      have hpi : p i = 1 := by dsimp only [p]; simp [hi.1, hi.2.1, hi.2.2]
      rw [hpi]; simp
  rw [hrem0, add_zero] at hdec
  have he_le_D : e ≤ (D : ℝ) := by
    simp only [e]
    have hcast : ((N - D : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast heD
    rw [Nat.cast_sub hDN] at hcast; exact hcast
  have hm3 : 1 ≤ D / 3 := by omega
  have hf_bound3 : ∀ k : Fin D, (k = i0 ∨ k = i1 ∨ k = i2) →
      2 * sigma0 - 2 * Cbg / ((D / 3 : ℕ) : ℝ) ≤ fieldAt D k := by
    intro k hk
    apply fieldAt_ge D k (D / 3) hm3
    · rcases hk with rfl | rfl | rfl <;> dsimp [i0, i1, i2, c] <;> omega
    · rcases hk with rfl | rfl | rfl <;> dsimp [i0, i1, i2, c] <;> omega
  have hfield3 :
      e * (2 * sigma0 - 2 * Cbg / ((D / 3 : ℕ) : ℝ)) ≤
      ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * fieldAt D k := by
    rw [← hsum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    by_cases hk : k = i0 ∨ k = i1 ∨ k = i2
    · exact mul_le_mul_of_nonneg_left (hf_bound3 k hk) (Nat.cast_nonneg _)
    · push Not at hk
      have hpk : p k = 1 := by dsimp only [p]; simp [hk.1, hk.2.1, hk.2.2]
      rw [hpk]; simp
  have hD_le_4third : (D : ℝ) ≤ 4 * ((D / 3 : ℕ) : ℝ) := by
    have : D ≤ 4 * (D / 3) := by omega
    exact_mod_cast this
  have hm3pos : (0 : ℝ) < ((D / 3 : ℕ) : ℝ) := by exact_mod_cast hm3
  have he0 : 0 ≤ e := by
    simp only [e]; linarith [show (D : ℝ) ≤ (N : ℝ) by exact_mod_cast hDN]
  have he_div : e * (2 * Cbg / ((D / 3 : ℕ) : ℝ)) ≤ 8 * Cbg := by
    rw [mul_div_assoc', div_le_iff₀ hm3pos]
    have hC := Cbg_nonneg
    nlinarith
  -- Penalty sum upper bound
  have hpen : ∑ k : Fin D, deltaPen (p k) ≤
      alphaConst * (e ^ 2 / 3 + e + 3) := by
    have h1 : ∑ k : Fin D, deltaPen (p k) ≤
        ∑ k : Fin D, alphaConst * ((p k * (p k - 1) : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun k _ => deltaPen_upper (p k))
    have h2 : (∑ k : Fin D, ((p k * (p k - 1) : ℕ) : ℝ)) =
        (∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) ^ 2) + e := by
      rw [← hsum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1k := hp.1 k
      rw [Nat.cast_mul, show (p k : ℝ) = ((p k - 1 : ℕ) : ℝ) + 1 by
        rw [Nat.cast_sub h1k, Nat.cast_one]; ring]
      ring
    have hsq3 : (∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) ^ 2) =
        (e0 : ℝ) ^ 2 + (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2 := by
      let S3 : Finset (Fin D) := {i0, i1, i2}
      rw [← Finset.sum_subset (Finset.subset_univ S3)]
      · simp only [S3]
        rw [Finset.sum_insert (by simp [h01, h02]),
          Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
        dsimp only [p]
        simp [h01.symm, h02.symm, h12.symm]
        ring
      · intro k _ hk
        simp only [S3, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        dsimp only [p]
        simp [hk.1, hk.2.1, hk.2.2]
    have he_eq : e = (e0 : ℝ) + (e1 : ℝ) + (e2 : ℝ) := by
      have hcast : ((N - D : ℕ) : ℝ) = (N : ℝ) - (D : ℝ) := Nat.cast_sub hDN
      rw [show e = ((s : ℕ) : ℝ) from hcast.symm, ← hes]
      push_cast; ring
    have hsq_bound : (e0 : ℝ) ^ 2 + (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2 ≤ e ^ 2 / 3 + 3 := by
      rw [he_eq]
      have hd01 : |(e0 : ℝ) - (e1 : ℝ)| ≤ 1 := by
        dsimp only [e0, e1]; split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith only
      have hd02 : |(e0 : ℝ) - (e2 : ℝ)| ≤ 1 := by
        dsimp only [e0, e2]; split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith only
      have hd12 : |(e1 : ℝ) - (e2 : ℝ)| ≤ 1 := by
        dsimp only [e1, e2]; split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith only
      have hs01 : ((e0 : ℝ) - (e1 : ℝ)) ^ 2 ≤ 1 := by nlinarith only [abs_le.mp hd01]
      have hs02 : ((e0 : ℝ) - (e2 : ℝ)) ^ 2 ≤ 1 := by nlinarith only [abs_le.mp hd02]
      have hs12 : ((e1 : ℝ) - (e2 : ℝ)) ^ 2 ≤ 1 := by nlinarith only [abs_le.mp hd12]
      have hid : 3 * ((e0 : ℝ) ^ 2 + (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2) -
          ((e0 : ℝ) + (e1 : ℝ) + (e2 : ℝ)) ^ 2 =
          ((e0 : ℝ) - (e1 : ℝ)) ^ 2 + ((e0 : ℝ) - (e2 : ℝ)) ^ 2 + ((e1 : ℝ) - (e2 : ℝ)) ^ 2 := by ring
      linarith only [hs01, hs02, hs12, hid]
    rw [← Finset.mul_sum, h2, hsq3] at h1
    have ha := alphaConst_pos
    have hmul : alphaConst * ((e0 : ℝ) ^ 2 + (e1 : ℝ) ^ 2 + (e2 : ℝ) ^ 2 + e) ≤
        alphaConst * (e ^ 2 / 3 + e + 3) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsq_bound]) (le_of_lt ha)
    linarith only [h1, hmul]
  have hbg := bgSum_ge D (by omega)
  have hND : (D : ℝ) = (N : ℝ) - e := by simp only [e]; ring
  have hsig := sigma0_ge_two
  have hal : alphaConst ≤ 1 / 2 := by unfold alphaConst V6star; norm_num
  have hlin_neg : 0 ≤ (1 / 2 + sigma0 - alphaConst) * e :=
    mul_nonneg (by linarith only [hsig, hal]) he0
  have hfield_exp : 2 * sigma0 * e - 8 * Cbg ≤
      ∑ k : Fin D, ((p k - 1 : ℕ) : ℝ) * fieldAt D k := by
    have hre : e * (2 * sigma0 - 2 * Cbg / ((D / 3 : ℕ) : ℝ)) =
        2 * sigma0 * e - e * (2 * Cbg / ((D / 3 : ℕ) : ℝ)) := by ring
    linarith only [hfield3, he_div, hre]
  have hgamma_id : -e ^ 2 / 2 + alphaConst * (e ^ 2 / 3 + e + 3) =
      -gammaConst * e ^ 2 / 2 + alphaConst * e + 3 * alphaConst := by
    unfold gammaConst; ring
  have hND_id : -(D : ℝ) * sigma0 - 2 * sigma0 * e = -sigma0 * (N : ℝ) - sigma0 * e := by
    rw [hND]; ring
  linarith only [hdec, hpen, hbg, hfield_exp, hlin_neg, hgamma_id, hND_id]

/-! ### Quadratic-root extraction & final assembly -/

private lemma finite_prefix_bound (g : ℕ → ℝ) (N0 : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, N < N0 → |g N| ≤ M := by
  refine ⟨∑ k ∈ Finset.range N0, |g k|, Finset.sum_nonneg (fun k _ => abs_nonneg _), ?_⟩
  intro N hN
  exact Finset.single_le_sum (fun k _ => abs_nonneg (g k)) (Finset.mem_range.mpr hN)

theorem main_proof :
    ∀ (u : ℕ → ℝ) (u_min u_max : ℝ),
      sigma0 < u_min →
      (∀ N : ℕ, 1 ≤ N → u_min ≤ u N ∧ u N ≤ u_max) →
      (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |((N : ℝ) - (rhoLayer fKS u N : ℝ)) -
          Real.sqrt (2 * (u N - sigma0) * (N : ℝ))| ≤ C) ∧
      (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |((rhoLayer fKS u N : ℝ) - (rhoLayer fRef u N : ℝ)) -
          thetaConst * Real.sqrt (2 * (u N - sigma0) * (N : ℝ))| ≤ C) := by
  intro u u_min u_max hsig_lt hu
  have hdiff_pos : 0 < u_min - sigma0 := sub_pos.mpr hsig_lt
  have hmax_ge : u_min ≤ u_max := by
    have h1 := hu 1 (le_refl 1); linarith
  have humax_pos : 0 < u_max - sigma0 := by linarith
  have hgam_pos := gammaConst_pos
  have hCbg := Cbg_nonneg
  have ha := alphaConst_pos
  -- Constants for large-N bounds
  set K1 : ℝ := Real.sqrt (16 * Cbg) + 1
  set K2 : ℝ := Real.sqrt (2 * (10 * Cbg + 3 * alphaConst) / gammaConst) + 1
  have hK1_pos : 0 < K1 := by positivity
  have hK2_pos : 0 < K2 := by positivity
  set L1 : ℝ := 1 / 2 + sigma0
  set L2 : ℝ := (1 / 2 + sigma0 + 6 * alphaConst) / gammaConst
  -- Pick N0 large enough that for all N ≥ N0:
  -- e1 := ⌈√(2(u_max - σ₀)N) + K1⌉ ≤ N/2 - 12 and e2 := ⌈√(2(u_max - σ₀)N / γ) + K2⌉ ≤ N/2 - 12
  set M_coeff : ℝ := Real.sqrt (2 * (u_max - sigma0) / gammaConst)
  have hM_nn : 0 ≤ M_coeff := Real.sqrt_nonneg _
  set N0 : ℕ := Nat.ceil ((4 * M_coeff + 4 * max K1 K2 + 30) ^ 2) + 30
  have hKS_large : ∀ N : ℕ, N0 ≤ N →
      Real.sqrt (2 * (u N - sigma0) * (N : ℝ)) - L1 ≤ (N : ℝ) - (rhoLayer fKS u N : ℝ) ∧
      (N : ℝ) - (rhoLayer fKS u N : ℝ) ≤ Real.sqrt (2 * (u N - sigma0) * (N : ℝ)) + (K1 + 1) := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have huN := hu N hN1
    have hrad_nn : 0 ≤ 2 * (u N - sigma0) * (N : ℝ) := by
      have : 0 ≤ u N - sigma0 := by linarith
      positivity
    set E : ℝ := Real.sqrt (2 * (u N - sigma0) * (N : ℝ))
    set e0 : ℕ := Nat.ceil (E + K1)
    have he0_ge : E + K1 ≤ (e0 : ℝ) := Nat.le_ceil _
    have he0_lt : (e0 : ℝ) < E + K1 + 1 := Nat.ceil_lt_add_one (by positivity)
    -- Show e0 ≤ N / 2 - 4 so D0 := N - e0 satisfies 4 ≤ D0, D0 ≤ N, N - D0 ≤ D0
    have hE_le : E ≤ M_coeff * Real.sqrt (N : ℝ) := by
      have hgam_le1 : gammaConst ≤ 1 := by unfold gammaConst; linarith
      have h1 : 2 * (u N - sigma0) * (N : ℝ) ≤ (2 * (u_max - sigma0) / gammaConst) * (N : ℝ) := by
        have hratio : u N - sigma0 ≤ (u_max - sigma0) / gammaConst := by
          rw [le_div_iff₀ hgam_pos]
          nlinarith
        have h2 : 2 * (u N - sigma0) ≤ 2 * (u_max - sigma0) / gammaConst := by
          have : 2 * ((u_max - sigma0) / gammaConst) = 2 * (u_max - sigma0) / gammaConst := by ring
          linarith
        exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg N)
      calc E = Real.sqrt (2 * (u N - sigma0) * (N : ℝ)) := rfl
        _ ≤ Real.sqrt ((2 * (u_max - sigma0) / gammaConst) * (N : ℝ)) := Real.sqrt_le_sqrt h1
        _ = M_coeff * Real.sqrt (N : ℝ) := Real.sqrt_mul (by positivity) (N : ℝ)
    have hsqrtN : 4 * M_coeff + 4 * max K1 K2 + 30 ≤ Real.sqrt (N : ℝ) := by
      have hNge : (4 * M_coeff + 4 * max K1 K2 + 30) ^ 2 ≤ (N : ℝ) := by
        have h1 : (Nat.ceil ((4 * M_coeff + 4 * max K1 K2 + 30) ^ 2) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (show Nat.ceil _ ≤ N by omega)
        exact (Nat.le_ceil _).trans h1
      have hsq : Real.sqrt ((4 * M_coeff + 4 * max K1 K2 + 30) ^ 2) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt hNge
      rwa [Real.sqrt_sq (by positivity)] at hsq
    have hsqrtN_pos : 1 ≤ Real.sqrt (N : ℝ) := by linarith [le_max_left K1 K2]
    have h2e0_le_N : 2 * (e0 : ℝ) + 12 ≤ (N : ℝ) := by
      have hNsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      have hK1_le : K1 ≤ max K1 K2 := le_max_left K1 K2
      nlinarith
    have he0_bound : 2 * e0 + 12 ≤ N := by
      have : ((2 * e0 + 12 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact h2e0_le_N
      exact_mod_cast this
    set D0 : ℕ := N - e0
    have hD0_4 : 4 ≤ D0 := by omega
    have hD0_le : D0 ≤ N := by omega
    have heD0 : N - D0 ≤ D0 := by omega
    have hmem_D0 : D0 ∈ { D : ℕ | 1 ≤ D ∧ D ≤ N ∧ minLayerEnergy fKS N D ≤ -(u N) * (N : ℝ) } := by
      refine ⟨by omega, hD0_le, ?_⟩
      have hup := minLayerEnergy_fKS_upper hD0_4 hD0_le heD0
      dsimp only at hup
      have hsub : (N : ℝ) - (D0 : ℝ) = (e0 : ℝ) := by
        have : D0 + e0 = N := by omega
        have hc : (D0 : ℝ) + (e0 : ℝ) = (N : ℝ) := by exact_mod_cast this
        linarith
      rw [hsub] at hup
      have hEsq : E ^ 2 = 2 * (u N - sigma0) * (N : ℝ) := Real.sq_sqrt hrad_nn
      have hK1sq : 16 * Cbg ≤ K1 ^ 2 := by
        have h1 : Real.sqrt (16 * Cbg) ≤ K1 := by linarith
        have h2 : (Real.sqrt (16 * Cbg)) ^ 2 ≤ K1 ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
        rwa [Real.sq_sqrt (by positivity)] at h2
      have hEnn : 0 ≤ E := Real.sqrt_nonneg _
      have he0sq : (E + K1) ^ 2 ≤ (e0 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) he0_ge 2
      have hsig := sigma0_ge_two
      have he0nn : 0 ≤ (e0 : ℝ) := Nat.cast_nonneg e0
      nlinarith
    set S_KS : Set ℕ := { D : ℕ | 1 ≤ D ∧ D ≤ N ∧ minLayerEnergy fKS N D ≤ -(u N) * (N : ℝ) }
    have hbdd : BddAbove S_KS := ⟨N, fun D hD => hD.2.1⟩
    have hne : S_KS.Nonempty := ⟨D0, hmem_D0⟩
    have hrho_ge : D0 ≤ rhoLayer fKS u N := le_csSup hbdd hmem_D0
    have hrho_mem : ∀ D ∈ S_KS, E - L1 ≤ (N : ℝ) - (D : ℝ) := by
      intro D hD
      have hlow := minLayerEnergy_ge_of_forall hD.1 hD.2.1 (fun p hp => layerEnergy_fKS_lower p hp)
      have hle := hD.2.2
      set eD : ℝ := (N : ℝ) - (D : ℝ)
      have heD_nn : 0 ≤ eD := by
        simp only [eD]; linarith [show (D : ℝ) ≤ (N : ℝ) by exact_mod_cast hD.2.1]
      have hL1_def : L1 = 1 / 2 + sigma0 := rfl
      have hL1_nn : 0 ≤ L1 := by linarith only [hL1_def, sigma0_ge_two]
      have hquad : 2 * (u N - sigma0) * (N : ℝ) ≤ (eD + L1) ^ 2 := by
        have hcomb : 2 * (u N - sigma0) * (N : ℝ) ≤ eD ^ 2 + 2 * L1 * eD := by
          rw [hL1_def]; linarith only [hlow, hle]
        have hexp : (eD + L1) ^ 2 = eD ^ 2 + 2 * L1 * eD + L1 ^ 2 := by ring
        linarith only [hcomb, hexp, sq_nonneg L1]
      have hsqrt : E ≤ eD + L1 := by
        have h1 := Real.sqrt_le_sqrt hquad
        rwa [Real.sqrt_sq (by linarith only [heD_nn, hL1_nn])] at h1
      linarith only [hsqrt]
    have hrho_in : rhoLayer fKS u N ∈ S_KS := Nat.sSup_mem hne hbdd
    have hlo := hrho_mem (rhoLayer fKS u N) hrho_in
    have hhi : (N : ℝ) - (rhoLayer fKS u N : ℝ) ≤ E + (K1 + 1) := by
      have h1 : (D0 : ℝ) ≤ (rhoLayer fKS u N : ℝ) := by exact_mod_cast hrho_ge
      have h2 : (D0 : ℝ) + (e0 : ℝ) = (N : ℝ) := by
        exact_mod_cast (show D0 + e0 = N by omega)
      linarith
    exact ⟨hlo, hhi⟩
  -- Same large-N bounds for fRef
  have hRef_large : ∀ N : ℕ, N0 ≤ N →
      Real.sqrt (2 * (u N - sigma0) * (N : ℝ) / gammaConst) - L2 ≤
        (N : ℝ) - (rhoLayer fRef u N : ℝ) ∧
      (N : ℝ) - (rhoLayer fRef u N : ℝ) ≤
        Real.sqrt (2 * (u N - sigma0) * (N : ℝ) / gammaConst) + (K2 + 1) := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have huN := hu N hN1
    have hrad_nn : 0 ≤ 2 * (u N - sigma0) * (N : ℝ) / gammaConst := by
      have : 0 ≤ u N - sigma0 := by linarith
      positivity
    set E2 : ℝ := Real.sqrt (2 * (u N - sigma0) * (N : ℝ) / gammaConst)
    set e0 : ℕ := Nat.ceil (E2 + K2)
    have he0_ge : E2 + K2 ≤ (e0 : ℝ) := Nat.le_ceil _
    have he0_lt : (e0 : ℝ) < E2 + K2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hE2_le : E2 ≤ M_coeff * Real.sqrt (N : ℝ) := by
      have h1 : 2 * (u N - sigma0) * (N : ℝ) / gammaConst ≤
          (2 * (u_max - sigma0) / gammaConst) * (N : ℝ) := by
        rw [mul_div_right_comm]
        have h2 : 2 * (u N - sigma0) / gammaConst ≤ 2 * (u_max - sigma0) / gammaConst :=
          div_le_div_of_nonneg_right (by linarith) (le_of_lt hgam_pos)
        exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg N)
      calc E2 = Real.sqrt (2 * (u N - sigma0) * (N : ℝ) / gammaConst) := rfl
        _ ≤ Real.sqrt ((2 * (u_max - sigma0) / gammaConst) * (N : ℝ)) := Real.sqrt_le_sqrt h1
        _ = M_coeff * Real.sqrt (N : ℝ) := Real.sqrt_mul (by positivity) (N : ℝ)
    have hsqrtN : 4 * M_coeff + 4 * max K1 K2 + 30 ≤ Real.sqrt (N : ℝ) := by
      have hNge : (4 * M_coeff + 4 * max K1 K2 + 30) ^ 2 ≤ (N : ℝ) := by
        have h1 : (Nat.ceil ((4 * M_coeff + 4 * max K1 K2 + 30) ^ 2) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (show Nat.ceil _ ≤ N by omega)
        exact (Nat.le_ceil _).trans h1
      have hsq : Real.sqrt ((4 * M_coeff + 4 * max K1 K2 + 30) ^ 2) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt hNge
      rwa [Real.sqrt_sq (by positivity)] at hsq
    have hsqrtN_pos : 1 ≤ Real.sqrt (N : ℝ) := by linarith [le_max_right K1 K2]
    have h2e0_le_N : 2 * (e0 : ℝ) + 24 ≤ (N : ℝ) := by
      have hNsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      have hK2_le : K2 ≤ max K1 K2 := le_max_right K1 K2
      have hlin : 2 * (e0 : ℝ) + 24 ≤ (4 * M_coeff + 4 * max K1 K2 + 30) * Real.sqrt (N : ℝ) := by
        nlinarith only [he0_lt, hE2_le, hsqrtN_pos, hK2_le, hM_nn, hK2_pos]
      have hsq2 : (4 * M_coeff + 4 * max K1 K2 + 30) * Real.sqrt (N : ℝ) ≤ (Real.sqrt (N : ℝ)) ^ 2 := by
        nlinarith only [hsqrtN, hsqrtN_pos]
      linarith only [hlin, hsq2, hNsq]
    have he0_bound : 2 * e0 + 24 ≤ N := by
      have : ((2 * e0 + 24 : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact h2e0_le_N
      exact_mod_cast this
    set D0 : ℕ := N - e0
    have hD0_12 : 12 ≤ D0 := by omega
    have hD0_le : D0 ≤ N := by omega
    have heD0 : N - D0 ≤ D0 := by omega
    have hmem_D0 : D0 ∈ { D : ℕ | 1 ≤ D ∧ D ≤ N ∧ minLayerEnergy fRef N D ≤ -(u N) * (N : ℝ) } := by
      refine ⟨by omega, hD0_le, ?_⟩
      have hup := minLayerEnergy_fRef_upper hD0_12 hD0_le heD0
      dsimp only at hup
      have hsub : (N : ℝ) - (D0 : ℝ) = (e0 : ℝ) := by
        have hc : (D0 : ℝ) + (e0 : ℝ) = (N : ℝ) := by exact_mod_cast (show D0 + e0 = N by omega)
        linarith
      rw [hsub] at hup
      have hE2sq : E2 ^ 2 = 2 * (u N - sigma0) * (N : ℝ) / gammaConst := Real.sq_sqrt hrad_nn
      have hK2sq : 2 * (10 * Cbg + 3 * alphaConst) / gammaConst ≤ K2 ^ 2 := by
        have h1 : Real.sqrt (2 * (10 * Cbg + 3 * alphaConst) / gammaConst) ≤ K2 := by linarith
        have h2 : (Real.sqrt (2 * (10 * Cbg + 3 * alphaConst) / gammaConst)) ^ 2 ≤ K2 ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
        rwa [Real.sq_sqrt (by positivity)] at h2
      have hE2nn : 0 ≤ E2 := Real.sqrt_nonneg _
      have he0sq : (E2 + K2) ^ 2 ≤ (e0 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) he0_ge 2
      have hgam_mul1 : gammaConst * E2 ^ 2 = 2 * (u N - sigma0) * (N : ℝ) := by
        rw [hE2sq]; exact mul_div_cancel₀ _ (ne_of_gt hgam_pos)
      have hgam_mul2 : 2 * (10 * Cbg + 3 * alphaConst) ≤ gammaConst * K2 ^ 2 := by
        have := mul_le_mul_of_nonneg_left hK2sq (le_of_lt hgam_pos)
        rwa [mul_div_cancel₀ _ (ne_of_gt hgam_pos)] at this
      have hge_sq : gammaConst * (E2 ^ 2 + K2 ^ 2) ≤ gammaConst * (e0 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [he0sq, hE2nn, hK2_pos]) (le_of_lt hgam_pos)
      linarith only [hup, hgam_mul1, hgam_mul2, hge_sq]
    set S_Ref : Set ℕ := { D : ℕ | 1 ≤ D ∧ D ≤ N ∧ minLayerEnergy fRef N D ≤ -(u N) * (N : ℝ) }
    have hbdd : BddAbove S_Ref := ⟨N, fun D hD => hD.2.1⟩
    have hne : S_Ref.Nonempty := ⟨D0, hmem_D0⟩
    have hrho_ge : D0 ≤ rhoLayer fRef u N := le_csSup hbdd hmem_D0
    have hrho_in : rhoLayer fRef u N ∈ S_Ref := Nat.sSup_mem hne hbdd
    have hlo : E2 - L2 ≤ (N : ℝ) - (rhoLayer fRef u N : ℝ) := by
      have hlow := minLayerEnergy_ge_of_forall hrho_in.1 hrho_in.2.1
        (fun p hp => layerEnergy_fRef_lower p hp)
      have hle := hrho_in.2.2
      set eD : ℝ := (N : ℝ) - (rhoLayer fRef u N : ℝ)
      have heD_nn : 0 ≤ eD := by
        simp only [eD]; linarith only [show (rhoLayer fRef u N : ℝ) ≤ (N : ℝ) by exact_mod_cast hrho_in.2.1]
      have hL2_nn : 0 ≤ L2 := by
        dsimp only [L2]
        exact div_nonneg (by linarith only [sigma0_ge_two, ha]) (le_of_lt hgam_pos)
      have hlin_eq : 1 / 2 + sigma0 + 6 * alphaConst = gammaConst * L2 := by
        dsimp only [L2]; exact (mul_div_cancel₀ _ (ne_of_gt hgam_pos)).symm
      have hquad : 2 * (u N - sigma0) * (N : ℝ) / gammaConst ≤ (eD + L2) ^ 2 := by
        rw [div_le_iff₀ hgam_pos]
        have hcomb : 2 * (u N - sigma0) * (N : ℝ) ≤
            gammaConst * eD ^ 2 + 2 * (gammaConst * L2) * eD := by
          rw [← hlin_eq]; linarith only [hlow, hle]
        have hsqL : 0 ≤ gammaConst * L2 ^ 2 := mul_nonneg (le_of_lt hgam_pos) (sq_nonneg L2)
        have hexp : (eD + L2) ^ 2 * gammaConst =
            gammaConst * eD ^ 2 + 2 * (gammaConst * L2) * eD + gammaConst * L2 ^ 2 := by ring
        linarith only [hcomb, hsqL, hexp]
      have hsqrt : E2 ≤ eD + L2 := by
        have h1 := Real.sqrt_le_sqrt hquad
        rwa [Real.sqrt_sq (by linarith only [heD_nn, hL2_nn])] at h1
      linarith only [hsqrt]
    have hhi : (N : ℝ) - (rhoLayer fRef u N : ℝ) ≤ E2 + (K2 + 1) := by
      have h1 : (D0 : ℝ) ≤ (rhoLayer fRef u N : ℝ) := by exact_mod_cast hrho_ge
      have h2 : (D0 : ℝ) + (e0 : ℝ) = (N : ℝ) := by
        exact_mod_cast (show D0 + e0 = N by omega)
      linarith
    exact ⟨hlo, hhi⟩
  -- Combine small N < N0 and large N ≥ N0 for both claims
  constructor
  · obtain ⟨M1, _, hM1⟩ := finite_prefix_bound
      (fun N => ((N : ℝ) - (rhoLayer fKS u N : ℝ)) - Real.sqrt (2 * (u N - sigma0) * (N : ℝ))) N0
    refine ⟨max M1 (max L1 (K1 + 1)), fun N _ => ?_⟩
    by_cases hN : N < N0
    · exact (hM1 N hN).trans (le_max_left _ _)
    · push Not at hN
      obtain ⟨hlo, hhi⟩ := hKS_large N hN
      refine (abs_le.mpr ⟨?_, ?_⟩).trans (le_max_right _ _)
      · linarith [le_max_left L1 (K1 + 1)]
      · linarith [le_max_right L1 (K1 + 1)]
  · obtain ⟨M2, _, hM2⟩ := finite_prefix_bound
      (fun N => ((rhoLayer fKS u N : ℝ) - (rhoLayer fRef u N : ℝ)) -
        thetaConst * Real.sqrt (2 * (u N - sigma0) * (N : ℝ))) N0
    set B2 : ℝ := max (L2 + (K1 + 1)) (L1 + (K2 + 1))
    refine ⟨max M2 B2, fun N hN1 => ?_⟩
    by_cases hN : N < N0
    · exact (hM2 N hN).trans (le_max_left _ _)
    · push Not at hN
      obtain ⟨hKS_lo, hKS_hi⟩ := hKS_large N hN
      obtain ⟨hRef_lo, hRef_hi⟩ := hRef_large N hN
      have huN := hu N hN1
      have hrad_nn : 0 ≤ 2 * (u N - sigma0) * (N : ℝ) := by
        have : 0 ≤ u N - sigma0 := by linarith
        positivity
      have htheta_eq :
          Real.sqrt (2 * (u N - sigma0) * (N : ℝ) / gammaConst) -
          Real.sqrt (2 * (u N - sigma0) * (N : ℝ)) =
          thetaConst * Real.sqrt (2 * (u N - sigma0) * (N : ℝ)) := by
        rw [Real.sqrt_div hrad_nn]
        unfold thetaConst gammaConst
        rw [div_eq_mul_inv]
        ring
      have hdiff_eq :
          (rhoLayer fKS u N : ℝ) - (rhoLayer fRef u N : ℝ) =
          ((N : ℝ) - (rhoLayer fRef u N : ℝ)) - ((N : ℝ) - (rhoLayer fKS u N : ℝ)) := by ring
      refine (abs_le.mpr ⟨?_, ?_⟩).trans (le_max_right _ _)
      · linarith [le_max_left (L2 + (K1 + 1)) (L1 + (K2 + 1))]
      · linarith [le_max_right (L2 + (K1 + 1)) (L1 + (K2 + 1))]

end OMA.P_arxiv_2607_09555

theorem OMA.solution : type_of% @OMA.S_arxiv_2607_09555.main :=
  OMA.P_arxiv_2607_09555.main_proof
