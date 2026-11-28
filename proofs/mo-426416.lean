import OMAStatements.S_mo_426416

theorem OMA.solution : type_of% @OMA.S_mo_426416.main := by
  intro m n A b x hx hAx
  have hinner : ∀ u v : Fin (n + 1) → ℝ,
      ∑ k : Fin (n + 1), u k * (A.transpose.mulVec (A.mulVec v)) k =
      ∑ r : Fin m, (A.mulVec u) r * (A.mulVec v) r := by
    intro u v
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    calc
      ∑ k : Fin (n + 1), u k * ∑ r : Fin m, A r k * ∑ j : Fin (n + 1), A r j * v j
          = ∑ k : Fin (n + 1), ∑ r : Fin m, u k * (A r k * ∑ j : Fin (n + 1), A r j * v j) := by
              refine Finset.sum_congr rfl fun k _ => Finset.mul_sum ..
      _ = ∑ r : Fin m, ∑ k : Fin (n + 1), u k * (A r k * ∑ j : Fin (n + 1), A r j * v j) :=
              Finset.sum_comm
      _ = ∑ r : Fin m, ∑ k : Fin (n + 1), (A r k * u k) * ∑ j : Fin (n + 1), A r j * v j := by
              refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ r : Fin m, (∑ k : Fin (n + 1), A r k * u k) * ∑ j : Fin (n + 1), A r j * v j := by
              refine Finset.sum_congr rfl fun r _ => (Finset.sum_mul ..).symm
  by_cases hinj : Function.Injective A.mulVec
  · let T : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      A.transpose.mulVecLin.comp A.mulVecLin
    have hT_apply : ∀ v, T v = A.transpose.mulVec (A.mulVec v) := fun _ => rfl
    have hT_inj : Function.Injective T := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hsum : ∑ r : Fin m, (A.mulVec v) r ^ 2 = 0 := by
        have h1 := hinner v v
        have hv' : A.transpose.mulVec (A.mulVec v) = 0 := hv
        have h2 : ∑ k : Fin (n + 1), v k * (A.transpose.mulVec (A.mulVec v)) k = 0 := by
          simp only [hv', Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        rw [h2] at h1
        have hsq : ∑ r : Fin m, (A.mulVec v) r ^ 2 = ∑ r : Fin m, (A.mulVec v) r * (A.mulVec v) r :=
          Finset.sum_congr rfl fun r _ => sq _
        rw [hsq, ← h1]
      have hAv : A.mulVec v = 0 := by
        ext r
        have hle : (A.mulVec v) r ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ((A.mulVec v) i)).mp hsum r
            (Finset.mem_univ r)
        exact sq_eq_zero_iff.mp hle
      exact hinj (by rw [hAv, Matrix.mulVec_zero])
    have hT_surj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT_inj
    choose h hh using fun j : Fin (n + 1) => hT_surj (Pi.single j 1)
    have hh_dot : ∀ j k : Fin (n + 1),
        h j k = ∑ r : Fin m, (A.mulVec (h j)) r * (A.mulVec (h k)) r := by
      intro j k
      have h1 := hinner (h j) (h k)
      have h2 : A.transpose.mulVec (A.mulVec (h k)) = Pi.single k 1 := hh k
      rw [h2] at h1
      have h3 : ∑ s : Fin (n + 1), h j s * (Pi.single k (1 : ℝ) : Fin (n + 1) → ℝ) s = h j k := by
        simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte]
      rw [← h3, h1]
    have hh_pos : ∀ j : Fin (n + 1), 0 < h j j := by
      intro j
      have hnn : h j j = ∑ r : Fin m, (A.mulVec (h j)) r ^ 2 := by
        rw [hh_dot j j]
        exact Finset.sum_congr rfl fun r _ => (sq _).symm
      have hge : 0 ≤ h j j := by
        rw [hnn]
        exact Finset.sum_nonneg fun r _ => sq_nonneg _
      refine lt_of_le_of_ne hge (fun h0 => ?_)
      have hsum0 : ∑ r : Fin m, (A.mulVec (h j)) r ^ 2 = 0 := by rw [← hnn, h0]
      have hAv : A.mulVec (h j) = 0 := by
        ext r
        have hle : (A.mulVec (h j)) r ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ((A.mulVec (h j)) i)).mp hsum0 r
            (Finset.mem_univ r)
        exact sq_eq_zero_iff.mp hle
      have hTj : T (h j) = 0 := by
        rw [hT_apply, hAv, Matrix.mulVec_zero]
      have h1 := congr_fun (hh j) j
      rw [hTj] at h1
      simp only [Pi.zero_apply, Pi.single_eq_same, zero_ne_one] at h1
    have hcs : ∀ i k : Fin (n + 1), (h i k) ^ 2 ≤ h i i * h k k := by
      intro i k
      rw [hh_dot i k, hh_dot i i, hh_dot k k]
      have hi2 : ∑ r : Fin m, (A.mulVec (h i)) r * (A.mulVec (h i)) r =
          ∑ r : Fin m, (A.mulVec (h i)) r ^ 2 := Finset.sum_congr rfl fun r _ => (sq _).symm
      have hk2 : ∑ r : Fin m, (A.mulVec (h k)) r * (A.mulVec (h k)) r =
          ∑ r : Fin m, (A.mulVec (h k)) r ^ 2 := Finset.sum_congr rfl fun r _ => (sq _).symm
      rw [hi2, hk2]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => A.mulVec (h i) r)
        (fun r => A.mulVec (h k) r)
    obtain ⟨i, -, hi_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1)))
      (fun k => (x k) ^ 2 / h k k) Finset.univ_nonempty
    let t : ℝ := x i / h i i
    let y : Fin (n + 1) → ℝ := fun k => x k - t * h i k
    refine ⟨i, y, ?_, ?_, ?_⟩
    · dsimp [y, t]
      rw [div_mul_cancel₀ _ (ne_of_gt (hh_pos i)), sub_self]
    · intro k
      dsimp [y]
      by_cases hik : h i k ≤ 0
      · have ht : 0 ≤ t := div_nonneg (hx i) (le_of_lt (hh_pos i))
        have hprod : t * h i k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hik
        exact sub_nonneg.mpr (le_trans hprod (hx k))
      · have hik_pos : 0 < h i k := not_le.mp hik
        have ht : 0 ≤ t := div_nonneg (hx i) (le_of_lt (hh_pos i))
        have hprod_nn : 0 ≤ t * h i k := mul_nonneg ht (le_of_lt hik_pos)
        have hmink : (x i) ^ 2 / h i i ≤ (x k) ^ 2 / h k k := hi_min k (Finset.mem_univ k)
        have hii_pos : 0 < h i i := hh_pos i
        have hkk_pos : 0 < h k k := hh_pos k
        have hsq_le : (t * h i k) ^ 2 ≤ (x k) ^ 2 := by
          calc
            (t * h i k) ^ 2 = ((x i) ^ 2 / (h i i) ^ 2) * (h i k) ^ 2 := by
              dsimp [t]; ring
            _ ≤ ((x i) ^ 2 / (h i i) ^ 2) * (h i i * h k k) := by
              gcongr
              exact hcs i k
            _ = ((x i) ^ 2 / h i i) * h k k := by
              have hii_ne : h i i ≠ 0 := ne_of_gt hii_pos
              field_simp [hii_ne]
            _ ≤ ((x k) ^ 2 / h k k) * h k k := by
              gcongr
            _ = (x k) ^ 2 := by
              exact div_mul_cancel₀ _ (ne_of_gt hkk_pos)
        have hle : t * h i k ≤ x k := (abs_le_of_sq_le_sq' hsq_le (hx k)).2
        exact sub_nonneg.mpr hle
    · intro k hki
      have hy_eq : y = x - t • h i := by
        ext j
        simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hy_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]
      have hTi : A.transpose.mulVec (A.mulVec (h i)) = Pi.single i 1 := hh i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hAx, hTi, Pi.single_apply,
        if_neg hki, mul_zero, sub_zero]
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨u₁, u₂, hu_eq, hu_ne⟩ := hinj
    let v0 : Fin (n + 1) → ℝ := u₁ - u₂
    have hv0_ne : v0 ≠ 0 := sub_ne_zero.mpr hu_ne
    have hv0_ker : A.mulVec v0 = 0 := by
      dsimp [v0]
      rw [Matrix.mulVec_sub, hu_eq, sub_self]
    have hex_nz : ∃ k0 : Fin (n + 1), v0 k0 ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hv0_ne (funext h0)
    obtain ⟨k0, hk0⟩ := hex_nz
    let v : Fin (n + 1) → ℝ := if 0 < v0 k0 then v0 else -v0
    have hv_ker : A.mulVec v = 0 := by
      by_cases hpos : 0 < v0 k0
      · simp only [v, if_pos hpos, hv0_ker]
      · simp only [v, if_neg hpos, Matrix.mulVec_neg, hv0_ker, neg_zero]
    have hvk0 : 0 < v k0 := by
      by_cases hpos : 0 < v0 k0
      · simp only [v, if_pos hpos, hpos]
      · have hneg : v0 k0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hk0
        simp only [v, if_neg hpos, Pi.neg_apply, neg_pos, hneg]
    let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => 0 < v k)
    have hS : S.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ k0, hvk0⟩⟩
    obtain ⟨i, hiS, hi_min⟩ := Finset.exists_min_image S (fun k => x k / v k) hS
    have hvi : 0 < v i := (Finset.mem_filter.mp hiS).2
    let t : ℝ := x i / v i
    have ht : 0 ≤ t := div_nonneg (hx i) (le_of_lt hvi)
    let y : Fin (n + 1) → ℝ := fun k => x k - t * v k
    refine ⟨i, y, ?_, ?_, ?_⟩
    · dsimp [y, t]
      rw [div_mul_cancel₀ _ (ne_of_gt hvi), sub_self]
    · intro k
      dsimp [y]
      by_cases hvk : 0 < v k
      · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hvk⟩
        have hle : t ≤ x k / v k := hi_min k hkS
        have hmul : t * v k ≤ x k := (le_div_iff₀ hvk).mp hle
        exact sub_nonneg.mpr hmul
      · have hvle : v k ≤ 0 := not_lt.mp hvk
        have hprod : t * v k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hvle
        exact sub_nonneg.mpr (le_trans hprod (hx k))
    · intro k _
      have hy_eq : y = x - t • v := by
        ext j
        simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hy_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, hv_ker, smul_zero, sub_zero, hAx]
