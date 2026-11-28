import OMAStatements.S_mo_428655

section
open OMA.S_mo_428655 Matrix

private lemma realify_det {n : ℕ} (B : Mat n) :
    (realify B).det = (B.det : ℝ) := by
  simpa [realify] using ((Int.castRingHom ℝ).map_det B).symm

private lemma det_ne_zero_of_posDef {n : ℕ} {B : Mat n} (h : (realify B).PosDef) :
    B.det ≠ 0 := by
  intro hdet
  have hrdet : (realify B).det = 0 := by
    rw [realify_det, hdet, Int.cast_zero]
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hrdet
  have hpos : 0 < star v ⬝ᵥ (realify B) *ᵥ v := h.dotProduct_mulVec_pos hv
  rw [hmul, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

private lemma realify_isHermitian_iff {n : ℕ} (M : Mat n) :
    (realify M).IsHermitian ↔ M.IsSymm := by
  constructor
  · intro h
    ext i j
    have hij := congr_arg (fun X => X i j) h.eq
    simp only [conjTranspose_apply, star_trivial, realify, map_apply, Int.coe_castRingHom] at hij
    exact Int.cast_injective hij
  · intro h
    ext i j
    simp only [conjTranspose_apply, star_trivial, realify, map_apply, Int.coe_castRingHom]
    exact congrArg (Int.cast : ℤ → ℝ) (congr_arg (fun X => X i j) h.eq)

private lemma vec_cast_dot_mulVec {n : ℕ} (M : Mat n) (v : Fin n → ℤ) :
    (fun i => (v i : ℝ)) ⬝ᵥ (realify M) *ᵥ (fun i => (v i : ℝ)) = ((v ⬝ᵥ M *ᵥ v : ℤ) : ℝ) := by
  simp only [dotProduct, mulVec, realify, map_apply, Int.coe_castRingHom]
  push_cast
  rfl

theorem OMA.solution : type_of% @OMA.S_mo_428655.main := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨!![-1, 0; 0, 0], ?_, ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · refine ⟨-1, by norm_num, ![1, 0], ?_, ?_⟩
      · intro h
        simpa using congr_fun h 0
      · ext i
        fin_cases i <;> simp [realify, mulVec, dotProduct]
    · simp [det_fin_two]
    · intro m B ⟨hpd, hdvd⟩
      have hdet0 : (!![-1, 0; 0, 0] : Mat 2).det = 0 := by simp [det_fin_two]
      rw [hdet0, zero_dvd_iff] at hdvd
      exact det_ne_zero_of_posDef hpd hdvd
  · intro m C L
    let A0 : Mat 2 := !![1, 0; 0, -1]
    have hA_props : ∀ k : ℤ, k ≠ 0 →
        (k • A0).IsSymm ∧ hasNegative (k • A0) ∧ hasNegative (-(k • A0)) ∧ (k • A0).det ≠ 0 := by
      intro k hk
      refine ⟨?_, ?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [A0]
      · rcases lt_or_gt_of_ne hk with hk_neg | hk_pos
        · refine ⟨(k : ℝ), Int.cast_lt_zero.mpr hk_neg, ![1, 0], ?_, ?_⟩
          · intro h
            simpa using congr_fun h 0
          · ext i
            fin_cases i <;> simp [A0, realify, mulVec, dotProduct]
        · refine ⟨-(k : ℝ), neg_lt_zero.mpr (Int.cast_pos.mpr hk_pos), ![0, 1], ?_, ?_⟩
          · intro h
            simpa using congr_fun h 1
          · ext i
            fin_cases i <;> simp [A0, realify, mulVec, dotProduct]
      · rcases lt_or_gt_of_ne hk with hk_neg | hk_pos
        · refine ⟨(k : ℝ), Int.cast_lt_zero.mpr hk_neg, ![0, 1], ?_, ?_⟩
          · intro h
            simpa using congr_fun h 1
          · ext i
            fin_cases i <;> simp [A0, realify, mulVec, dotProduct]
        · refine ⟨-(k : ℝ), neg_lt_zero.mpr (Int.cast_pos.mpr hk_pos), ![1, 0], ?_, ?_⟩
          · intro h
            simpa using congr_fun h 0
          · ext i
            fin_cases i <;> simp [A0, realify, mulVec, dotProduct]
      · have hdet : (k • A0).det = -(k * k) := by
          simp [A0, det_fin_two]
        rw [hdet]
        exact neg_ne_zero.mpr (mul_self_ne_zero.mpr hk)
    let M : Mat m := L A0
    by_cases hM0 : M = 0
    · let k : ℤ := (C.det.natAbs : ℤ) + 2
      have hk : k ≠ 0 := by positivity
      obtain ⟨hsym, hneg1, hneg2, hdet⟩ := hA_props k hk
      refine ⟨k • A0, hsym, hneg1, hneg2, hdet, ?_⟩
      intro ⟨hpd, hdvd⟩
      have hCeq : C + L (k • A0) = C := by
        rw [L.map_smul, show L A0 = M from rfl, hM0, smul_zero, add_zero]
      rw [hCeq] at hpd hdvd
      have hCne : C.det ≠ 0 := det_ne_zero_of_posDef hpd
      have hAdet : (k • A0).det = -(k * k) := by
        simp [A0, det_fin_two]
      rw [hAdet, neg_dvd] at hdvd
      have hdvd_nat : k.natAbs * k.natAbs ∣ C.det.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hdvd
        simpa [Int.natAbs_mul] using this
      have hle : k.natAbs * k.natAbs ≤ C.det.natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hCne) hdvd_nat
      have hk_nat : k.natAbs = C.det.natAbs + 2 := by
        dsimp [k]
        omega
      rw [hk_nat] at hle
      nlinarith
    · by_cases hMsym : M.IsSymm
      · have hex : ∃ v : Fin m → ℤ, v ≠ 0 ∧ v ⬝ᵥ M *ᵥ v ≠ 0 := by
          by_cases hdiag : ∃ i : Fin m, M i i ≠ 0
          · obtain ⟨i, hi⟩ := hdiag
            refine ⟨Pi.single i 1, ?_, ?_⟩
            · intro h
              have := congr_fun h i
              simp at this
            · simp [dotProduct, mulVec, Pi.single_apply, hi]
          · push Not at hdiag
            have hne : ∃ i j : Fin m, M i j ≠ 0 := by
              by_contra h
              push Not at h
              exact hM0 (ext h)
            obtain ⟨i, j, hij⟩ := hne
            have hne_ij : i ≠ j := by
              intro heq
              subst heq
              exact hij (hdiag i)
            refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
            · intro h
              have := congr_fun h i
              simp [hne_ij.symm] at this
            · have hji : M j i = M i j := (congr_arg (fun X => X j i) hMsym.eq).symm
              have hval : (Pi.single i (1 : ℤ) + Pi.single j 1) ⬝ᵥ M *ᵥ (Pi.single i 1 + Pi.single j 1) =
                  2 * M i j := by
                simp only [dotProduct_add, add_dotProduct, mulVec_add, mulVec_single]
                simp [hdiag i, hdiag j, hji]
                ring
              rw [hval]
              exact mul_ne_zero (by norm_num) hij
        obtain ⟨v, hv, hqM⟩ := hex
        let qC : ℤ := v ⬝ᵥ C *ᵥ v
        let qM : ℤ := v ⬝ᵥ M *ᵥ v
        let k : ℤ := if 0 < qM then -((qC.natAbs : ℤ) + 1) else (qC.natAbs : ℤ) + 1
        have hk : k ≠ 0 := by
          dsimp [k]
          split_ifs <;> omega
        have hneg_quad : qC + k * qM < 0 := by
          have hbd : -(qC.natAbs : ℤ) ≤ qC ∧ qC ≤ (qC.natAbs : ℤ) := by
            rcases Int.natAbs_eq qC with h | h <;> omega
          dsimp [k]
          split_ifs with hq
          · have h1 : (1 : ℤ) ≤ qM := by omega
            nlinarith
          · have h1 : qM ≤ -1 := by omega
            nlinarith
        obtain ⟨hsym, hneg1, hneg2, hdet⟩ := hA_props k hk
        refine ⟨k • A0, hsym, hneg1, hneg2, hdet, ?_⟩
        intro ⟨hpd, _⟩
        let vr : Fin m → ℝ := fun i => (v i : ℝ)
        have hvr : vr ≠ 0 := by
          intro h
          apply hv
          ext i
          have hi : (v i : ℝ) = ((0 : ℤ) : ℝ) := by
            simpa [vr] using congr_fun h i
          exact Int.cast_injective hi
        have hpos : 0 < star vr ⬝ᵥ (realify (C + L (k • A0))) *ᵥ vr :=
          hpd.dotProduct_mulVec_pos hvr
        have hCeq : C + L (k • A0) = C + k • M := by
          rw [L.map_smul, show L A0 = M from rfl]
        rw [hCeq] at hpos
        have hval : star vr ⬝ᵥ (realify (C + k • M)) *ᵥ vr = ((qC + k * qM : ℤ) : ℝ) := by
          have h1 : realify (C + k • M) = realify C + (k : ℝ) • realify M := by
            ext i j
            simp only [realify, map_apply, Int.coe_castRingHom, Matrix.add_apply, Matrix.smul_apply,
              smul_eq_mul, Int.cast_add, Int.cast_mul]
          rw [star_trivial, h1, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
            vec_cast_dot_mulVec, vec_cast_dot_mulVec]
          push_cast
          rfl
        rw [hval] at hpos
        have hlt : ((qC + k * qM : ℤ) : ℝ) < 0 := Int.cast_lt_zero.mpr hneg_quad
        linarith
      · by_cases h1 : works ((1 : ℤ) • A0) (C + L ((1 : ℤ) • A0))
        · obtain ⟨hsym, hneg1, hneg2, hdet⟩ := hA_props 2 (by norm_num)
          refine ⟨(2 : ℤ) • A0, hsym, hneg1, hneg2, hdet, ?_⟩
          intro h2
          have hL1 : L ((1 : ℤ) • A0) = (1 : ℤ) • M := L.map_smul (1 : ℤ) A0
          have hL2 : L ((2 : ℤ) • A0) = (2 : ℤ) • M := L.map_smul (2 : ℤ) A0
          have hs1 : (C + (1 : ℤ) • M).IsSymm := by
            rw [← realify_isHermitian_iff]
            have := h1.1.1
            rwa [hL1] at this
          have hs2 : (C + (2 : ℤ) • M).IsSymm := by
            rw [← realify_isHermitian_iff]
            have := h2.1.1
            rwa [hL2] at this
          apply hMsym
          ext i j
          have h1ij := congr_arg (fun X => X i j) hs1.eq
          have h2ij := congr_arg (fun X => X i j) hs2.eq
          simp only [transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1ij h2ij
          change M j i = M i j
          linarith
        · obtain ⟨hsym, hneg1, hneg2, hdet⟩ := hA_props 1 (by norm_num)
          exact ⟨(1 : ℤ) • A0, hsym, hneg1, hneg2, hdet, h1⟩
  · intro n A hdet
    have hdet_sq : (Aᵀ * A).det = A.det ^ 2 := by
      simp [det_mul, det_transpose, sq]
    refine ⟨⟨?_, ?_⟩, hdet_sq⟩
    · have hreal : realify (Aᵀ * A) = (realify A)ᵀ * realify A := by
        ext i j
        simp [realify, mul_apply]
      rw [hreal]
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · ext i j
        simp [conjTranspose_apply, mul_apply, mul_comm]
      · intro x hx
        have hRx : realify A *ᵥ x ≠ 0 := by
          intro hzero
          have hrdet : (realify A).det ≠ 0 := by
            rw [realify_det]
            exact Int.cast_ne_zero.mpr hdet
          exact hx (Matrix.eq_zero_of_mulVec_eq_zero hrdet hzero)
        have hdot : star x ⬝ᵥ ((realify A)ᵀ * realify A) *ᵥ x =
            (realify A *ᵥ x) ⬝ᵥ (realify A *ᵥ x) := by
          rw [star_trivial, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
        rw [hdot]
        have hge : 0 ≤ (realify A *ᵥ x) ⬝ᵥ (realify A *ᵥ x) :=
          Finset.sum_nonneg fun i _ => mul_self_nonneg _
        have hne : (realify A *ᵥ x) ⬝ᵥ (realify A *ᵥ x) ≠ 0 :=
          mt dotProduct_self_eq_zero.mp hRx
        exact lt_of_le_of_ne hge hne.symm
    · rw [hdet_sq]
      exact dvd_pow_self A.det (by norm_num)

end
