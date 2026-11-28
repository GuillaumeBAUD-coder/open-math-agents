import OMAStatements.S_mo_428655
import Mathlib

namespace OMA.P428655
open Matrix OMA.S_mo_428655

lemma realify_det {m : ℕ} (B : Mat m) : (realify B).det = (B.det : ℝ) := by
  unfold realify
  exact (RingHom.map_det (Int.castRingHom ℝ) B).symm

lemma realify_add {m : ℕ} (B C : Mat m) : realify (B + C) = realify B + realify C := by
  unfold realify; ext i j; simp

lemma realify_smul {m : ℕ} (k : ℤ) (B : Mat m) : realify (k • B) = (k : ℝ) • realify B := by
  unfold realify; ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul]
  simp

lemma part1 : ∃ A : Mat 2, A.IsSymm ∧ hasNegative A ∧ A.det=0 ∧
    ∀ (m : ℕ) (B : Mat m),¬ works A B := by
  refine ⟨!![-1, 0; 0, 0], ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · refine ⟨-1, by norm_num, ![1, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · ext i; fin_cases i <;> simp [realify, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]
  · intro m B ⟨hpd, hdvd⟩
    have h0 : B.det = 0 := by
      have : (!![-1, 0; 0, 0] : Mat 2).det = 0 := by simp [Matrix.det_fin_two]
      rw [this] at hdvd
      exact zero_dvd_iff.mp hdvd
    have := hpd.det_pos
    rw [realify_det, h0] at this
    simp at this

/-- The symmetric test matrix. -/
def S (k : ℤ) : Mat 2 := !![0, k; k, 0]

lemma S_eq (k : ℤ) : S k = k • S 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S]

lemma S_det (k : ℤ) : (S k).det = -k ^ 2 := by
  simp [S, Matrix.det_fin_two]; ring

lemma S_neg (k : ℤ) (hk : k ≠ 0) : hasNegative (S k) := by
  rcases lt_or_gt_of_ne hk with h | h
  · refine ⟨(k : ℝ), by exact_mod_cast h, ![1, 1], ?_, ?_⟩
    · intro h'
      have := congrFun h' 0
      simp at this
    · ext i; fin_cases i <;> simp [S, realify, mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨-(k : ℝ), by have : (0:ℝ) < k := by exact_mod_cast h
                         linarith, ![1, -1], ?_, ?_⟩
    · intro h'
      have := congrFun h' 0
      simp at this
    · ext i; fin_cases i <;> simp [S, realify, mulVec, dotProduct, Fin.sum_univ_two]

lemma S_negneg (k : ℤ) (hk : k ≠ 0) : hasNegative (-S k) := by
  have : -S k = S (-k) := by ext i j; fin_cases i <;> fin_cases j <;> simp [S]
  rw [this]; exact S_neg (-k) (neg_ne_zero.mpr hk)

lemma S_symm (k : ℤ) : (S k).IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma det_mod {m : ℕ} (C M : Mat m) (k : ℤ) : k ∣ (C + k • M).det - C.det := by
  have hk0 : ((k : ℤ) : ZMod k.natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; simp
  have key : ((Int.castRingHom (ZMod k.natAbs)).mapMatrix (C + k • M)) =
      (Int.castRingHom (ZMod k.natAbs)).mapMatrix C := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, eq_intCast, hk0, zero_mul, add_zero]
  have h1 := RingHom.map_det (Int.castRingHom (ZMod k.natAbs)) (C + k • M)
  have h2 := RingHom.map_det (Int.castRingHom (ZMod k.natAbs)) C
  rw [key, ← h2] at h1
  have h3 : (Int.castRingHom (ZMod k.natAbs)) ((C + k • M).det - C.det) = 0 := by
    rw [map_sub, h1, sub_self]
  rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  exact Int.natAbs_dvd.mp h3

lemma part2 : ∀ (m : ℕ) (C : Mat m) (L : Mat 2 →ₗ[ℤ] Mat m),
      ∃ A : Mat 2, A.IsSymm ∧ hasNegative A ∧ hasNegative (-A) ∧ A.det≠0 ∧
        ¬ works A (C+L A) := by
  intro m C L
  by_contra hcon
  push Not at hcon
  set M := L (S 1) with hM
  have hw : ∀ k : ℤ, k ≠ 0 → works (S k) (C + k • M) := by
    intro k hk
    have := hcon (S k) (S_symm k) (S_neg k hk) (S_negneg k hk)
      (by rw [S_det]; exact neg_ne_zero.mpr (pow_ne_zero 2 hk))
    rwa [S_eq k, map_zsmul, ← S_eq k] at this
  -- det C = 0
  have hdet : C.det = 0 := by
    by_contra hne
    have hk : 2 * C.det ≠ 0 := mul_ne_zero two_ne_zero hne
    obtain ⟨_, hdvd⟩ := hw (2 * C.det) hk
    rw [S_det] at hdvd
    have h1 : 2 * C.det ∣ (C + (2 * C.det) • M).det :=
      dvd_trans (⟨-(2 * C.det), by ring⟩ : 2 * C.det ∣ -(2 * C.det) ^ 2) hdvd
    have h2 := det_mod C M (2 * C.det)
    have h3 : 2 * C.det ∣ C.det := by
      have := dvd_sub h1 h2
      simpa using this
    have h4 := Int.natAbs_le_of_dvd_ne_zero h3 hne
    rw [Int.natAbs_mul] at h4
    have : 0 < C.det.natAbs := Int.natAbs_pos.mpr hne
    simp at h4
    omega
  have hdetR : (realify C).det = 0 := by rw [realify_det, hdet]; simp
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetR
  have p1 := ((hw 1 one_ne_zero).1).dotProduct_mulVec_pos hv0
  have p2 := ((hw (-1) (by norm_num)).1).dotProduct_mulVec_pos hv0
  rw [realify_add, realify_smul, add_mulVec, hv] at p1 p2
  simp only [smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_zero] at p1 p2
  push_cast at p1 p2
  simp at p1 p2
  linarith

lemma part3 : ∀ (n : ℕ) (A : Mat n), A.det≠0 → works A (Aᵀ*A) ∧ (Aᵀ*A).det=A.det^2 := by
  intro n A hA
  have hd : (Aᵀ*A).det = A.det^2 := by rw [det_mul, det_transpose]; ring
  refine ⟨⟨?_, ?_⟩, hd⟩
  · have hr : realify (Aᵀ * A) = (realify A)ᴴ * realify A := by
      unfold realify
      rw [Matrix.map_mul, conjTranspose_eq_transpose_of_trivial, transpose_map]
    rw [hr]
    apply PosDef.conjTranspose_mul_self
    have hdetR : (realify A).det ≠ 0 := by rw [realify_det]; exact_mod_cast hA
    intro x y hxy
    have hu : IsUnit (realify A) := (isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdetR)
    have := congrArg (fun z => (realify A)⁻¹ *ᵥ z) hxy
    simp only [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hu), one_mulVec] at this
    exact this
  · rw [hd]; exact ⟨A.det, by ring⟩

end OMA.P428655

theorem OMA.solution : type_of% @OMA.S_mo_428655.main :=
  ⟨OMA.P428655.part1, OMA.P428655.part2, OMA.P428655.part3⟩
