import OMAStatements.S_mo_304281

open OMA.S_mo_304281 Matrix Polynomial
open scoped Matrix

namespace RowOrthogonalStability

noncomputable def sqNorm {m : ℕ} (v : Fin m → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma sqNorm_nonneg {m : ℕ} (v : Fin m → ℂ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma sqNorm_pos_of_ne_zero {m : ℕ} {v : Fin m → ℂ} (hv : v ≠ 0) : 0 < sqNorm v := by
  refine lt_of_le_of_ne (sqNorm_nonneg v) fun h0 ↦ hv ?_
  ext i
  have hi : ‖v i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg ‖v j‖).mp h0.symm i (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

lemma sqNorm_eq_zero_iff {m : ℕ} (v : Fin m → ℂ) : sqNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hne
    linarith [sqNorm_pos_of_ne_zero hne]
  · rintro rfl
    unfold sqNorm
    simp

lemma sqNorm_smul {m : ℕ} (z : ℂ) (v : Fin m → ℂ) : sqNorm (z • v) = ‖z‖ ^ 2 * sqNorm v := by
  unfold sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

lemma ofReal_sqNorm {m : ℕ} (v : Fin m → ℂ) :
    ((sqNorm v : ℝ) : ℂ) = ∑ i, star (v i) * v i := by
  unfold sqNorm
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.star_def, Complex.conj_mul']

lemma star_mul_mulVec_real {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℝ) (v : Fin m → ℂ) :
    ((sqNorm ((M.map Complex.ofReal)ᵀ *ᵥ v) : ℝ) : ℂ) =
      ∑ i : Fin m, ∑ l : Fin m, star (v i) * ((M * Mᵀ) i l : ℂ) * v l := by
  rw [ofReal_sqNorm]
  have hterm : ∀ j : Fin k,
      star (((M.map Complex.ofReal)ᵀ *ᵥ v) j) * (((M.map Complex.ofReal)ᵀ *ᵥ v) j) =
        ∑ i : Fin m, ∑ l : Fin m, star (v i) * ((M i j : ℂ) * (M l j : ℂ)) * v l := fun j ↦ by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

lemma sqNorm_add_eq {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hAB : A * Aᵀ + B * Bᵀ = 1) (v : Fin n → ℂ) :
    sqNorm ((A.map Complex.ofReal)ᵀ *ᵥ v) + sqNorm ((B.map Complex.ofReal)ᵀ *ᵥ v) = sqNorm v := by
  apply Complex.ofReal_injective
  push_cast
  rw [star_mul_mulVec_real A v, star_mul_mulVec_real B v, ofReal_sqNorm]
  rw [← Finset.sum_add_distrib]
  have hinner : ∀ i : Fin n,
      (∑ l : Fin n, star (v i) * ((A * Aᵀ) i l : ℂ) * v l) +
        (∑ l : Fin n, star (v i) * ((B * Bᵀ) i l : ℂ) * v l) = star (v i) * v i := fun i ↦ by
    rw [← Finset.sum_add_distrib]
    have hsum : ∀ l : Fin n,
        star (v i) * ((A * Aᵀ) i l : ℂ) * v l + star (v i) * ((B * Bᵀ) i l : ℂ) * v l =
          star (v i) * (((A * Aᵀ + B * Bᵀ) i l : ℝ) : ℂ) * v l := fun l ↦ by
      simp only [Matrix.add_apply]; push_cast; ring
    simp_rw [hsum, hAB]
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hli
      simp [hli.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp_rw [hinner]

lemma eval_charpoly_eq_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpoly.eval z = (Matrix.scalar (Fin n) z - M).det := by
  unfold Matrix.charpoly
  have hdet := RingHom.map_det (Polynomial.evalRingHom z) (Matrix.charmatrix M)
  have hmat : (Polynomial.evalRingHom z).mapMatrix (Matrix.charmatrix M) =
      Matrix.scalar (Fin n) z - M := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, Polynomial.coe_evalRingHom]
    by_cases h : i = j <;> simp [h]
  rw [hmat] at hdet
  simpa [Polynomial.coe_evalRingHom] using hdet

lemma isRoot_charpoly_iff_exists_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpoly.IsRoot z ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ Mᵀ *ᵥ v = z • v := by
  rw [← Matrix.charpoly_transpose M, Polynomial.IsRoot.def, eval_charpoly_eq_det,
    Matrix.exists_mulVec_eq_zero_iff.symm]
  constructor
  · rintro ⟨v, hv, h0⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.scalar_apply] at h0
    ext i
    have hi := congr_fun h0 i
    simpa [Matrix.mulVec_diagonal] using hi.symm
  · rintro ⟨v, hv, heig⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, heig]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

lemma mulVec_pow_of_eigenvector {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    {v : Fin n → ℂ} (hv : M *ᵥ v = z • v) : ∀ m : ℕ, (M ^ m) *ᵥ v = z ^ m • v
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ', ← Matrix.mulVec_mulVec, mulVec_pow_of_eigenvector hv m,
      Matrix.mulVec_smul, hv, smul_smul, pow_succ', mul_comm]

lemma map_ofReal_mul {m p q : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) (N : Matrix (Fin p) (Fin q) ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

lemma map_ofReal_pow {n : ℕ} (M : Sq n) (m : ℕ) :
    (M ^ m).map Complex.ofReal = (M.map Complex.ofReal) ^ m := by
  induction m with
  | zero =>
    ext i j
    by_cases h : i = j <;> simp [h]
  | succ m ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact map_ofReal_mul (M ^ m) M

lemma pow_n_eq_neg_sum_charpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M ^ n = - ∑ j : Fin n, M.charpoly.coeff j.val • M ^ j.val := by
  have hch := Matrix.aeval_self_charpoly M
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmon : M.charpoly.Monic := Matrix.charpoly_monic M
  have hlc : M.charpoly.coeff n = 1 := by
    simpa [Polynomial.leadingCoeff, hdeg] using hmon.leadingCoeff
  have hpoly : M.charpoly = X ^ n + ∑ j : Fin n, C (M.charpoly.coeff j.val) * X ^ j.val := by
    ext k
    simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    by_cases hk : k < n
    · have hk_ne : k ≠ n := Nat.ne_of_lt hk
      rw [if_neg hk_ne, zero_add, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hjk
        have hne : k ≠ j.val := fun h ↦ hjk (Fin.ext h.symm)
        simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · by_cases hkn : k = n
      · rw [hkn, if_pos rfl, Finset.sum_eq_zero]
        · rw [add_zero]; exact hlc
        · intro j _
          have hne : n ≠ j.val := Nat.ne_of_gt j.isLt
          simp [hne]
      · have hgt : n < k := by omega
        rw [if_neg hkn, zero_add, Finset.sum_eq_zero]
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        · intro j _
          have hne : k ≠ j.val := by omega
          simp [hne]
  rw [hpoly, map_add, map_pow, Polynomial.aeval_X, map_sum] at hch
  have hsum : (∑ j : Fin n, Polynomial.aeval M (C (M.charpoly.coeff j.val) * X ^ j.val)) =
      ∑ j : Fin n, M.charpoly.coeff j.val • M ^ j.val := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
  rw [hsum] at hch
  exact eq_neg_of_add_eq_zero_left hch

lemma spectral_le_one {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hAB : A * Aᵀ + B * Bᵀ = 1) (z : ℂ) (hz : (A.map Complex.ofReal).charpoly.IsRoot z) :
    ‖z‖ ≤ 1 := by
  obtain ⟨v, hv_ne, hv_eig⟩ := (isRoot_charpoly_iff_exists_eigenvector _ z).mp hz
  have hkey := sqNorm_add_eq A B hAB v
  rw [hv_eig, sqNorm_smul] at hkey
  have hv_pos : 0 < sqNorm v := sqNorm_pos_of_ne_zero hv_ne
  have hB_nn : 0 ≤ sqNorm ((B.map Complex.ofReal)ᵀ *ᵥ v) := sqNorm_nonneg _
  have hsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith
  nlinarith [norm_nonneg z]

lemma stable_of_rank_eq {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hAB : A * Aᵀ + B * Bᵀ = 1) (hrank : (tests A B).rank = n) : stable A := by
  intro z hz
  have hle : ‖z‖ ≤ 1 := spectral_le_one A B hAB z hz
  refine lt_of_le_of_ne hle fun h1 ↦ ?_
  obtain ⟨v, hv_ne, hv_eig⟩ := (isRoot_charpoly_iff_exists_eigenvector _ z).mp hz
  have hkey := sqNorm_add_eq A B hAB v
  rw [hv_eig, sqNorm_smul, h1, one_pow, one_mul] at hkey
  have hBv0 : (B.map Complex.ofReal)ᵀ *ᵥ v = 0 :=
    (sqNorm_eq_zero_iff _).mp (by linarith)
  have hall_C : ∀ m : ℕ, ((Bᵀ * Aᵀ ^ m).map Complex.ofReal) *ᵥ v = 0 := fun m ↦ by
    rw [map_ofReal_mul, map_ofReal_pow]
    have hAt : (Aᵀ).map Complex.ofReal = (A.map Complex.ofReal)ᵀ := by ext i j; rfl
    have hBt : (Bᵀ).map Complex.ofReal = (B.map Complex.ofReal)ᵀ := by ext i j; rfl
    rw [hAt, hBt, ← Matrix.mulVec_mulVec, mulVec_pow_of_eigenvector hv_eig m,
      Matrix.mulVec_smul, hBv0, smul_zero]
  let x : Fin n → ℝ := fun i ↦ (v i).re
  let y : Fin n → ℝ := fun i ↦ (v i).im
  have hxy_ne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hboth
    push Not at hboth
    apply hv_ne
    ext i
    exact Complex.ext (congr_fun hboth.1 i) (congr_fun hboth.2 i)
  have hker_re : (tests A B) *ᵥ x = 0 := by
    ext ⟨m, r⟩
    have h0 := congr_arg Complex.re (congr_fun (hall_C m.val) r)
    simpa [tests, Matrix.mulVec, dotProduct, x] using h0
  have hker_im : (tests A B) *ᵥ y = 0 := by
    ext ⟨m, r⟩
    have h0 := congr_arg Complex.im (congr_fun (hall_C m.val) r)
    simpa [tests, Matrix.mulVec, dotProduct, y] using h0
  obtain ⟨w, hw_ne, hw_ker⟩ : ∃ w : Fin n → ℝ, w ≠ 0 ∧ (tests A B) *ᵥ w = 0 := by
    rcases hxy_ne with hx | hy
    · exact ⟨x, hx, hker_re⟩
    · exact ⟨y, hy, hker_im⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (tests A B).mulVecLin
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hdim] at hrn
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker (tests A B).mulVecLin) := by
    have hne_bot : LinearMap.ker (tests A B).mulVecLin ≠ ⊥ := fun hbot ↦ by
      have hmem : w ∈ LinearMap.ker (tests A B).mulVecLin := hw_ker
      rw [hbot, Submodule.mem_bot] at hmem
      exact hw_ne hmem
    exact Nat.pos_of_ne_zero fun h0 ↦ hne_bot (Submodule.finrank_eq_zero.mp h0)
  have hr_eq : Module.finrank ℝ (LinearMap.range (tests A B).mulVecLin) = (tests A B).rank := rfl
  omega

lemma rank_eq_of_stable {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ)
    (hAB : A * Aᵀ + B * Bᵀ = 1) (hstab : stable A) : (tests A B).rank = n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (tests A B).mulVecLin
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hdim] at hrn
  have hr_eq : Module.finrank ℝ (LinearMap.range (tests A B).mulVecLin) = (tests A B).rank := rfl
  by_contra hne
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker (tests A B).mulVecLin) := by omega
  have hker_ne_bot : LinearMap.ker (tests A B).mulVecLin ≠ ⊥ := fun hbot ↦ by
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne_bot
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hw_ne (Subsingleton.elim w 0)
  let AC : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal
  let BC : Matrix (Fin n) (Fin k) ℂ := B.map Complex.ofReal
  let W : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {v | ∀ m : Fin n, (BCᵀ * ACᵀ ^ m.val) *ᵥ v = 0}
      add_mem' := fun ha hb m ↦ by rw [Matrix.mulVec_add, ha m, hb m, add_zero]
      zero_mem' := fun m ↦ by simp
      smul_mem' := fun c _ hv m ↦ by rw [Matrix.mulVec_smul, hv m, smul_zero] }
  have hW_ne_bot : W ≠ ⊥ := by
    intro hbot
    let wC : Fin n → ℂ := fun i ↦ (w i : ℂ)
    have hwC_mem : wC ∈ W := fun m ↦ by
      ext r
      have h0 : ((tests A B) *ᵥ w) (m, r) = 0 := congr_fun hw_mem (m, r)
      have hmat : BCᵀ * ACᵀ ^ m.val = (Bᵀ * Aᵀ ^ m.val).map Complex.ofReal := by
        rw [map_ofReal_mul, map_ofReal_pow]
        have hAt : (Aᵀ).map Complex.ofReal = ACᵀ := by ext i j; rfl
        have hBt : (Bᵀ).map Complex.ofReal = BCᵀ := by ext i j; rfl
        rw [hAt, hBt]
      rw [hmat]
      have hcast : (((Bᵀ * Aᵀ ^ m.val).map Complex.ofReal) *ᵥ wC) r =
          (((Bᵀ * Aᵀ ^ m.val) *ᵥ w) r : ℂ) := by
        simp [Matrix.mulVec, dotProduct, wC]
      rw [hcast]
      have htest : ((Bᵀ * Aᵀ ^ m.val) *ᵥ w) r = ((tests A B) *ᵥ w) (m, r) := rfl
      rw [htest, h0, Complex.ofReal_zero]
      rfl
    rw [hbot, Submodule.mem_bot] at hwC_mem
    apply hw_ne
    ext i
    exact Complex.ofReal_injective (congr_fun hwC_mem i)
  have hW_inv : ∀ v ∈ W, ACᵀ.mulVecLin v ∈ W := fun v hv m ↦ by
    change (BCᵀ * ACᵀ ^ m.val) *ᵥ (ACᵀ *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
    by_cases hlt : m.val + 1 < n
    · exact hv ⟨m.val + 1, hlt⟩
    · have heq : m.val + 1 = n := by omega
      rw [heq, pow_n_eq_neg_sum_charpoly ACᵀ, Matrix.mul_neg, Matrix.neg_mulVec,
        Matrix.mul_sum, Matrix.sum_mulVec]
      rw [Finset.sum_eq_zero]
      · simp
      · intro j _
        rw [Matrix.mul_smul, Matrix.smul_mulVec, hv j, smul_zero]
  let T : Module.End ℂ W := LinearMap.restrict ACᵀ.mulVecLin hW_inv
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW_ne_bot
  obtain ⟨z, hz_eig⟩ := Module.End.exists_eigenvalue T
  obtain ⟨⟨v, hvW⟩, hv_has⟩ := hz_eig.exists_hasEigenvector
  have hv_ne : v ≠ 0 := fun h0 ↦ hv_has.2 (Subtype.ext h0)
  have hv_eig : ACᵀ *ᵥ v = z • v := by
    have h := congr_arg Subtype.val (Module.End.mem_eigenspace_iff.mp hv_has.1)
    simpa only [T, LinearMap.restrict_apply, Matrix.mulVecLin_apply, Submodule.coe_smul_of_tower] using h
  have hroot : AC.charpoly.IsRoot z :=
    (isRoot_charpoly_iff_exists_eigenvector AC z).mpr ⟨v, hv_ne, hv_eig⟩
  have hBv0 : BCᵀ *ᵥ v = 0 := by
    have h0 := hvW ⟨0, hn_pos⟩
    simpa using h0
  have hkey := sqNorm_add_eq A B hAB v
  change sqNorm (ACᵀ *ᵥ v) + sqNorm (BCᵀ *ᵥ v) = sqNorm v at hkey
  rw [hv_eig, sqNorm_smul, hBv0, (sqNorm_eq_zero_iff 0).mpr rfl, add_zero] at hkey
  have hv_pos : 0 < sqNorm v := sqNorm_pos_of_ne_zero hv_ne
  have hsq1 : ‖z‖ ^ 2 = 1 := mul_right_cancel₀ hv_pos.ne' (by linarith)
  have hnorm1 : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
  have hlt1 : ‖z‖ < 1 := hstab z hroot
  linarith

end RowOrthogonalStability

theorem OMA.solution : type_of% @OMA.S_mo_304281.main := by
  intro n k A B hAB
  exact ⟨RowOrthogonalStability.spectral_le_one A B hAB,
    ⟨RowOrthogonalStability.rank_eq_of_stable A B hAB,
     RowOrthogonalStability.stable_of_rank_eq A B hAB⟩⟩
