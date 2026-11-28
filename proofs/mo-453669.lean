import OMAStatements.S_mo_453669

open OMA.S_mo_453669 Matrix

namespace UnitaryCorrelationObstruction

noncomputable def vecs : Fin 4 → Fin 2 → ℂ :=
  ![![1, 0], ![0, 1], ![3 / 5, 4 / 5], ![3 / 5, 4 * Complex.I / 5]]

lemma vecs_unit (i : Fin 4) : star (vecs i) ⬝ᵥ vecs i = 1 := by
  fin_cases i
  · simp [vecs, dotProduct, Fin.sum_univ_two]
  · simp [vecs, dotProduct, Fin.sum_univ_two]
  · simp [vecs, dotProduct, Fin.sum_univ_two, map_div₀, map_ofNat]
    norm_num
  · simp [vecs, dotProduct, Fin.sum_univ_two, map_div₀, map_mul, map_ofNat]
    linear_combination -(16 / 25 : ℂ) * Complex.I_sq

lemma eq_zero_of_trace_conjTranspose_mul_self {N : ℕ} (A : Mat N)
    (h : (Aᴴ * A).trace = 0) : A = 0 := by
  have hsum : (∑ k : Fin N, ∑ l : Fin N, Complex.normSq (A l k)) = 0 := by
    have hre := congr_arg Complex.re h
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.zero_re, Complex.re_sum] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    simp [Complex.normSq_apply]
  have hall : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      ∑ l : Fin N, Complex.normSq (A l k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
      Finset.sum_nonneg fun l _ ↦ Complex.normSq_nonneg _).mp hsum
  ext l k
  have hk := hall k (Finset.mem_univ k)
  have hlk := (Finset.sum_eq_zero_iff_of_nonneg fun l' _ ↦
    Complex.normSq_nonneg _).mp hk l (Finset.mem_univ l)
  exact Complex.normSq_eq_zero.mp hlk

lemma trace_linear_relation {N : ℕ} {U : Fin 4 → Matrix.unitaryGroup (Fin N) ℂ}
    (hU : ∀ i j, (((U i : Mat N)ᴴ * (U j : Mat N)).trace / (N : ℂ)) =
      star (vecs i) ⬝ᵥ vecs j)
    (hN : 0 < N) {α β : ℂ} {r : Fin 4}
    (hvec : vecs r = α • vecs 0 + β • vecs 1) :
    (U r : Mat N) = α • (U 0 : Mat N) + β • (U 1 : Mat N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have htr : ∀ i j, ((U i : Mat N)ᴴ * (U j : Mat N)).trace =
      (N : ℂ) * (star (vecs i) ⬝ᵥ vecs j) := fun i j ↦ by
    have h := hU i j
    rw [div_eq_iff hN0] at h
    rw [h, mul_comm]
  let A : Mat N := α • (U 0 : Mat N) + β • (U 1 : Mat N) - (U r : Mat N)
  have htrA : (Aᴴ * A).trace = 0 := by
    have hexp :
        Aᴴ * A =
          (star α * α) • ((U 0 : Mat N)ᴴ * (U 0 : Mat N)) +
          (star α * β) • ((U 0 : Mat N)ᴴ * (U 1 : Mat N)) -
          (star α) • ((U 0 : Mat N)ᴴ * (U r : Mat N)) +
          (star β * α) • ((U 1 : Mat N)ᴴ * (U 0 : Mat N)) +
          (star β * β) • ((U 1 : Mat N)ᴴ * (U 1 : Mat N)) -
          (star β) • ((U 1 : Mat N)ᴴ * (U r : Mat N)) -
          α • ((U r : Mat N)ᴴ * (U 0 : Mat N)) -
          β • ((U r : Mat N)ᴴ * (U 1 : Mat N)) +
          ((U r : Mat N)ᴴ * (U r : Mat N)) := by
      dsimp [A]
      simp only [conjTranspose_sub, conjTranspose_add, conjTranspose_smul,
        Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.star_def]
      ring
    rw [hexp]
    simp only [trace_add, trace_sub, trace_smul, smul_eq_mul, htr]
    have h00 : star (vecs 0) ⬝ᵥ vecs 0 = 1 := vecs_unit 0
    have h11 : star (vecs 1) ⬝ᵥ vecs 1 = 1 := vecs_unit 1
    have hrr : star (vecs r) ⬝ᵥ vecs r = 1 := vecs_unit r
    have h01 : star (vecs 0) ⬝ᵥ vecs 1 = 0 := by simp [vecs, dotProduct, Fin.sum_univ_two]
    have h10 : star (vecs 1) ⬝ᵥ vecs 0 = 0 := by simp [vecs, dotProduct, Fin.sum_univ_two]
    have h0r : star (vecs 0) ⬝ᵥ vecs r = α := by
      rw [hvec, dotProduct_add, dotProduct_smul, dotProduct_smul, h00, h01]; simp
    have h1r : star (vecs 1) ⬝ᵥ vecs r = β := by
      rw [hvec, dotProduct_add, dotProduct_smul, dotProduct_smul, h10, h11]; simp
    have hr0 : star (vecs r) ⬝ᵥ vecs 0 = star α := by
      rw [hvec, star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct,
        h00, h10]; simp
    have hr1 : star (vecs r) ⬝ᵥ vecs 1 = star β := by
      rw [hvec, star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct,
        h01, h11]; simp
    have hnorm : star α * α + star β * β = 1 := by
      have h := hrr
      rw [hvec, star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct,
        dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, h00, h01, h10, h11] at h
      simpa [smul_eq_mul] using h
    rw [h00, h01, h0r, h10, h11, h1r, hr0, hr1, hrr]
    calc
      star α * α * ((N : ℂ) * 1) + star α * β * ((N : ℂ) * 0) - star α * ((N : ℂ) * α) +
          star β * α * ((N : ℂ) * 0) + star β * β * ((N : ℂ) * 1) - star β * ((N : ℂ) * β) -
          α * ((N : ℂ) * star α) - β * ((N : ℂ) * star β) + (N : ℂ) * 1 =
          (N : ℂ) * (1 - (star α * α + star β * β)) := by ring
      _ = 0 := by rw [hnorm]; ring
  have hA0 : A = 0 := eq_zero_of_trace_conjTranspose_mul_self A htrA
  exact (sub_eq_zero.mp hA0).symm

end UnitaryCorrelationObstruction

theorem OMA.solution : type_of% @OMA.S_mo_453669.main := by
  open UnitaryCorrelationObstruction in
  refine ⟨vecs, vecs_unit, fun N hN ⟨U, hU⟩ ↦ ?_⟩
  have hU2 : (U 2 : Mat N) = (3 / 5 : ℂ) • (U 0 : Mat N) + (4 / 5 : ℂ) • (U 1 : Mat N) :=
    trace_linear_relation hU hN (by ext i; fin_cases i <;> simp [vecs])
  have hU3 : (U 3 : Mat N) = (3 / 5 : ℂ) • (U 0 : Mat N) + (4 * Complex.I / 5 : ℂ) • (U 1 : Mat N) :=
    trace_linear_relation hU hN (by ext i; fin_cases i <;> simp [vecs])
  let W : Mat N := (U 0 : Mat N)ᴴ * (U 1 : Mat N)
  have h00 : (U 0 : Mat N)ᴴ * (U 0 : Mat N) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U 0).property
  have h11 : (U 1 : Mat N)ᴴ * (U 1 : Mat N) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U 1).property
  have h22 : (U 2 : Mat N)ᴴ * (U 2 : Mat N) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U 2).property
  have h33 : (U 3 : Mat N)ᴴ * (U 3 : Mat N) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U 3).property
  have hWstar : (U 1 : Mat N)ᴴ * (U 0 : Mat N) = Wᴴ := by
    dsimp [W]; simp [conjTranspose_mul]
  have hsumW : W + Wᴴ = 0 := by
    have h := h22
    rw [hU2] at h
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h00, h11, hWstar] at h
    have hst3 : star (3 / 5 : ℂ) = 3 / 5 := by simp
    have hst4 : star (4 / 5 : ℂ) = 4 / 5 := by simp
    rw [hst3, hst4] at h
    ext i j
    have hij := congr_fun (congr_fun h i) j
    change ((3 / 5 : ℂ) * (3 / 5) * (1 : Mat N) i j + (3 / 5) * (4 / 5) * Wᴴ i j) +
      ((4 / 5) * (3 / 5) * W i j + (4 / 5) * (4 / 5) * (1 : Mat N) i j) = (1 : Mat N) i j at hij
    simp only [Matrix.add_apply, Matrix.zero_apply]
    linear_combination (25 / 12 : ℂ) * hij
  have hdiffW : W - Wᴴ = 0 := by
    have h := h33
    rw [hU3] at h
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h00, h11, hWstar] at h
    have hst3 : star (3 / 5 : ℂ) = 3 / 5 := by simp
    have hst4I : star (4 * Complex.I / 5 : ℂ) = -(4 * Complex.I / 5) := by
      simp; ring
    rw [hst3, hst4I] at h
    ext i j
    have hij := congr_fun (congr_fun h i) j
    change ((3 / 5 : ℂ) * (3 / 5) * (1 : Mat N) i j + (3 / 5) * (-(4 * Complex.I / 5)) * Wᴴ i j) +
      ((4 * Complex.I / 5) * (3 / 5) * W i j + (4 * Complex.I / 5) * (-(4 * Complex.I / 5)) * (1 : Mat N) i j) =
      (1 : Mat N) i j at hij
    have h4 : (4 * Complex.I / 5 : ℂ) * -(4 * Complex.I / 5) = 16 / 25 := by
      linear_combination -(16 / 25 : ℂ) * Complex.I_sq
    rw [h4] at hij
    simp only [Matrix.sub_apply, Matrix.zero_apply]
    linear_combination (-25 * Complex.I / 12 : ℂ) * hij + (W i j - Wᴴ i j) * Complex.I_sq
  have hW0 : W = 0 := by
    ext i j
    have h1 := congr_fun (congr_fun hsumW i) j
    have h2 := congr_fun (congr_fun hdiffW i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply] at h1 h2 ⊢
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  have hWW : Wᴴ * W = 1 := by
    have h00' : (U 0 : Mat N) * (U 0 : Mat N)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (U 0).property
    calc
      Wᴴ * W = (U 1 : Mat N)ᴴ * ((U 0 : Mat N) * (U 0 : Mat N)ᴴ) * (U 1 : Mat N) := by
        dsimp [W]; simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h00', Matrix.mul_one, h11]
  rw [hW0, Matrix.mul_zero] at hWW
  have h01 := congr_fun (congr_fun hWW ⟨0, hN⟩) ⟨0, hN⟩
  simp at h01
