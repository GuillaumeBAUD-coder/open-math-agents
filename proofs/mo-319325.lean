import OMAStatements.S_mo_319325

open Filter Topology
open scoped MatrixOrder

namespace OMA.Mo319325

private def A : Matrix (Fin 2) (Fin 2) ℝ := !![(-1 : ℝ), 1; 0, -1]

private noncomputable def s (k : ℕ) : ℝ := (1 : ℝ) / ((k : ℝ) + 1)

private noncomputable def t (k : ℕ) : ℝ :=
  if Even k then s k else (3 / 2 : ℝ) * s k

private noncomputable def S (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![s k, t k]

private noncomputable def P (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![s k ^ 2, t k ^ 2]

private noncomputable def X (k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * s k ^ 2, -(t k ^ 2); -(t k ^ 2), 2 * t k ^ 2]

private lemma s_pos (k : ℕ) : 0 < s k := by
  unfold s
  positivity

private lemma t_pos (k : ℕ) : 0 < t k := by
  unfold t
  split_ifs
  · exact s_pos k
  · have hs := s_pos k
    linarith

private lemma t_le (k : ℕ) : t k ≤ (3 / 2 : ℝ) * s k := by
  unfold t
  split_ifs
  · have hs := s_pos k
    linarith
  · exact le_rfl

private lemma A_hurwitz : OMA.S_mo_319325.hurwitz A := by
  intro z hz
  rw [spectrum.mem_iff] at hz
  have hdet : (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z - A.map Complex.ofReal).det = 0 := by
    by_contra hne
    exact hz ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
  have hcalc :
      (algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) z - A.map Complex.ofReal).det = (z + 1) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [A, Algebra.algebraMap_eq_smul_one]
    ring
  rw [hcalc, sq] at hdet
  have hz1 : z + 1 = 0 := mul_self_eq_zero.mp hdet
  have hz' : z = -1 := eq_neg_of_add_eq_zero_left hz1
  simp [hz']

private lemma P_posDef (k : ℕ) : (P k).PosDef := by
  rw [P, Matrix.posDef_diagonal_iff]
  intro i
  fin_cases i
  · exact pow_pos (s_pos k) 2
  · exact pow_pos (t_pos k) 2

private lemma X_posDef (k : ℕ) : (X k).PosDef := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [X]
  · intro x hx
    have hsum : (x.sum fun i xi => x.sum fun j xj => star xi * X k i j * xj) =
        (2 * s k ^ 2 - t k ^ 2 / 2) * (x 0) ^ 2 + 2 * t k ^ 2 * (x 1 - x 0 / 2) ^ 2 := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      simp only [Fin.sum_univ_two]
      rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
      simp [Fin.sum_univ_two, X]
      ring
    rw [hsum]
    have hs : 0 < s k := s_pos k
    have ht : 0 < t k := t_pos k
    have htle : t k ≤ (3 / 2 : ℝ) * s k := t_le k
    have htsq : t k ^ 2 ≤ (9 / 4 : ℝ) * s k ^ 2 := by nlinarith
    have hc1 : 0 < 2 * s k ^ 2 - t k ^ 2 / 2 := by nlinarith
    have hc2 : 0 < 2 * t k ^ 2 := by positivity
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have h1sq : 0 < (x 1) ^ 2 := sq_pos_of_ne_zero h1
      simp only [h0]
      nlinarith
    · have h0sq : 0 < (x 0) ^ 2 := sq_pos_of_ne_zero h0
      have hsq2 : 0 ≤ (x 1 - x 0 / 2) ^ 2 := sq_nonneg _
      nlinarith

private lemma lyapunov (k : ℕ) : A * P k + P k * A.transpose = -(X k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.neg_apply,
      Fin.sum_univ_two, A, P, X, Matrix.diagonal_apply] <;>
    simp <;> ring

private lemma S_nonneg (k : ℕ) : 0 ≤ S k := by
  rw [Matrix.nonneg_iff_posSemidef, S, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i
  · exact (s_pos k).le
  · exact (t_pos k).le

private lemma S_mul_S (k : ℕ) : S k * S k = P k := by
  rw [S, P, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [sq]

private lemma sqrt_P (k : ℕ) : CFC.sqrt (P k) = S k :=
  CFC.sqrt_unique (S_mul_S k) (S_nonneg k)

private lemma S_inv (k : ℕ) : (S k)⁻¹ = Matrix.diagonal ![(s k)⁻¹, (t k)⁻¹] := by
  apply Matrix.inv_eq_right_inv
  rw [S, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [(s_pos k).ne', (t_pos k).ne']

private lemma normalized_01 (k : ℕ) :
    OMA.S_mo_319325.normalized (P k) (X k) 0 1 = -(t k / s k) := by
  rw [OMA.S_mo_319325.normalized, sqrt_P, S_inv]
  simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  have ht : t k ≠ 0 := (t_pos k).ne'
  have hs : s k ≠ 0 := (s_pos k).ne'
  field_simp

private lemma tendsto_s : Tendsto s atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private lemma tendsto_s_sq : Tendsto (fun k => s k ^ 2) atTop (𝓝 0) := by
  simpa using tendsto_s.pow 2

private lemma tendsto_t_sq : Tendsto (fun k => t k ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun k => (9 / 4 : ℝ) * s k ^ 2)
    (fun k => sq_nonneg (t k)) (fun k => ?_) ?_
  · have hs := s_pos k
    have ht := t_pos k
    have htle := t_le k
    nlinarith
  · simpa using tendsto_s_sq.const_mul (9 / 4 : ℝ)

private lemma tendsto_P : Tendsto P atTop (𝓝 0) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [P] using tendsto_s_sq
  · simp [P]
  · simp [P]
  · simpa [P] using tendsto_t_sq

private lemma tendsto_X : Tendsto X atTop (𝓝 0) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [X] using tendsto_s_sq.const_mul (2 : ℝ)
  · simpa [X] using tendsto_t_sq.neg
  · simpa [X] using tendsto_t_sq.neg
  · simpa [X] using tendsto_t_sq.const_mul (2 : ℝ)

end OMA.Mo319325

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_319325.main) := by
  intro hmain
  obtain ⟨L, hL⟩ :=
    hmain 2 (by norm_num) OMA.Mo319325.A OMA.Mo319325.A_hurwitz
      OMA.Mo319325.X OMA.Mo319325.P
      OMA.Mo319325.X_posDef OMA.Mo319325.P_posDef OMA.Mo319325.lyapunov
      0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero
      Matrix.det_zero
      OMA.Mo319325.tendsto_X OMA.Mo319325.tendsto_P
  have h01 : Tendsto (fun k => OMA.S_mo_319325.normalized (OMA.Mo319325.P k) (OMA.Mo319325.X k) 0 1)
      atTop (𝓝 (L 0 1)) :=
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hL 0) 1)
  have heven_tendsto : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    Filter.tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (by norm_num)) tendsto_id
  have hodd_tendsto : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun m => show m ≤ 2 * m + 1 by omega) tendsto_id
  have heven_val :
      (fun m : ℕ => OMA.S_mo_319325.normalized (OMA.Mo319325.P (2 * m)) (OMA.Mo319325.X (2 * m)) 0 1) =
        fun _ => (-1 : ℝ) := by
    funext m
    rw [OMA.Mo319325.normalized_01]
    have hsm : OMA.Mo319325.s (2 * m) ≠ 0 := (OMA.Mo319325.s_pos (2 * m)).ne'
    simp [OMA.Mo319325.t, hsm]
  have hodd_val :
      (fun m : ℕ => OMA.S_mo_319325.normalized (OMA.Mo319325.P (2 * m + 1)) (OMA.Mo319325.X (2 * m + 1)) 0 1) =
        fun _ => (-(3 / 2 : ℝ)) := by
    funext m
    rw [OMA.Mo319325.normalized_01]
    have hsm : OMA.Mo319325.s (2 * m + 1) ≠ 0 := (OMA.Mo319325.s_pos (2 * m + 1)).ne'
    have hnot : ¬ Even (2 * m + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨m, rfl⟩
    simp [OMA.Mo319325.t, hnot, hsm]
  have hL1 : L 0 1 = (-1 : ℝ) := by
    have h1 := h01.comp heven_tendsto
    have h2 : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1 : ℝ)) := tendsto_const_nhds
    change Tendsto (fun m => OMA.S_mo_319325.normalized (OMA.Mo319325.P (2 * m)) (OMA.Mo319325.X (2 * m)) 0 1) atTop (𝓝 (L 0 1)) at h1
    rw [heven_val] at h1
    exact tendsto_nhds_unique h1 h2
  have hL2 : L 0 1 = (-(3 / 2 : ℝ)) := by
    have h1 := h01.comp hodd_tendsto
    have h2 : Tendsto (fun _ : ℕ => (-(3 / 2 : ℝ))) atTop (𝓝 (-(3 / 2 : ℝ))) := tendsto_const_nhds
    change Tendsto (fun m => OMA.S_mo_319325.normalized (OMA.Mo319325.P (2 * m + 1)) (OMA.Mo319325.X (2 * m + 1)) 0 1) atTop (𝓝 (L 0 1)) at h1
    rw [hodd_val] at h1
    exact tendsto_nhds_unique h1 h2
  linarith
