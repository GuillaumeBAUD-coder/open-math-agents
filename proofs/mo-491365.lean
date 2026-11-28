import OMAStatements.S_mo_491365

-- Credit: @MMexicann
-- Bounds for the extreme eigenvalues of Gram matrices under separate linear changes.

namespace OMA.Mo491365
open OMA.S_mo_491365

private theorem largest_bounds {n m : ℕ} (x : Fin (m + 1) → E n) :
    largest x ≤ ∑ i, ‖x i‖ ^ 2 ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ((m + 1 : ℕ) : ℝ) * largest x := by
  let e := (Matrix.isHermitian_gram ℝ x).eigenvalues
  have h_nonneg (i : Fin (m + 1)) : 0 ≤ e i :=
    (Matrix.posSemidef_gram ℝ x).eigenvalues_nonneg i
  have h_trace : (∑ i, e i) = ∑ i, ‖x i‖ ^ 2 := by
    calc
      (∑ i, e i) = (Matrix.gram ℝ x).trace := by
        simpa [e] using (Matrix.isHermitian_gram ℝ x).trace_eq_sum_eigenvalues.symm
      _ = ∑ i, ‖x i‖ ^ 2 := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.gram_apply, real_inner_self_eq_norm_sq]
  rw [← h_trace]
  constructor
  · apply Finset.sup'_le
    intro i hi
    exact Finset.single_le_sum (fun j _ => h_nonneg j) hi
  · calc
      (∑ i, e i) ≤ ∑ _i : Fin (m + 1), largest x :=
        Finset.sum_le_sum fun i hi => Finset.le_sup' e hi
      _ = ((m + 1 : ℕ) : ℝ) * largest x := by
        simp [nsmul_eq_mul]

private theorem largest_map_le {n m : ℕ} (T : Fin (m + 1) → E n ≃L[ℝ] E n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin (m + 1) → E n,
      largest (fun i => T i (x i)) ≤ C * largest x := by
  let a (i : Fin (m + 1)) := ‖(T i).toContinuousLinearMap‖
  let D : ℝ := (∑ i, a i ^ 2) + 1
  have h_D : 0 < D := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => sq_nonneg _) zero_lt_one
  have h_a_le_D (i : Fin (m + 1)) : a i ^ 2 ≤ D := by
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le_one)
  refine ⟨D * ((m + 1 : ℕ) : ℝ), mul_pos h_D (Nat.cast_pos.mpr (Nat.succ_pos m)), ?_⟩
  intro x
  calc
    largest (fun i => T i (x i)) ≤ ∑ i, ‖T i (x i)‖ ^ 2 := (largest_bounds _).1
    _ ≤ ∑ i, D * ‖x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h_norm : ‖T i (x i)‖ ≤ a i * ‖x i‖ := (T i).toContinuousLinearMap.le_opNorm _
      calc
        ‖T i (x i)‖ ^ 2 ≤ (a i * ‖x i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h_norm _
        _ = a i ^ 2 * ‖x i‖ ^ 2 := mul_pow _ _ _
        _ ≤ D * ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right (h_a_le_D i) (sq_nonneg _)
    _ = D * ∑ i, ‖x i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (D * ((m + 1 : ℕ) : ℝ)) * largest x := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (largest_bounds x).2 h_D.le

theorem largest_comparison (n m : ℕ) (T : Fin (m + 1) → E n ≃L[ℝ] E n) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : Fin (m + 1) → E n, c * largest (fun i => T i (x i)) ≤ largest x ∧
        largest x ≤ C * largest (fun i => T i (x i)) := by
  obtain ⟨D, h_D, h_forward⟩ := largest_map_le T
  obtain ⟨C, h_C, h_backward⟩ := largest_map_le (fun i => (T i).symm)
  refine ⟨D⁻¹, inv_pos.mpr h_D, C, h_C, fun x => ⟨?_, ?_⟩⟩
  · rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ h_D, mul_comm]
    exact h_forward x
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      h_backward (fun i => T i (x i))

end OMA.Mo491365

namespace OMA.Mo491365

open OMA.S_mo_491365

theorem gram_smallest_bounds (x : Fin 2 → E 2) :
    0 ≤ smallest x ∧
    (Matrix.gram ℝ x).det ≤ (Matrix.gram ℝ x).trace * smallest x ∧
    (Matrix.gram ℝ x).trace * smallest x ≤ 2 * (Matrix.gram ℝ x).det := by
  let h := Matrix.isHermitian_gram ℝ x
  let a := h.eigenvalues 0
  let b := h.eigenvalues 1
  have ha : 0 ≤ a := (Matrix.posSemidef_gram ℝ x).eigenvalues_nonneg 0
  have hb : 0 ≤ b := (Matrix.posSemidef_gram ℝ x).eigenvalues_nonneg 1
  have ht : (Matrix.gram ℝ x).trace = a + b := by
    simpa only [Fin.sum_univ_two, RCLike.ofReal_real_eq_id, id_eq] using
      h.trace_eq_sum_eigenvalues
  have hd : (Matrix.gram ℝ x).det = a * b := by
    simpa only [Fin.prod_univ_two, RCLike.ofReal_real_eq_id, id_eq] using
      h.det_eq_prod_eigenvalues
  have hs : smallest x = min a b := by
    unfold smallest
    apply le_antisymm
    · exact le_min (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 2)))
        (Finset.inf'_le _ (Finset.mem_univ (1 : Fin 2)))
    · apply Finset.le_inf'
      intro i _
      fin_cases i
      · exact min_le_left a b
      · exact min_le_right a b
  rw [ht, hd, hs]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact ⟨ha, by nlinarith [sq_nonneg a], by nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]⟩
  · rw [min_eq_right hba]
    exact ⟨hb, by nlinarith [sq_nonneg b], by nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]⟩

theorem compare_near_singular {x y : Fin 2 → E 2} {K ε : ℝ} (hK : 0 < K)
    (hε : 0 < ε) (hεsmall : ε < 1 / 1000) (hKε : K * ε < 1 / 1000)
    (hxdet : (Matrix.gram ℝ x).det = ε ^ 2)
    (hydet : 1 / 16 ≤ (Matrix.gram ℝ y).det)
    (hxtrace : 1 ≤ (Matrix.gram ℝ x).trace)
    (hytrace : (Matrix.gram ℝ y).trace ≤ 20) :
    K * (Matrix.gram ℝ x).det < (Matrix.gram ℝ y).det ∧
    K * smallest x < smallest y := by
  obtain ⟨hxnonneg, _, hxbound⟩ := gram_smallest_bounds x
  obtain ⟨hynonneg, hybound, _⟩ := gram_smallest_bounds y
  have hxsmall : smallest x ≤ 2 * ε ^ 2 := by
    rw [hxdet] at hxbound
    calc
      smallest x = 1 * smallest x := (one_mul _).symm
      _ ≤ (Matrix.gram ℝ x).trace * smallest x :=
        mul_le_mul_of_nonneg_right hxtrace hxnonneg
      _ ≤ 2 * ε ^ 2 := hxbound
  have hysmall : 1 / 16 ≤ 20 * smallest y :=
    hydet.trans (hybound.trans (mul_le_mul_of_nonneg_right hytrace hynonneg))
  have hproduct : K * ε ^ 2 < 1 / 1000 * (1 / 1000 : ℝ) := by
    calc
      K * ε ^ 2 = (K * ε) * ε := by ring
      _ < (1 / 1000) * ε := mul_lt_mul_of_pos_right hKε hε
      _ ≤ (1 / 1000) * (1 / 1000) :=
        mul_le_mul_of_nonneg_left hεsmall.le (by norm_num)
  constructor
  · rw [hxdet]
    exact lt_of_lt_of_le (by linarith) hydet
  · have hupper := mul_le_mul_of_nonneg_left hxsmall hK.le
    linarith [show K * (2 * ε ^ 2) = 2 * (K * ε ^ 2) by ring]

theorem choose_epsilon {K : ℝ} (hK : 0 < K) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 1000 ∧ K * ε < 1 / 1000 := by
  let ε : ℝ := (1 / 1000) / (K + 1)
  have hd : 0 < K + 1 := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, ?_, ?_⟩
  · dsimp [ε]
    apply (div_lt_iff₀ hd).2
    linarith
  · have h := mul_lt_mul_of_pos_right (show K < K + 1 by linarith) hε
    calc
      K * ε < (K + 1) * ε := h
      _ = 1 / 1000 := by dsimp [ε]; field_simp

end OMA.Mo491365

namespace OMA.Mo491365Witness

open OMA.S_mo_491365

noncomputable def vectors (s : ℝ) : Fin 2 → E 2 := ![!₂[1, 1], !₂[1, s]]

theorem changeTwo_vectors (s : ℝ) : changeTwo (vectors s) = vectors (2 * s) := by
  funext i
  fin_cases i <;> simp [changeTwo, vectors]

theorem gram_vectors (s : ℝ) :
    Matrix.gram ℝ (vectors s) = !![2, 1 + s; 1 + s, 1 + s ^ 2] := by
  ext i j
  simp only [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [vectors, dotProduct, Fin.sum_univ_two, pow_two, add_comm, one_add_one_eq_two]

theorem trace_vectors (s : ℝ) : (Matrix.gram ℝ (vectors s)).trace = 3 + s ^ 2 := by
  rw [gram_vectors, Matrix.trace_fin_two_of]
  ring

theorem det_vectors (s : ℝ) : (Matrix.gram ℝ (vectors s)).det = (s - 1) ^ 2 := by
  rw [gram_vectors, Matrix.det_fin_two_of]
  ring

theorem independent_vectors (s : ℝ) (hs : s ≠ 1) :
    LinearIndependent ℝ (vectors s) := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, det_vectors]
  exact pow_ne_zero _ (sub_ne_zero.mpr hs)

end OMA.Mo491365Witness

open OMA.S_mo_491365 OMA.Mo491365Witness

theorem OMA.solution : type_of% @OMA.S_mo_491365.main := by
  refine ⟨OMA.Mo491365.largest_comparison, ?_, ?_⟩
  · intro K hK
    obtain ⟨ε, hε, hεsmall, hKε⟩ := OMA.Mo491365.choose_epsilon hK
    refine ⟨vectors (1 + ε), independent_vectors _ (by linarith), ?_⟩
    rw [changeTwo_vectors]
    refine ⟨independent_vectors _ (by linarith), ?_⟩
    apply OMA.Mo491365.compare_near_singular hK hε hεsmall hKε
    · rw [det_vectors]
      ring
    · rw [det_vectors]
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ))
        (show 1 ≤ 2 * (1 + ε) - 1 by linarith) 2
      linarith
    · rw [trace_vectors]
      nlinarith [sq_nonneg (1 + ε)]
    · rw [trace_vectors]
      have h := pow_le_pow_left₀ (show 0 ≤ 2 * (1 + ε) by positivity)
        (show 2 * (1 + ε) ≤ 3 by linarith) 2
      linarith
  · intro K hK
    obtain ⟨ε, hε, hεsmall, hKε⟩ := OMA.Mo491365.choose_epsilon hK
    refine ⟨vectors ((1 + ε) / 2), independent_vectors _ (by linarith), ?_⟩
    rw [changeTwo_vectors]
    rw [show 2 * ((1 + ε) / 2) = 1 + ε by ring]
    refine ⟨independent_vectors _ (by linarith), ?_⟩
    apply OMA.Mo491365.compare_near_singular hK hε hεsmall hKε
    · rw [det_vectors]
      ring
    · rw [det_vectors, show ((1 + ε) / 2 - 1) ^ 2 = (1 - (1 + ε) / 2) ^ 2 by ring]
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (show 1 / 4 ≤ 1 - (1 + ε) / 2 by linarith) 2
      linarith
    · rw [trace_vectors]
      nlinarith [sq_nonneg (1 + ε)]
    · rw [trace_vectors]
      have h := pow_le_pow_left₀ (show 0 ≤ (1 + ε) / 2 by positivity)
        (show (1 + ε) / 2 ≤ 1 by linarith) 2
      linarith
