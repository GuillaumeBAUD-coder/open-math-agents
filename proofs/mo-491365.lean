import OMAStatements.S_mo_491365

open OMA.S_mo_491365 Matrix

namespace GramDeformationComparison

lemma gram_trace_eq {n m : ℕ} (x : Fin (m + 1) → E n) :
    (Matrix.gram ℝ x).trace = ∑ i : Fin (m + 1), ‖x i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.gram_apply, real_inner_self_eq_norm_sq]

lemma gram_eig_nonneg {n m : ℕ} (x : Fin (m + 1) → E n) (i : Fin (m + 1)) :
    0 ≤ (Matrix.isHermitian_gram ℝ x).eigenvalues i :=
  (Matrix.posSemidef_gram ℝ x).eigenvalues_nonneg i

lemma largest_le_sum_sq {n m : ℕ} (x : Fin (m + 1) → E n) :
    largest x ≤ ∑ i : Fin (m + 1), ‖x i‖ ^ 2 := by
  rw [← gram_trace_eq, (Matrix.isHermitian_gram ℝ x).trace_eq_sum_eigenvalues]
  unfold largest
  refine Finset.sup'_le _ _ fun i _ ↦ ?_
  simpa using Finset.single_le_sum (fun j _ ↦ gram_eig_nonneg x j) (Finset.mem_univ i)

lemma sum_sq_le_mul_largest {n m : ℕ} (x : Fin (m + 1) → E n) :
    ∑ i : Fin (m + 1), ‖x i‖ ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * largest x := by
  rw [← gram_trace_eq, (Matrix.isHermitian_gram ℝ x).trace_eq_sum_eigenvalues]
  calc
    ∑ i : Fin (m + 1), (Matrix.isHermitian_gram ℝ x).eigenvalues i ≤
        ∑ _i : Fin (m + 1), largest x :=
      Finset.sum_le_sum fun i _ ↦ Finset.le_sup' _ (Finset.mem_univ i)
    _ = ((m + 1 : ℕ) : ℝ) * largest x := by simp

lemma largest_equiv (n m : ℕ) (T : Fin (m + 1) → E n ≃L[ℝ] E n) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : Fin (m + 1) → E n, c * largest (fun i ↦ T i (x i)) ≤ largest x ∧
        largest x ≤ C * largest (fun i ↦ T i (x i)) := by
  let M : ℝ := 1 + ∑ i : Fin (m + 1), ‖(T i : E n →L[ℝ] E n)‖ ^ 2
  let M' : ℝ := 1 + ∑ i : Fin (m + 1), ‖((T i).symm : E n →L[ℝ] E n)‖ ^ 2
  have hM : 0 < M := by
    dsimp [M]; linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
      sq_nonneg ‖(T i : E n →L[ℝ] E n)‖]
  have hM' : 0 < M' := by
    dsimp [M']; linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
      sq_nonneg ‖((T i).symm : E n →L[ℝ] E n)‖]
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  refine ⟨1 / (((m + 1 : ℕ) : ℝ) * M), by positivity, ((m + 1 : ℕ) : ℝ) * M', by positivity,
    fun x ↦ ⟨?_, ?_⟩⟩
  · have hsum : ∑ i : Fin (m + 1), ‖T i (x i)‖ ^ 2 ≤ M * ∑ i : Fin (m + 1), ‖x i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have h1 : ‖T i (x i)‖ ≤ ‖(T i : E n →L[ℝ] E n)‖ * ‖x i‖ := (T i : E n →L[ℝ] E n).le_opNorm (x i)
      have h2 : ‖(T i : E n →L[ℝ] E n)‖ ^ 2 ≤ M := by
        dsimp [M]
        have := Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖(T j : E n →L[ℝ] E n)‖) (Finset.mem_univ i)
        linarith
      have hsq : ‖T i (x i)‖ ^ 2 ≤ ‖(T i : E n →L[ℝ] E n)‖ ^ 2 * ‖x i‖ ^ 2 := by
        nlinarith [norm_nonneg (T i (x i)), norm_nonneg (x i), norm_nonneg (T i : E n →L[ℝ] E n)]
      exact hsq.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    have hchain : largest (fun i ↦ T i (x i)) ≤ ((m + 1 : ℕ) : ℝ) * M * largest x := by
      calc
        largest (fun i ↦ T i (x i)) ≤ ∑ i : Fin (m + 1), ‖T i (x i)‖ ^ 2 := largest_le_sum_sq _
        _ ≤ M * ∑ i : Fin (m + 1), ‖x i‖ ^ 2 := hsum
        _ ≤ M * (((m + 1 : ℕ) : ℝ) * largest x) := mul_le_mul_of_nonneg_left (sum_sq_le_largest_aux x) hM.le
        _ = ((m + 1 : ℕ) : ℝ) * M * largest x := by ring
    rw [one_div_mul_eq_div, div_le_iff₀ (mul_pos hm hM)]
    linarith
  · have hsum : ∑ i : Fin (m + 1), ‖x i‖ ^ 2 ≤ M' * ∑ i : Fin (m + 1), ‖T i (x i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have h1 : ‖x i‖ ≤ ‖((T i).symm : E n →L[ℝ] E n)‖ * ‖T i (x i)‖ := by
        simpa using ((T i).symm : E n →L[ℝ] E n).le_opNorm (T i (x i))
      have h2 : ‖((T i).symm : E n →L[ℝ] E n)‖ ^ 2 ≤ M' := by
        dsimp [M']
        have := Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖((T j).symm : E n →L[ℝ] E n)‖)
          (Finset.mem_univ i)
        linarith
      have hsq : ‖x i‖ ^ 2 ≤ ‖((T i).symm : E n →L[ℝ] E n)‖ ^ 2 * ‖T i (x i)‖ ^ 2 := by
        nlinarith [norm_nonneg (x i), norm_nonneg (T i (x i)),
          norm_nonneg ((T i).symm : E n →L[ℝ] E n)]
      exact hsq.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    calc
      largest x ≤ ∑ i : Fin (m + 1), ‖x i‖ ^ 2 := largest_le_sum_sq x
      _ ≤ M' * ∑ i : Fin (m + 1), ‖T i (x i)‖ ^ 2 := hsum
      _ ≤ M' * (((m + 1 : ℕ) : ℝ) * largest (fun i ↦ T i (x i))) :=
        mul_le_mul_of_nonneg_left (sum_sq_le_mul_largest _) hM'.le
      _ = ((m + 1 : ℕ) : ℝ) * M' * largest (fun i ↦ T i (x i)) := by ring
where
  sum_sq_le_largest_aux (x : Fin (m + 1) → E n) := sum_sq_le_mul_largest x

lemma gram2_det_eq (u v : E 2) :
    (Matrix.gram ℝ ![u, v]).det = (u 0 * v 1 - u 1 * v 0) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Fin.sum_univ_two]
  ring

lemma gram2_trace_eq (u v : E 2) :
    (Matrix.gram ℝ ![u, v]).trace = u 0 ^ 2 + u 1 ^ 2 + v 0 ^ 2 + v 1 ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.gram_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  ring

lemma smallest_mul_largest_eq_det (x : Fin 2 → E 2) :
    smallest x * largest x = (Matrix.gram ℝ x).det := by
  have hdet := (Matrix.isHermitian_gram ℝ x).det_eq_prod_eigenvalues
  rw [Fin.prod_univ_two] at hdet
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  unfold smallest largest
  set e₀ := (Matrix.isHermitian_gram ℝ x).eigenvalues 0
  set e₁ := (Matrix.isHermitian_gram ℝ x).eigenvalues 1
  have hinf : Finset.univ.inf' Finset.univ_nonempty (Matrix.isHermitian_gram ℝ x).eigenvalues =
      min e₀ e₁ := by
    change Finset.inf' ({0, 1} : Finset (Fin 2)) _ _ = min e₀ e₁
    simp [Finset.inf'_insert, e₀, e₁]
  have hsup : Finset.univ.sup' Finset.univ_nonempty (Matrix.isHermitian_gram ℝ x).eigenvalues =
      max e₀ e₁ := by
    change Finset.sup' ({0, 1} : Finset (Fin 2)) _ _ = max e₀ e₁
    simp [Finset.sup'_insert, e₀, e₁]
  rw [hinf, hsup, min_mul_max, ← hdet]

lemma smallest_bounds (x : Fin 2 → E 2) (htr : 0 < (Matrix.gram ℝ x).trace) :
    (Matrix.gram ℝ x).det / (Matrix.gram ℝ x).trace ≤ smallest x ∧
      smallest x ≤ 2 * (Matrix.gram ℝ x).det / (Matrix.gram ℝ x).trace := by
  have hprod := smallest_mul_largest_eq_det x
  have hle : largest x ≤ (Matrix.gram ℝ x).trace := by
    rw [gram_trace_eq]; exact largest_le_sum_sq x
  have hge : (Matrix.gram ℝ x).trace ≤ 2 * largest x := by
    rw [gram_trace_eq]; simpa using sum_sq_le_mul_largest x
  have hLpos : 0 < largest x := by linarith
  have hSnonneg : 0 ≤ smallest x := by
    unfold smallest
    exact Finset.le_inf' _ _ fun i _ ↦ gram_eig_nonneg x i
  constructor
  · rw [div_le_iff₀ htr]
    calc
      (Matrix.gram ℝ x).det = smallest x * largest x := hprod.symm
      _ ≤ smallest x * (Matrix.gram ℝ x).trace := mul_le_mul_of_nonneg_left hle hSnonneg
  · rw [le_div_iff₀ htr]
    calc
      smallest x * (Matrix.gram ℝ x).trace ≤ smallest x * (2 * largest x) :=
        mul_le_mul_of_nonneg_left hge hSnonneg
      _ = 2 * (Matrix.gram ℝ x).det := by rw [← hprod]; ring

lemma linIndep_fin2_of_det_ne_zero {u v : E 2} (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congr_arg (fun p : E 2 ↦ p 0) hg
  have h1 := congr_arg (fun p : E 2 ↦ p 1) hg
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1
  have hg0 : g 0 = 0 := by
    have : (u 0 * v 1 - u 1 * v 0) * g 0 = 0 := by linear_combination v 1 * h0 - v 0 * h1
    exact (mul_eq_zero.mp this).resolve_left h
  have hg1 : g 1 = 0 := by
    have : (u 0 * v 1 - u 1 * v 0) * g 1 = 0 := by linear_combination u 0 * h1 - u 1 * h0
    exact (mul_eq_zero.mp this).resolve_left h
  intro i; fin_cases i <;> assumption

lemma changeTwo_gt (K : ℝ) (hK : 0 < K) :
    ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧ LinearIndependent ℝ (changeTwo x) ∧
      K * (Matrix.gram ℝ x).det < (Matrix.gram ℝ (changeTwo x)).det ∧
      K * smallest x < smallest (changeTwo x) := by
  let ε : ℝ := 1 / (10 * (K + 1))
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]; rw [div_le_one (by linarith)]; linarith
  have hε2 : 40 * K * ε ^ 2 < 1 := by
    have hK1 : 10 * (K + 1) > 0 := by linarith
    dsimp [ε]
    rw [div_pow, one_pow, mul_div_assoc', mul_one, div_lt_one (by positivity)]
    nlinarith
  let u : E 2 := !₂[1, 1]
  let v : E 2 := !₂[1, 1 + ε]
  let x : Fin 2 → E 2 := ![u, v]
  let y : Fin 2 → E 2 := changeTwo x
  have hy_eq : y = ![u, !₂[1, 2 * (1 + ε)]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [y, changeTwo, x, u, v]
  have hdx : (Matrix.gram ℝ x).det = ε ^ 2 := by
    dsimp [x]; rw [gram2_det_eq]; simp [u, v]
  have hdy : (Matrix.gram ℝ y).det = (1 + 2 * ε) ^ 2 := by
    rw [hy_eq, gram2_det_eq]; simp [u]; ring
  have htx : (Matrix.gram ℝ x).trace = 3 + (1 + ε) ^ 2 := by
    dsimp [x]; rw [gram2_trace_eq]; simp [u, v]; ring
  have hty : (Matrix.gram ℝ y).trace = 3 + (2 * (1 + ε)) ^ 2 := by
    rw [hy_eq, gram2_trace_eq]; simp [u]; ring
  refine ⟨x, linIndep_fin2_of_det_ne_zero (by simp [u, v]; linarith), ?_, ?_, ?_⟩
  · rw [show changeTwo x = y from rfl, hy_eq]
    exact linIndep_fin2_of_det_ne_zero (by simp [u]; linarith)
  · rw [hdx, hdy]; nlinarith
  · have hbx := (smallest_bounds x (by rw [htx]; positivity)).2
    have hby := (smallest_bounds y (by rw [hty]; positivity)).1
    rw [hdx, htx] at hbx
    rw [hdy, hty] at hby
    have hS1 : smallest x ≤ ε ^ 2 := by
      have : 2 * ε ^ 2 / (3 + (1 + ε) ^ 2) ≤ ε ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      exact hbx.trans this
    have hS2 : (1 : ℝ) / 20 ≤ smallest y := by
      have : (1 : ℝ) / 20 ≤ (1 + 2 * ε) ^ 2 / (3 + (2 * (1 + ε)) ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      exact this.trans hby
    nlinarith

lemma changeTwo_lt (K : ℝ) (hK : 0 < K) :
    ∃ x : Fin 2 → E 2, LinearIndependent ℝ x ∧ LinearIndependent ℝ (changeTwo x) ∧
      K * (Matrix.gram ℝ (changeTwo x)).det < (Matrix.gram ℝ x).det ∧
      K * smallest (changeTwo x) < smallest x := by
  let ε : ℝ := 1 / (20 * (K + 1))
  have hε0 : 0 < ε := by positivity
  have hε_half : ε ≤ 1 / 2 := by
    dsimp [ε]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hε2 : 400 * K * ε ^ 2 < 1 := by
    dsimp [ε]
    rw [div_pow, one_pow, mul_div_assoc', mul_one, div_lt_one (by positivity)]
    nlinarith
  let u : E 2 := !₂[1, 2]
  let v : E 2 := !₂[1, 1 + ε]
  let x : Fin 2 → E 2 := ![u, v]
  let y : Fin 2 → E 2 := changeTwo x
  have hy_eq : y = ![u, !₂[1, 2 * (1 + ε)]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [y, changeTwo, x, u, v]
  have hdx : (Matrix.gram ℝ x).det = (1 - ε) ^ 2 := by
    dsimp [x]; rw [gram2_det_eq]; simp [u, v]; ring
  have hdy : (Matrix.gram ℝ y).det = 4 * ε ^ 2 := by
    rw [hy_eq, gram2_det_eq]; simp [u]; ring
  have htx : (Matrix.gram ℝ x).trace = 6 + (1 + ε) ^ 2 := by
    dsimp [x]; rw [gram2_trace_eq]; simp [u, v]; ring
  have hty : (Matrix.gram ℝ y).trace = 6 + (2 * (1 + ε)) ^ 2 := by
    rw [hy_eq, gram2_trace_eq]; simp [u]; ring
  refine ⟨x, linIndep_fin2_of_det_ne_zero (by simp [u, v]; linarith), ?_, ?_, ?_⟩
  · rw [show changeTwo x = y from rfl, hy_eq]
    exact linIndep_fin2_of_det_ne_zero (by simp [u]; linarith)
  · rw [hdx, hdy]; nlinarith
  · have hbx := (smallest_bounds x (by rw [htx]; positivity)).1
    have hby := (smallest_bounds y (by rw [hty]; positivity)).2
    rw [hdx, htx] at hbx
    rw [hdy, hty] at hby
    have hS1 : smallest y ≤ ε ^ 2 := by
      have : 2 * (4 * ε ^ 2) / (6 + (2 * (1 + ε)) ^ 2) ≤ ε ^ 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      exact hby.trans this
    have hS2 : (1 : ℝ) / 40 ≤ smallest x := by
      have : (1 : ℝ) / 40 ≤ (1 - ε) ^ 2 / (6 + (1 + ε) ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      exact this.trans hbx
    nlinarith

end GramDeformationComparison

theorem OMA.solution : type_of% @OMA.S_mo_491365.main := by
  open GramDeformationComparison in
  exact ⟨largest_equiv, changeTwo_gt, changeTwo_lt⟩
