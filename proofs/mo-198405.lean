import OMAStatements.S_mo_198405

open OMA.S_mo_198405 Matrix Finset

namespace SphericalCapSimplex

/-- Determinant of `α • I + β • J` on `Fin n` for `n ≥ 1`. -/
lemma det_smul_one_add_const {n : ℕ} (hn : 1 ≤ n) (α β : ℝ) :
    (Matrix.of fun i j : Fin n ↦ (if i = j then α else 0) + β).det =
      α ^ (n - 1) * (α + (n : ℝ) * β) := by
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ (if i = j then α else 0) + β
  let z0 : Fin n := ⟨0, by omega⟩
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j ↦ (if i = j then (1 : ℝ) else 0) - (if i ≠ z0 ∧ j = z0 then 1 else 0)
  let P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j ↦ (if i = j then (1 : ℝ) else 0) + (if i ≠ z0 ∧ j = z0 then 1 else 0)
  have hQ_tri : Q.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    have hne : i ≠ j := ne_of_lt hlt
    have hj_ne : j ≠ z0 := by
      intro h; subst h
      exact Nat.not_lt_zero _ (Fin.lt_def.mp hlt)
    simp [Q, hne, hj_ne]
  have hP_tri : P.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    have hne : i ≠ j := ne_of_lt hlt
    have hj_ne : j ≠ z0 := by
      intro h; subst h
      exact Nat.not_lt_zero _ (Fin.lt_def.mp hlt)
    simp [P, hne, hj_ne]
  have hQ_det : Q.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular Q hQ_tri]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    by_cases hi : i = z0 <;> simp [Q, hi]
  have hP_det : P.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular P hP_tri]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    by_cases hi : i = z0 <;> simp [P, hi]
  have hQA : ∀ i j : Fin n, (Q * A) i j =
      if i = z0 then (if z0 = j then α else 0) + β
      else (if i = j then α else 0) - (if z0 = j then α else 0) := fun i j ↦ by
    rw [Matrix.mul_apply]
    by_cases hi : i = z0
    · rw [if_pos hi, Finset.sum_eq_single z0]
      · simp [Q, A, hi]
      · intro k _ hk; simp [Q, hi, hk.symm]
      · intro h; exact absurd (Finset.mem_univ z0) h
    · rw [if_neg hi]
      have hzero : ∀ k : Fin n, k ≠ i → k ≠ z0 → Q i k * A k j = 0 := fun k h1 h2 ↦ by
        simp [Q, h1.symm, h2]
      calc
        ∑ k : Fin n, Q i k * A k j = ∑ k ∈ ({i, z0} : Finset (Fin n)), Q i k * A k j := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_).symm
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          exact hzero k hk.1 hk.2
        _ = Q i i * A i j + Q i z0 * A z0 j := Finset.sum_pair hi
        _ = (if i = j then α else 0) - (if z0 = j then α else 0) := by
          simp [Q, A, hi]; ring
  have hQAP : ∀ i j : Fin n, (Q * A * P) i j =
      if j = z0 then (if i = z0 then α + (n : ℝ) * β else 0)
      else (if i = z0 then β else if i = j then α else 0) := fun i j ↦ by
    rw [Matrix.mul_apply]
    by_cases hj : j = z0
    · rw [if_pos hj]
      have hcol0 : ∀ k : Fin n, P k z0 = 1 := fun k ↦ by
        by_cases hk : k = z0 <;> simp [P, hk]
      simp_rw [hj, hcol0, mul_one, hQA]
      by_cases hi : i = z0
      · rw [if_pos hi]
        simp_rw [if_pos hi]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        simp
      · rw [if_neg hi]
        simp_rw [if_neg hi]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
        simp
    · rw [if_neg hj, Finset.sum_eq_single j]
      · rw [hQA]
        have hp : P j j = 1 := by simp [P, hj]
        rw [hp, mul_one]
        by_cases hi : i = z0 <;> simp [hi, Ne.symm hj]
      · intro k _ hkj; simp [P, hkj, hj]
      · intro h; exact absurd (Finset.mem_univ j) h
  have hQAP_tri : (Q * A * P).BlockTriangular id := by
    intro i j hij
    have hj_lt : j < i := hij
    rw [hQAP]
    by_cases hj : j = z0
    · rw [if_pos hj]
      have hi_ne : i ≠ z0 := by
        intro h; subst h; subst hj; exact lt_irrefl _ hj_lt
      rw [if_neg hi_ne]
    · rw [if_neg hj]
      have hi_ne : i ≠ z0 := by
        intro h; subst h; exact Nat.not_lt_zero _ (Fin.lt_def.mp hj_lt)
      rw [if_neg hi_ne, if_neg (ne_of_gt hj_lt)]
  have hdet_eq : A.det = (Q * A * P).det := by
    rw [Matrix.det_mul, Matrix.det_mul, hQ_det, hP_det, one_mul, mul_one]
  rw [hdet_eq, Matrix.det_of_isUpperTriangular hQAP_tri]
  have hprod : ∏ i : Fin n, (Q * A * P) i i =
      (Q * A * P) z0 z0 * ∏ i ∈ Finset.univ.erase z0, (Q * A * P) i i :=
    (Finset.mul_prod_erase Finset.univ (fun i ↦ (Q * A * P) i i) (Finset.mem_univ z0)).symm
  rw [hprod, hQAP z0 z0, if_pos rfl, if_pos rfl]
  have hrest : ∏ i ∈ Finset.univ.erase z0, (Q * A * P) i i = α ^ (n - 1) := by
    have hconst : ∀ i ∈ Finset.univ.erase z0, (Q * A * P) i i = α := fun i hi ↦ by
      have hne : i ≠ z0 := (Finset.mem_erase.mp hi).1
      rw [hQAP i i, if_neg hne, if_neg hne, if_pos rfl]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ z0),
      Finset.card_univ, Fintype.card_fin]
  rw [hrest, mul_comm]

/-- Hadamard / AM-GM determinant bound: if every row of `M` has squared norm `≤ R`, then `|M.det| ≤ √(R ^ N)`. -/
lemma abs_det_le_of_row_sq_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) {R : ℝ} (_hR : 0 ≤ R) (hrow : ∀ i : ι, ∑ j : ι, (M i j) ^ 2 ≤ R) :
    |M.det| ≤ Real.sqrt (R ^ Fintype.card ι) := by
  by_cases hcard : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    rw [hcard, pow_zero, Real.sqrt_one, Matrix.det_isEmpty]
    norm_num
  have hN_pos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hcard
  let G : Matrix ι ι ℝ := M * Mᵀ
  have hG_herm : G.IsHermitian := by
    ext i j
    simp only [G, Matrix.conjTranspose_apply, star_trivial, Matrix.mul_apply, Matrix.transpose_apply,
      mul_comm]
  have hG_psd : ∀ v : ι → ℝ, 0 ≤ dotProduct v (G *ᵥ v) := fun v ↦ by
    have h : dotProduct v (G *ᵥ v) = ∑ j : ι, ((Mᵀ *ᵥ v) j) ^ 2 := by
      dsimp only [G]
      rw [← Matrix.mulVec_mulVec]
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
      have h1 : ∀ i : ι, v i * ∑ k : ι, M i k * ∑ l : ι, M l k * v l =
          ∑ k : ι, (M i k * v i) * ∑ l : ι, M l k * v l := fun i ↦ by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ by ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← Finset.sum_mul, sq]
    rw [h]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have heig_nn : ∀ k : ι, 0 ≤ hG_herm.eigenvalues k := fun k ↦ by
    let v : ι → ℝ := fun i ↦ (hG_herm.eigenvectorBasis k) i
    have hv_eig : G *ᵥ v = hG_herm.eigenvalues k • v :=
      hG_herm.mulVec_eigenvectorBasis k
    have hv_norm : dotProduct v v = 1 := by
      have h1 := hG_herm.eigenvectorBasis.orthonormal.1 k
      rw [EuclideanSpace.norm_eq] at h1
      have hsq : ∑ i : ι, ‖(hG_herm.eigenvectorBasis k) i‖ ^ 2 = 1 := by
        have := congr_arg (fun x : ℝ ↦ x ^ 2) h1
        rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at this
        simpa using this
      simpa [dotProduct, v, sq] using hsq
    have hdot := hG_psd v
    rw [hv_eig, dotProduct_smul, smul_eq_mul, hv_norm, mul_one] at hdot
    exact hdot
  have hdet_prod : M.det ^ 2 = ∏ k : ι, hG_herm.eigenvalues k := by
    have h1 : G.det = M.det ^ 2 := by
      dsimp [G]; rw [Matrix.det_mul, Matrix.det_transpose, sq]
    rw [← h1, hG_herm.det_eq_prod_eigenvalues]
    simp
  have htr_sum : ∑ k : ι, hG_herm.eigenvalues k ≤ (Fintype.card ι : ℝ) * R := by
    have htr : G.trace = ∑ k : ι, hG_herm.eigenvalues k := by
      simpa using hG_herm.trace_eq_sum_eigenvalues
    rw [← htr]
    unfold Matrix.trace Matrix.diag
    calc
      ∑ i : ι, G i i = ∑ i : ι, ∑ j : ι, (M i j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [G, Matrix.mul_apply, Matrix.transpose_apply, sq]
      _ ≤ ∑ _i : ι, R := Finset.sum_le_sum fun i _ ↦ hrow i
      _ = (Fintype.card ι : ℝ) * R := by simp
  let w : ι → ℝ := fun _ ↦ 1 / (Fintype.card ι : ℝ)
  have hw_nn : ∀ k ∈ Finset.univ, 0 ≤ w k := fun _ _ ↦ by dsimp [w]; positivity
  have hw_sum : ∑ k : ι, w k = 1 := by
    dsimp [w]
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    simp [hne]
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ w hG_herm.eigenvalues
    hw_nn hw_sum (fun k _ ↦ heig_nn k)
  have hrhs_le : ∑ k : ι, w k * hG_herm.eigenvalues k ≤ R := by
    dsimp [w]
    rw [← Finset.mul_sum, one_div_mul_eq_div, div_le_iff₀ (by exact_mod_cast hN_pos)]
    linarith
  have hgeom_le : ∏ k : ι, (hG_herm.eigenvalues k) ^ (1 / (Fintype.card ι : ℝ)) ≤ R :=
    hamgm.trans hrhs_le
  have hpow_le : (∏ k : ι, (hG_herm.eigenvalues k) ^ (1 / (Fintype.card ι : ℝ))) ^ Fintype.card ι ≤
      R ^ Fintype.card ι := by
    refine pow_le_pow_left₀ ?_ hgeom_le _
    exact Finset.prod_nonneg fun k _ ↦ Real.rpow_nonneg (heig_nn k) _
  have hlhs_eq : (∏ k : ι, (hG_herm.eigenvalues k) ^ (1 / (Fintype.card ι : ℝ))) ^ Fintype.card ι =
      ∏ k : ι, hG_herm.eigenvalues k := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (heig_nn k)]
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    simp [hne]
  rw [hlhs_eq, ← hdet_prod] at hpow_le
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hpow_le

lemma q_pos {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) : 0 < q n ε := by
  unfold q
  refine lt_min zero_lt_one ?_
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  positivity

lemma q_le_one {n : ℕ} {ε : ℝ} : q n ε ≤ 1 := min_le_left _ _

lemma stretch_sq {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    (stretch n (q n ε)) ^ 2 = q n ε * (2 * (n : ℝ) - ((n : ℝ) + 1) * q n ε) / ((n : ℝ) - 1) := by
  unfold stretch
  refine Real.sq_sqrt ?_
  have hq0 : 0 < q n ε := q_pos hn hε
  have hq1 : q n ε ≤ 1 := q_le_one
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 ≤ 2 * (n : ℝ) - ((n : ℝ) + 1) * q n ε := by nlinarith
  have hden : 0 < (n : ℝ) - 1 := by linarith
  exact div_nonneg (mul_nonneg hq0.le hnum) hden.le

lemma stretch_pos {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) : 0 < stretch n (q n ε) := by
  unfold stretch
  refine Real.sqrt_pos.mpr ?_
  have hq0 : 0 < q n ε := q_pos hn hε
  have hq1 : q n ε ≤ 1 := q_le_one
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 < 2 * (n : ℝ) - ((n : ℝ) + 1) * q n ε := by nlinarith
  have hden : 0 < (n : ℝ) - 1 := by linarith
  exact div_pos (mul_pos hq0 hnum) hden

lemma regularVolume_pos {n : ℕ} (hn : 2 ≤ n) : 0 < regularVolume n := by
  unfold regularVolume
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  positivity

/-- Attainment of `optimalVolume n ε` by the north-pole-apex regular-rim simplex. -/
lemma optimalVolume_mem {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    ∃ (u : Idx n → ℝ) (v : Idx n → Fin n → ℝ),
      admissible n ε u v ∧ volume u v = optimalVolume n ε := by
  let qv : ℝ := q n ε
  let s : ℝ := stretch n qv
  have hq0 : 0 < qv := q_pos hn hε
  have hq1 : qv ≤ 1 := q_le_one
  have hs0 : 0 < s := stretch_pos hn hε
  have hs2 : s ^ 2 = qv * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv) / ((n : ℝ) - 1) := stretch_sq hn hε
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  let u : Idx n → ℝ := Sum.elim (fun _ ↦ 0) (fun _ ↦ qv)
  let v : Idx n → Fin n → ℝ :=
    Sum.elim (fun _ _ ↦ 0) (fun k l ↦ s * ((if k = l then (1 : ℝ) else 0) - 1 / (n : ℝ)))
  refine ⟨u, v, ?_, ?_⟩
  · intro i
    cases i with
    | inl _ =>
      simp [u, v, shape]
      positivity
    | inr k =>
      refine ⟨hq0.le, ?_, ?_, ?_⟩
      · have hle : qv ≤ (n : ℝ) * ε / ((n : ℝ) + 1) := min_le_right _ _
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
        have := (le_div_iff₀ hpos).mp hle
        dsimp [u]; linarith
      · dsimp [v]
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp [hn_pos.ne']
      · dsimp [u, v, shape]
        have hsq_sum : ∑ l : Fin n, (s * ((if k = l then (1 : ℝ) else 0) - 1 / (n : ℝ))) ^ 2 =
            s ^ 2 * (((n : ℝ) - 1) / (n : ℝ)) := by
          have hterm : ∀ l : Fin n,
              (s * ((if k = l then (1 : ℝ) else 0) - 1 / (n : ℝ))) ^ 2 =
                s ^ 2 * ((if k = l then 1 - 2 / (n : ℝ) else 0) + 1 / (n : ℝ) ^ 2) := fun l ↦ by
            by_cases hkl : k = l <;> simp [hkl] <;> ring
          simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          simp only [Finset.mem_univ, if_true]
          congr 1
          field_simp [hn_pos.ne']
          ring
        rw [hsq_sum, hs2]
        have hcalc : qv * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv) / ((n : ℝ) - 1) * (((n : ℝ) - 1) / (n : ℝ)) =
            2 * qv - (1 + 1 / (n : ℝ)) * qv ^ 2 := by
          field_simp [hn_pos.ne', hn1_pos.ne']
        linarith
  · unfold volume optimalVolume
    congr 1
    have hdet : (bary u v).det = qv * s ^ (n - 1) := by
      let M : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun k l ↦ (if k = l then s else 0) + (qv - s) / (n : ℝ)
      have hbary_eq : bary u v =
          Matrix.fromBlocks (Matrix.of fun _ _ : Unit ↦ (1 : ℝ)) (0 : Matrix Unit (Fin n) ℝ)
            (Matrix.of fun (_ : Fin n) (_ : Unit) ↦ 1 - qv) M := by
        ext i j
        cases i <;> cases j
        · simp [bary, u]
        · simp [bary, u, v]
        · simp [bary, u]
        · rename_i k l
          simp only [bary, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, M, u, v]
          by_cases hkl : k = l <;> simp [hkl] <;> ring
      rw [hbary_eq, Matrix.det_fromBlocks_zero₁₂]
      have h1 : (Matrix.of fun _ _ : Unit ↦ (1 : ℝ)).det = 1 := by simp
      rw [h1, one_mul]
      have hM := det_smul_one_add_const (by omega : 1 ≤ n) s ((qv - s) / (n : ℝ))
      dsimp [M] at hM ⊢
      rw [hM]
      have hlin : s + (n : ℝ) * ((qv - s) / (n : ℝ)) = qv := by
        field_simp [hn_pos.ne']; ring
      rw [hlin, mul_comm]
    rw [hdet, abs_of_pos (mul_pos hq0 (pow_pos hs0 _))]

/-- Upper bound: every admissible simplex has `volume u v ≤ optimalVolume n ε`. -/
lemma volume_le_optimalVolume {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε)
    {u : Idx n → ℝ} {v : Idx n → Fin n → ℝ} (hadm : admissible n ε u v) :
    volume u v ≤ optimalVolume n ε := by
  unfold volume optimalVolume
  refine mul_le_mul_of_nonneg_left ?_ (regularVolume_pos hn).le
  let qv : ℝ := q n ε
  let s : ℝ := stretch n qv
  have hq0 : 0 < qv := q_pos hn hε
  have hq1 : qv ≤ 1 := q_le_one
  have hs0 : 0 < s := stretch_pos hn hε
  have hs2 : s ^ 2 = qv * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv) / ((n : ℝ) - 1) := stretch_sq hn hε
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnp1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsqn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  let a : ℝ := (n : ℝ) * qv / ((n : ℝ) + 1)
  let b : ℝ := Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) * s
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hb_pos : 0 < b := by dsimp [b]; positivity
  have hn2m1_pos : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hpos2 : 0 < 2 * (n : ℝ) - ((n : ℝ) + 1) * qv := by nlinarith
  have hb2 : b ^ 2 = (n : ℝ) * qv * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv) / ((n : ℝ) ^ 2 - 1) := by
    dsimp [b]
    rw [mul_pow, Real.sq_sqrt (by positivity), hs2]
    field_simp
    ring
  -- Key enclosing ellipsoid inequality
  have hellip : ∀ i : Idx n, (u i - a) ^ 2 / a ^ 2 + (∑ l : Fin n, (v i l) ^ 2) / b ^ 2 ≤ 1 := by
    intro i
    rcases hadm i with ⟨hu0, hu_cap, _, hv_le⟩
    have hshape_le : (u i - a) ^ 2 / a ^ 2 + shape n (u i) / b ^ 2 ≤ 1 := by
      have hden_pos : 0 < (n : ℝ) * qv ^ 2 * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv) := by
        positivity
      have hident : 1 - (u i - a) ^ 2 / a ^ 2 - shape n (u i) / b ^ 2 =
          2 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) * qv ^ 2 * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv)) *
            (1 - qv) * u i * (qv - u i) := by
        unfold shape
        rw [hb2]
        dsimp [a]
        have hD_pos : 0 < 2 * (n : ℝ) - ((n : ℝ) + 1) * qv := hpos2
        generalize hD_def : 2 * (n : ℝ) - ((n : ℝ) + 1) * qv = D at hD_pos ⊢
        field_simp
        rw [← hD_def]
        ring
      have hrhs_nn : 0 ≤ 2 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) * qv ^ 2 * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv)) *
          (1 - qv) * u i * (qv - u i) := by
        by_cases hq_eq : qv = 1
        · simp [hq_eq]
        · have hq_lt : qv < 1 := lt_of_le_of_ne hq1 hq_eq
          have hq_val : qv = (n : ℝ) * ε / ((n : ℝ) + 1) := by
            dsimp only [qv, q] at hq_lt ⊢
            exact min_eq_right (by
              by_contra hgt; push Not at hgt
              have : min 1 ((n : ℝ) * ε / ((n : ℝ) + 1)) = 1 := min_eq_left hgt.le
              linarith)
          have hui_le : u i ≤ qv := by
            rw [hq_val, le_div_iff₀ hnp1_pos]
            linarith
          have hc_nn : 0 ≤ 2 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) * qv ^ 2 * (2 * (n : ℝ) - ((n : ℝ) + 1) * qv)) :=
            div_nonneg (by positivity) hden_pos.le
          have h1 : 0 ≤ 1 - qv := by linarith
          have h2 : 0 ≤ qv - u i := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hc_nn h1) hu0) h2
      linarith
    have hdiv_le : (∑ l : Fin n, (v i l) ^ 2) / b ^ 2 ≤ shape n (u i) / b ^ 2 :=
      div_le_div_of_nonneg_right hv_le (sq_nonneg b)
    linarith
  -- Construct the explicit scaling matrix `C` such that `M := bary u v * C` has row sq norms `≤ (n + 1) / n`
  let γ : ℝ := 1 / (a * Real.sqrt (n : ℝ)) - 1 / ((n : ℝ) * b) - 1 / Real.sqrt (n : ℝ)
  let C : Matrix (Idx n) (Idx n) ℝ := Matrix.of fun r c ↦
    match r, c with
    | .inl _, .inl _ => 1 / Real.sqrt (n : ℝ)
    | .inl _, .inr _ => -(1 / Real.sqrt (n : ℝ))
    | .inr _, .inl _ => 1 / Real.sqrt (n : ℝ)
    | .inr k, .inr l => (if k = l then 1 / b else 0) + γ
  let M : Matrix (Idx n) (Idx n) ℝ := bary u v * C
  have hM_inl : ∀ i : Idx n, M i (.inl ()) = 1 / Real.sqrt (n : ℝ) := fun i ↦ by
    dsimp [M]
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, bary, C, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, (hadm i).2.2.1, add_zero]
    field_simp [hn_pos.ne', hsqn_pos.ne']
    ring
  have hM_inr : ∀ (i : Idx n) (l : Fin n),
      M i (.inr l) = (u i - a) / (a * Real.sqrt (n : ℝ)) + v i l / b := fun i l ↦ by
    dsimp [M]
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, bary, C, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    have hsum : ∑ k : Fin n, (u i / (n : ℝ) + v i k) * ((if k = l then 1 / b else 0) + γ) =
        (u i / (n : ℝ) + v i l) * (1 / b) + u i * γ := by
      have hterm : ∀ k : Fin n,
          (u i / (n : ℝ) + v i k) * ((if k = l then 1 / b else 0) + γ) =
            (if k = l then (u i / (n : ℝ) + v i k) * (1 / b) else 0) +
              (u i / (n : ℝ) + v i k) * γ := fun k ↦ by
        by_cases hkl : k = l
        · simp [hkl]; ring
        · simp [hkl]
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, (hadm i).2.2.1, add_zero]
      congr 1
      field_simp [hn_pos.ne']
    rw [hsum]
    dsimp [γ]
    field_simp [hn_pos.ne', hsqn_pos.ne', ha_pos.ne', hb_pos.ne']
    ring
  have hM_row : ∀ i : Idx n, ∑ j : Idx n, (M i j) ^ 2 ≤ ((n : ℝ) + 1) / (n : ℝ) := fun i ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_unique, hM_inl i]
    simp_rw [hM_inr i]
    have hsum_inr : ∑ l : Fin n, ((u i - a) / (a * Real.sqrt (n : ℝ)) + v i l / b) ^ 2 =
        (u i - a) ^ 2 / a ^ 2 + (∑ l : Fin n, (v i l) ^ 2) / b ^ 2 := by
      have hterm : ∀ l : Fin n,
          ((u i - a) / (a * Real.sqrt (n : ℝ)) + v i l / b) ^ 2 =
            (u i - a) ^ 2 / (a ^ 2 * (n : ℝ)) +
              (2 * (u i - a) / (a * Real.sqrt (n : ℝ) * b)) * v i l +
              (v i l) ^ 2 / b ^ 2 := fun l ↦ by
        have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
        field_simp [ha_pos.ne', hb_pos.ne', hsqn_pos.ne', hn_pos.ne']
        linear_combination -(u i - a) ^ 2 * b ^ 2 * hsq
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, (hadm i).2.2.1, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
      congr 1
      field_simp [hn_pos.ne', ha_pos.ne']
    rw [hsum_inr]
    have h1 : (1 / Real.sqrt (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt hn_pos.le]
    rw [h1]
    have hbound := hellip i
    have hsplit : ((n : ℝ) + 1) / (n : ℝ) = 1 / (n : ℝ) + 1 := by
      field_simp [hn_pos.ne']; ring
    linarith
  have hC_det : C.det = 1 / (a * b ^ (n - 1)) := by
    let E : Matrix (Idx n) (Idx n) ℝ := Matrix.of fun r c ↦
      match r, c with
      | .inl _, .inl _ => 1
      | .inl _, .inr _ => 1
      | .inr _, .inl _ => 0
      | .inr k, .inr l => if k = l then 1 else 0
    have hE_det : E.det = 1 := by
      have hE_eq : E = Matrix.fromBlocks (Matrix.of fun _ _ : Unit ↦ (1 : ℝ))
          (Matrix.of fun (_ : Unit) (_ : Fin n) ↦ (1 : ℝ))
          (0 : Matrix (Fin n) Unit ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) := by
        ext r c
        cases r <;> cases c <;> simp [E, Matrix.one_apply]
      rw [hE_eq, Matrix.det_fromBlocks_zero₂₁]
      simp
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun k l ↦ (if k = l then 1 / b else 0) + (1 / (a * Real.sqrt (n : ℝ)) - 1 / ((n : ℝ) * b))
    have hCE : C * E = Matrix.fromBlocks (Matrix.of fun _ _ : Unit ↦ 1 / Real.sqrt (n : ℝ))
        (0 : Matrix Unit (Fin n) ℝ)
        (Matrix.of fun (_ : Fin n) (_ : Unit) ↦ 1 / Real.sqrt (n : ℝ)) D := by
      ext r c
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
      cases r <;> cases c
      · simp [C, E]
      · simp [C, E]
      · simp [C, E]
      · rename_i k l
        simp only [C, E, D, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ l)]
        dsimp [γ]
        ring
    have h1 : C.det = (C * E).det := by rw [Matrix.det_mul, hE_det, mul_one]
    rw [h1, hCE, Matrix.det_fromBlocks_zero₁₂]
    have htl : (Matrix.of fun _ _ : Unit ↦ 1 / Real.sqrt (n : ℝ)).det = 1 / Real.sqrt (n : ℝ) := by
      simp
    rw [htl]
    have hD := det_smul_one_add_const (by omega : 1 ≤ n) (1 / b)
      (1 / (a * Real.sqrt (n : ℝ)) - 1 / ((n : ℝ) * b))
    dsimp [D] at hD ⊢
    rw [hD]
    have hlin : 1 / b + (n : ℝ) * (1 / (a * Real.sqrt (n : ℝ)) - 1 / ((n : ℝ) * b)) =
        Real.sqrt (n : ℝ) / a := by
      have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
      field_simp [hn_pos.ne', ha_pos.ne', hb_pos.ne', hsqn_pos.ne']
      linear_combination -b * hsq
    rw [hlin]
    rw [_root_.one_div_pow]
    field_simp [hsqn_pos.ne', ha_pos.ne', hb_pos.ne']
  have hM_bound := abs_det_le_of_row_sq_sum_le M (by positivity) hM_row
  have hcard : Fintype.card (Idx n) = n + 1 := by
    simp [Idx, add_comm]
  rw [hcard] at hM_bound
  have hM_det : |M.det| = |(bary u v).det| / (a * b ^ (n - 1)) := by
    dsimp [M]
    rw [Matrix.det_mul, abs_mul, hC_det, abs_of_pos (by positivity : 0 < 1 / (a * b ^ (n - 1)))]
    ring
  rw [hM_det, div_le_iff₀ (by positivity)] at hM_bound
  have hrhs_eq : Real.sqrt ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) * (a * b ^ (n - 1)) =
      qv * s ^ (n - 1) := by
    have hlhs_nn : 0 ≤ Real.sqrt ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) * (a * b ^ (n - 1)) := by
      positivity
    have hrhs_nn : 0 ≤ qv * s ^ (n - 1) := by positivity
    have hsq_eq : (Real.sqrt ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) * (a * b ^ (n - 1))) ^ 2 =
        (qv * s ^ (n - 1)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow, mul_pow]
      dsimp [a, b]
      rw [mul_pow, ← pow_mul, mul_comm (n - 1) 2, pow_mul, Real.sq_sqrt (by positivity)]
      have hexp : 2 + (n - 1) = n + 1 := by omega
      have hpow_cancel : ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) *
          (((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1)) ^ (n - 1)) = 1 := by
        rw [← pow_add, hexp, ← mul_pow]
        have h1 : (((n : ℝ) + 1) / (n : ℝ)) * ((n : ℝ) / ((n : ℝ) + 1)) = 1 := by
          field_simp [hn_pos.ne', hnp1_pos.ne']
        rw [h1, one_pow]
      have hrearr : ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) *
          ((((n : ℝ) * qv / ((n : ℝ) + 1)) ^ 2 *
            (((n : ℝ) / ((n : ℝ) + 1)) ^ (n - 1) * (s ^ (n - 1)) ^ 2))) =
          ((((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1)) *
            (((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1)) ^ (n - 1)) *
            (qv ^ 2 * (s ^ (n - 1)) ^ 2) := by
        ring
      rw [hrearr, hpow_cancel, one_mul]
      ring
    nlinarith
  linarith

end SphericalCapSimplex

theorem OMA.solution : type_of% @OMA.S_mo_198405.main := by
  refine ⟨fun ε hε0 hε2 ↦ ?_, fun n hn ε hε0 _hε2 ↦ ?_⟩
  · rw [Real.diam_Icc (by linarith)]
    ring
  · refine ⟨?_, ?_⟩
    · exact SphericalCapSimplex.optimalVolume_mem hn hε0
    · rintro V ⟨u, v, hadm, rfl⟩
      exact SphericalCapSimplex.volume_le_optimalVolume hn hε0 hadm
