import OMAStatements.S_mo_228115

open OMA.S_mo_228115 Matrix Finset

namespace NearestKronecker

lemma orth_transpose_mul_self {n : ℕ} (Q : Orth n) : (Q : Sq n)ᵀ * (Q : Sq n) = 1 := by
  have h := (Unitary.mem_iff.mp Q.2).1
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma orth_mul_transpose_self {n : ℕ} (Q : Orth n) : (Q : Sq n) * (Q : Sq n)ᵀ = 1 := by
  have h := (Unitary.mem_iff.mp Q.2).2
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma orth_col_sq_sum {n : ℕ} (Q : Orth n) (j : Fin n) :
    ∑ i : Fin n, ((Q : Sq n) i j) ^ 2 = 1 := by
  have h := congr_fun (congr_fun (orth_transpose_mul_self Q) j) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using h

lemma orth_sq_sum {n : ℕ} (Q : Orth n) :
    ∑ i : Fin n, ∑ j : Fin n, ((Q : Sq n) i j) ^ 2 = (n : ℝ) := by
  rw [Finset.sum_comm]
  simp_rw [orth_col_sq_sum Q]
  simp

lemma orth_of_transpose_mul_self {n : ℕ} {U : Sq n} (h : Uᵀ * U = 1) : U ∈ unitary (Sq n) := by
  have hdet : IsUnit U.det := by
    have hd : Uᵀ.det * U.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
    exact isUnit_iff_ne_zero.mpr fun h0 ↦ by rw [h0, mul_zero] at hd; norm_num at hd
  have h2 : U * Uᵀ = 1 := by
    have hinv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hdet
    have heq : Uᵀ = U⁻¹ := by
      calc Uᵀ = Uᵀ * (U * U⁻¹) := by rw [hinv, mul_one]
      _ = (Uᵀ * U) * U⁻¹ := by rw [Matrix.mul_assoc]
      _ = U⁻¹ := by rw [h, one_mul]
    rw [heq, hinv]
  rw [Unitary.mem_iff]
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using ⟨h, h2⟩

lemma orth_of_orthonormalBasis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ Q : Orth n, ∀ i j : Fin n, (Q : Sq n) i j = (b j) i := by
  let U : Sq n := Matrix.of fun i j ↦ (b j) i
  have hUtU : Uᵀ * U = 1 := by
    ext i j
    simp only [U, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    have hinner := orthonormal_iff_ite.mp b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [dotProduct, mul_comm] using hinner
  exact ⟨⟨U, orth_of_transpose_mul_self hUtU⟩, fun i j ↦ rfl⟩

lemma cauchy_schwarz_sum {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * y i ≤ Real.sqrt (∑ i : Fin n, x i ^ 2) * Real.sqrt (∑ i : Fin n, y i ^ 2) := by
  have h1 : (∑ i : Fin n, x i * y i) ^ 2 ≤ (∑ i : Fin n, x i ^ 2) * (∑ i : Fin n, y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have h2 : Real.sqrt ((∑ i : Fin n, x i * y i) ^ 2) ≤
      Real.sqrt ((∑ i : Fin n, x i ^ 2) * (∑ i : Fin n, y i ^ 2)) :=
    Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at h2
  exact (le_abs_self _).trans h2

lemma loss_eq_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Blocks ι n) (p : Equiv.Perm ι) (Q : Orth n) :
    loss A p Q = sizeSq A + (Fintype.card ι : ℝ) * n - 2 * score (blockSum A p) Q := by
  unfold loss sizeSq score blockSum
  have hexp : ∀ a b : ι, ∀ i j : Fin n,
      (A (a, i) (b, j) - (if p a = b then (Q : Sq n) i j else 0)) ^ 2 =
        A (a, i) (b, j) ^ 2 + (if p a = b then ((Q : Sq n) i j) ^ 2 else 0) -
          2 * (if p a = b then A (a, i) (b, j) * (Q : Sq n) i j else 0) := by
    intro a b i j
    by_cases h : p a = b
    · simp [h]; ring
    · simp [h]
  simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hQterm : ∑ a : ι, ∑ b : ι, ∑ i : Fin n, ∑ j : Fin n,
      (if p a = b then ((Q : Sq n) i j) ^ 2 else 0) = (Fintype.card ι : ℝ) * n := by
    have h1 : ∀ a : ι, ∑ b : ι, ∑ i : Fin n, ∑ j : Fin n,
        (if p a = b then ((Q : Sq n) i j) ^ 2 else 0) = (n : ℝ) := fun a ↦ by
      rw [Finset.sum_eq_single (p a)]
      · simp only [if_true]
        exact orth_sq_sum Q
      · intro b _ hba
        simp [Ne.symm hba]
      · intro h; exact absurd (Finset.mem_univ (p a)) h
    simp_rw [h1]
    simp
  have hcross : ∑ a : ι, ∑ b : ι, ∑ i : Fin n, ∑ j : Fin n,
      2 * (if p a = b then A (a, i) (b, j) * (Q : Sq n) i j else 0) =
      2 * ((Q : Sq n)ᵀ * Matrix.of fun i j ↦ ∑ a : ι, A (a, i) (p a, j)).trace := by
    have h1 : ∀ a : ι, ∑ b : ι, ∑ i : Fin n, ∑ j : Fin n,
        2 * (if p a = b then A (a, i) (b, j) * (Q : Sq n) i j else 0) =
        2 * ∑ i : Fin n, ∑ j : Fin n, A (a, i) (p a, j) * (Q : Sq n) i j := fun a ↦ by
      rw [Finset.sum_eq_single (p a)]
      · simp only [if_true, ← Finset.mul_sum]
      · intro b _ hba
        simp [Ne.symm hba]
      · intro h; exact absurd (Finset.mem_univ (p a)) h
    simp_rw [h1, ← Finset.mul_sum]
    congr 1
    unfold Matrix.trace Matrix.diag
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    calc
      ∑ a : ι, ∑ i : Fin n, ∑ j : Fin n, A (a, i) (p a, j) * (Q : Sq n) i j
          = ∑ i : Fin n, ∑ a : ι, ∑ j : Fin n, A (a, i) (p a, j) * (Q : Sq n) i j :=
        Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ a : ι, A (a, i) (p a, j) * (Q : Sq n) i j :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ j : Fin n, ∑ i : Fin n, ∑ a : ι, A (a, i) (p a, j) * (Q : Sq n) i j :=
        Finset.sum_comm
      _ = ∑ j : Fin n, ∑ i : Fin n, (Q : Sq n) i j * ∑ a : ι, A (a, i) (p a, j) := by
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [hQterm, hcross]

/-- Classical orthogonal Procrustes theorem: `nuclear S` is the exact maximum of `score S Q` over `Q ∈ Orth n`. -/
lemma isGreatest_score_nuclear {n : ℕ} (S : Sq n) :
    IsGreatest (Set.range (fun Q : Orth n ↦ score S Q)) (nuclear S) := by
  let hH := Matrix.isHermitian_conjTranspose_mul_self S
  let V : Orth n := hH.eigenvectorUnitary
  let W : Sq n := S * (V : Sq n)
  have hVtV : (V : Sq n)ᵀ * (V : Sq n) = 1 := orth_transpose_mul_self V
  have hVVt : (V : Sq n) * (V : Sq n)ᵀ = 1 := orth_mul_transpose_self V
  have hspec : Sᵀ * S = (V : Sq n) * Matrix.diagonal hH.eigenvalues * (V : Sq n)ᵀ := by
    calc
      Sᵀ * S = Sᴴ * S := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = ((Unitary.conjStarAlgAut ℝ (Sq n)) V) (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) :=
        hH.spectral_theorem
      _ = (V : Sq n) * Matrix.diagonal hH.eigenvalues * (V : Sq n)ᵀ := by
        simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_eq_transpose_of_trivial]
  have hWtW : Wᵀ * W = Matrix.diagonal hH.eigenvalues := by
    dsimp only [W]
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Sᵀ S (V : Sq n), hspec]
    calc
      (V : Sq n)ᵀ * ((V : Sq n) * Matrix.diagonal hH.eigenvalues * (V : Sq n)ᵀ * (V : Sq n))
          = ((V : Sq n)ᵀ * (V : Sq n)) * Matrix.diagonal hH.eigenvalues *
              ((V : Sq n)ᵀ * (V : Sq n)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal hH.eigenvalues := by
        rw [hVtV, one_mul, mul_one]
  have hW_inner : ∀ i j : Fin n,
      ∑ k : Fin n, W k i * W k j = if i = j then hH.eigenvalues i else 0 := fun i j ↦ by
    have h := congr_fun (congr_fun hWtW i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply] using h
  have heig_nn : ∀ j : Fin n, 0 ≤ hH.eigenvalues j := fun j ↦ by
    have h := hW_inner j j
    simp only [if_true] at h
    rw [← h]
    exact Finset.sum_nonneg fun k _ ↦ mul_self_nonneg (W k j)
  let σ : Fin n → ℝ := fun j ↦ Real.sqrt (hH.eigenvalues j)
  have hσ_sq : ∀ j : Fin n, σ j ^ 2 = hH.eigenvalues j := fun j ↦ Real.sq_sqrt (heig_nn j)
  have hW_sq : ∀ j : Fin n, ∑ k : Fin n, (W k j) ^ 2 = hH.eigenvalues j := fun j ↦ by
    have h := hW_inner j j
    simpa [sq] using h
  refine ⟨?_, ?_⟩
  · -- Attainment: build orthogonal U matching normalized nonzero columns of W, then Q = U * Vᵀ
    let s : Set (Fin n) := {j | 0 < σ j}
    let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j ↦
      (1 / σ j) • WithLp.toLp 2 (fun k ↦ W k j)
    have hv_orth : Orthonormal ℝ (s.domRestrict v) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi0 : 0 < σ i := hi
      simp only [Set.domRestrict_apply, v, inner_smul_left, inner_smul_right,
        conj_trivial, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
      have hdot : ∑ k : Fin n, W k j * W k i = if i = j then hH.eigenvalues i else 0 := by
        simpa [mul_comm] using hW_inner i j
      rw [hdot]
      by_cases hij : i = j
      · subst hij
        simp only [if_true, ← hσ_sq i]
        field_simp [hi0.ne']
      · have hne : (⟨i, hi⟩ : s) ≠ ⟨j, hj⟩ := fun h ↦ hij (congr_arg Subtype.val h)
        simp [hij, hne]
    have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
      simp [finrank_euclideanSpace]
    obtain ⟨b, hb⟩ := hv_orth.exists_orthonormalBasis_extension_of_card_eq hfinrank
    obtain ⟨U, hU⟩ := orth_of_orthonormalBasis b
    let Q : Orth n := ⟨(U : Sq n) * (V : Sq n)ᵀ, by
      refine orth_of_transpose_mul_self ?_
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (U : Sq n)ᵀ (U : Sq n) (V : Sq n)ᵀ, orth_transpose_mul_self U,
        one_mul, hVVt]⟩
    refine ⟨Q, ?_⟩
    dsimp only
    unfold score nuclear
    have htr : ((Q : Sq n)ᵀ * S).trace = ((U : Sq n)ᵀ * W).trace := by
      have hQ : (Q : Sq n)ᵀ = (V : Sq n) * (U : Sq n)ᵀ := by
        simp [Q, Matrix.transpose_mul]
      rw [hQ, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [htr]
    unfold Matrix.trace Matrix.diag
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hU]
    by_cases hpos : 0 < σ j
    · have hbj : b j = v j := hb j hpos
      rw [hbj]
      simp only [v, PiLp.smul_apply, smul_eq_mul]
      calc
        ∑ k : Fin n, (1 / σ j * W k j) * W k j
            = (1 / σ j) * ∑ k : Fin n, (W k j) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = (1 / σ j) * (σ j ^ 2) := by rw [hW_sq j, hσ_sq j]
        _ = σ j := by field_simp [hpos.ne']
    · have hσ0 : σ j = 0 := le_antisymm (not_lt.mp hpos) (Real.sqrt_nonneg _)
      have heig0 : hH.eigenvalues j = 0 := by
        rw [← hσ_sq j, hσ0, sq, mul_zero]
      have hW0 : ∀ k : Fin n, W k j = 0 := fun k ↦ by
        have hsum0 : ∑ l : Fin n, (W l j) ^ 2 = 0 := by rw [hW_sq j, heig0]
        have hle : (W k j) ^ 2 ≤ 0 := by
          rw [← hsum0]
          exact Finset.single_le_sum (fun l _ ↦ sq_nonneg (W l j)) (Finset.mem_univ k)
        exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
      simp [hW0]
      exact hσ0.symm
  · -- Upper bound: for every Q ∈ Orth n, score S Q ≤ nuclear S
    rintro _ ⟨Q, rfl⟩
    dsimp only
    unfold score nuclear
    let U : Orth n := ⟨(Q : Sq n) * (V : Sq n), by
      refine orth_of_transpose_mul_self ?_
      rw [Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (Q : Sq n)ᵀ (Q : Sq n) (V : Sq n), orth_transpose_mul_self Q,
        one_mul, hVtV]⟩
    have htr : ((Q : Sq n)ᵀ * S).trace = ((U : Sq n)ᵀ * W).trace := by
      calc
        ((Q : Sq n)ᵀ * S).trace
            = (((Q : Sq n)ᵀ * S) * ((V : Sq n) * (V : Sq n)ᵀ)).trace := by
          rw [hVVt, mul_one]
        _ = ((V : Sq n)ᵀ * ((Q : Sq n)ᵀ * S * (V : Sq n))).trace := by
          rw [← Matrix.mul_assoc ((Q : Sq n)ᵀ * S) (V : Sq n) (V : Sq n)ᵀ, Matrix.trace_mul_comm]
        _ = ((U : Sq n)ᵀ * W).trace := by
          simp [U, W, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [htr]
    unfold Matrix.trace Matrix.diag
    refine Finset.sum_le_sum fun j _ ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hcs := cauchy_schwarz_sum (fun k ↦ (U : Sq n) k j) (fun k ↦ W k j)
    rw [orth_col_sq_sum U j, Real.sqrt_one, one_mul, hW_sq j] at hcs
    exact hcs

/-- Nuclear norm of a matrix whose only nonzero column is column `0` equals the `ℓ²` norm of column `0`. -/
lemma nuclear_sq_of_single_col {m : ℕ} (S : Sq (m + 1))
    (hzero : ∀ i j : Fin (m + 1), j ≠ 0 → S i j = 0) :
    nuclear S ^ 2 = ∑ i : Fin (m + 1), (S i 0) ^ 2 := by
  let w : Fin (m + 1) → ℝ := fun i ↦ S i 0
  let r : ℝ := Real.sqrt (∑ i : Fin (m + 1), (w i) ^ 2)
  have hscore_eq : ∀ Q : Orth (m + 1), score S Q = ∑ i : Fin (m + 1), (Q : Sq (m + 1)) i 0 * w i := by
    intro Q
    unfold score Matrix.trace Matrix.diag
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp only [Matrix.mul_apply, Matrix.transpose_apply, w]
    · intro j _ hj
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hzero i j hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin (m + 1))) h
  have hr_greatest : IsGreatest (Set.range (fun Q : Orth (m + 1) ↦ score S Q)) r := by
    refine ⟨?_, ?_⟩
    · by_cases hr0 : r = 0
      · refine ⟨1, ?_⟩
        dsimp only
        rw [hscore_eq 1, hr0]
        have hsum0 : ∑ i : Fin (m + 1), (w i) ^ 2 = 0 := by
          have := congr_arg (fun t : ℝ ↦ t ^ 2) hr0
          rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)] at this
          simpa using this
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        have hwi : w i = 0 := by
          have hle : (w i) ^ 2 ≤ 0 := by
            rw [← hsum0]
            exact Finset.single_le_sum (fun l _ ↦ sq_nonneg (w l)) (Finset.mem_univ i)
          exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
        rw [hwi, mul_zero]
      · have hr_pos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
        let s : Set (Fin (m + 1)) := {0}
        let v : Fin (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) := fun _ ↦
          (1 / r) • WithLp.toLp 2 w
        have hv_orth : Orthonormal ℝ (s.domRestrict v) := by
          rw [orthonormal_iff_ite]
          rintro ⟨i, hi⟩ ⟨j, hj⟩
          have hi0 : i = 0 := hi
          have hj0 : j = 0 := hj
          subst hi0; subst hj0
          simp only [Set.domRestrict_apply, v, inner_smul_left, inner_smul_right,
            conj_trivial, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
            if_true]
          have hr2 : ∑ k : Fin (m + 1), w k * w k = r ^ 2 := by
            simp_rw [← sq]
            exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).symm
          rw [hr2]
          field_simp [hr_pos.ne']
        have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = Fintype.card (Fin (m + 1)) := by
          simp [finrank_euclideanSpace]
        obtain ⟨b, hb⟩ := hv_orth.exists_orthonormalBasis_extension_of_card_eq hfinrank
        obtain ⟨Q, hQ⟩ := orth_of_orthonormalBasis b
        refine ⟨Q, ?_⟩
        dsimp only
        rw [hscore_eq Q]
        have hb0 : b 0 = v 0 := hb 0 rfl
        simp_rw [hQ, hb0]
        simp only [v, PiLp.smul_apply, smul_eq_mul]
        calc
          ∑ i : Fin (m + 1), (1 / r * w i) * w i
              = (1 / r) * ∑ i : Fin (m + 1), (w i) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ ↦ by ring
          _ = (1 / r) * r ^ 2 := by
            rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
          _ = r := by field_simp [hr_pos.ne']
    · rintro _ ⟨Q, rfl⟩
      dsimp only
      rw [hscore_eq Q]
      have hcs := cauchy_schwarz_sum (fun i ↦ (Q : Sq (m + 1)) i 0) w
      rw [orth_col_sq_sum Q 0, Real.sqrt_one, one_mul] at hcs
      exact hcs
  have hEq : nuclear S = r := (isGreatest_score_nuclear S).unique hr_greatest
  rw [hEq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Rounding a `{-1, 0, 1}` vertex assignment to `{-1, 1}` without decreasing the quadratic cut value. -/
lemma exists_bool_cut_ge {v e : ℕ} (s t : Fin e → Fin v) :
    ∀ (m : ℕ) (c : Fin v → ℝ),
      (∀ u, c u = -1 ∨ c u = 0 ∨ c u = 1) →
      (Finset.univ.filter fun u ↦ c u = 0).card ≤ m →
      ∃ b : Fin v → Bool,
        ∑ a : Fin e, (c (s a) - c (t a)) ^ 2 ≤ 4 * (cut s t b : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro c hc hcard
    have hne0 : ∀ u : Fin v, c u ≠ 0 := by
      intro u hu
      have hmem : u ∈ Finset.univ.filter fun u ↦ c u = 0 := by simp [hu]
      have hpos : 0 < (Finset.univ.filter fun u ↦ c u = 0).card := Finset.card_pos.mpr ⟨u, hmem⟩
      omega
    let b : Fin v → Bool := fun u ↦ decide (c u = -1)
    refine ⟨b, ?_⟩
    unfold cut
    rw [Nat.cast_sum, Finset.mul_sum]
    refine le_of_eq (Finset.sum_congr rfl fun a _ ↦ ?_)
    have hs : c (s a) = -1 ∨ c (s a) = 1 := by
      rcases hc (s a) with h | h | h
      · exact Or.inl h
      · exact absurd h (hne0 (s a))
      · exact Or.inr h
    have ht : c (t a) = -1 ∨ c (t a) = 1 := by
      rcases hc (t a) with h | h | h
      · exact Or.inl h
      · exact absurd h (hne0 (t a))
      · exact Or.inr h
    rcases hs with hs | hs <;> rcases ht with ht | ht <;> simp [b, hs, ht] <;> norm_num
  | succ m ih =>
    intro c hc hcard
    by_cases hempty : (Finset.univ.filter fun u ↦ c u = 0).card = 0
    · exact ih c hc (by omega)
    · obtain ⟨u0, hu0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
      have hcu0 : c u0 = 0 := (Finset.mem_filter.mp hu0).2
      let cPos : Fin v → ℝ := Function.update c u0 1
      let cNeg : Fin v → ℝ := Function.update c u0 (-1)
      have hcPos : ∀ u, cPos u = -1 ∨ cPos u = 0 ∨ cPos u = 1 := fun u ↦ by
        by_cases h : u = u0
        · subst h; simp [cPos]
        · simpa [cPos, h] using hc u
      have hcNeg : ∀ u, cNeg u = -1 ∨ cNeg u = 0 ∨ cNeg u = 1 := fun u ↦ by
        by_cases h : u = u0
        · subst h; simp [cNeg]
        · simpa [cNeg, h] using hc u
      have hsubPos : (Finset.univ.filter fun u ↦ cPos u = 0) ⊆
          (Finset.univ.filter fun u ↦ c u = 0).erase u0 := by
        intro u hu
        have h0 : cPos u = 0 := (Finset.mem_filter.mp hu).2
        have hne : u ≠ u0 := by
          intro heq; subst heq; simp [cPos] at h0
        simp [Finset.mem_erase, hne, cPos] at h0 ⊢
        exact h0
      have hsubNeg : (Finset.univ.filter fun u ↦ cNeg u = 0) ⊆
          (Finset.univ.filter fun u ↦ c u = 0).erase u0 := by
        intro u hu
        have h0 : cNeg u = 0 := (Finset.mem_filter.mp hu).2
        have hne : u ≠ u0 := by
          intro heq; subst heq; simp [cNeg] at h0
        simp [Finset.mem_erase, hne, cNeg] at h0 ⊢
        exact h0
      have hcard_erase : ((Finset.univ.filter fun u ↦ c u = 0).erase u0).card ≤ m := by
        rw [Finset.card_erase_of_mem hu0]; omega
      have hcardPos : (Finset.univ.filter fun u ↦ cPos u = 0).card ≤ m :=
        (Finset.card_le_card hsubPos).trans hcard_erase
      have hcardNeg : (Finset.univ.filter fun u ↦ cNeg u = 0).card ≤ m :=
        (Finset.card_le_card hsubNeg).trans hcard_erase
      have havg : 2 * ∑ a : Fin e, (c (s a) - c (t a)) ^ 2 ≤
          ∑ a : Fin e, (cPos (s a) - cPos (t a)) ^ 2 +
            ∑ a : Fin e, (cNeg (s a) - cNeg (t a)) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun a _ ↦ ?_
        by_cases hs : s a = u0 <;> by_cases ht : t a = u0
        · simp [cPos, cNeg, hs, ht, hcu0]
        · simp only [cPos, cNeg, Function.update_apply, hs, ht, ↓reduceIte, hcu0]
          nlinarith
        · simp only [cPos, cNeg, Function.update_apply, hs, ht, ↓reduceIte, hcu0]
          nlinarith
        · simp only [cPos, cNeg, Function.update_apply, hs, ht, ↓reduceIte]
          ring_nf
          exact le_rfl
      by_cases hcmp : ∑ a : Fin e, (c (s a) - c (t a)) ^ 2 ≤
          ∑ a : Fin e, (cPos (s a) - cPos (t a)) ^ 2
      · obtain ⟨b, hb⟩ := ih cPos hcPos hcardPos
        exact ⟨b, hcmp.trans hb⟩
      · have hcmp2 : ∑ a : Fin e, (c (s a) - c (t a)) ^ 2 ≤
            ∑ a : Fin e, (cNeg (s a) - cNeg (t a)) ^ 2 := by linarith
        obtain ⟨b, hb⟩ := ih cNeg hcNeg hcardNeg
        exact ⟨b, hcmp2.trans hb⟩

end NearestKronecker

theorem OMA.solution : type_of% @OMA.S_mo_228115.main := by
  refine ⟨?_, ?_⟩
  · intro ι _ _ n A
    have hleast : ∀ p : Equiv.Perm ι,
        IsLeast (Set.range (fun Q : Orth n ↦ loss A p Q))
          (sizeSq A + (Fintype.card ι : ℝ) * n - 2 * nuclear (blockSum A p)) := by
      intro p
      obtain ⟨⟨Q0, hQ0⟩, hQ_max⟩ := NearestKronecker.isGreatest_score_nuclear (blockSum A p)
      dsimp only at hQ0
      refine ⟨⟨Q0, ?_⟩, ?_⟩
      · dsimp only
        rw [NearestKronecker.loss_eq_expansion, hQ0]
      · rintro _ ⟨Q, rfl⟩
        dsimp only
        rw [NearestKronecker.loss_eq_expansion]
        have hle : score (blockSum A p) Q ≤ nuclear (blockSum A p) := hQ_max ⟨Q, rfl⟩
        linarith
    have hmin_exists : ∃ (p : Equiv.Perm ι) (Q : Orth n), ∀ r U, loss A p Q ≤ loss A r U := by
      obtain ⟨p0, _, hp0_max⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm ι))
          (fun p ↦ nuclear (blockSum A p)) ⟨1, Finset.mem_univ 1⟩
      obtain ⟨⟨Q0, hQ0⟩, _⟩ := NearestKronecker.isGreatest_score_nuclear (blockSum A p0)
      dsimp only at hQ0
      refine ⟨p0, Q0, fun r U ↦ ?_⟩
      have h1 : loss A p0 Q0 = sizeSq A + (Fintype.card ι : ℝ) * n - 2 * nuclear (blockSum A p0) := by
        rw [NearestKronecker.loss_eq_expansion, hQ0]
      have h2 : sizeSq A + (Fintype.card ι : ℝ) * n - 2 * nuclear (blockSum A r) ≤ loss A r U :=
        (hleast r).2 ⟨U, rfl⟩
      have h3 : nuclear (blockSum A r) ≤ nuclear (blockSum A p0) := hp0_max r (Finset.mem_univ r)
      linarith
    refine ⟨hmin_exists, hleast, ?_⟩
    intro p Q
    constructor
    · intro hopt
      obtain ⟨_, hQ_max⟩ := NearestKronecker.isGreatest_score_nuclear (blockSum A p)
      have hle_nuc : score (blockSum A p) Q ≤ nuclear (blockSum A p) := hQ_max ⟨Q, rfl⟩
      have hscore_eq : score (blockSum A p) Q = nuclear (blockSum A p) := by
        obtain ⟨⟨Qp, hQp⟩, _⟩ := NearestKronecker.isGreatest_score_nuclear (blockSum A p)
        dsimp only at hQp
        have hle := hopt p Qp
        rw [NearestKronecker.loss_eq_expansion, NearestKronecker.loss_eq_expansion, hQp] at hle
        linarith
      refine ⟨fun r ↦ ?_, hscore_eq⟩
      obtain ⟨⟨Qr, hQr⟩, _⟩ := NearestKronecker.isGreatest_score_nuclear (blockSum A r)
      dsimp only at hQr
      have hle := hopt r Qr
      rw [NearestKronecker.loss_eq_expansion, NearestKronecker.loss_eq_expansion, hscore_eq, hQr] at hle
      linarith
    · rintro ⟨hp_max, hscore_eq⟩ r U
      have h1 : loss A p Q = sizeSq A + (Fintype.card ι : ℝ) * n - 2 * nuclear (blockSum A p) := by
        rw [NearestKronecker.loss_eq_expansion, hscore_eq]
      have h2 : sizeSq A + (Fintype.card ι : ℝ) * n - 2 * nuclear (blockSum A r) ≤ loss A r U :=
        (hleast r).2 ⟨U, rfl⟩
      have h3 : nuclear (blockSum A r) ≤ nuclear (blockSum A p) := hp_max r
      linarith
  · intro v e s t
    refine ⟨?_, ?_⟩
    · intro i j
      unfold cutInput
      simp only [Matrix.of_apply]
      split_ifs with hcond hflag
      · have hinc : incidence s t i.1.1 i.2 = -1 ∨ incidence s t i.1.1 i.2 = 0 ∨
            incidence s t i.1.1 i.2 = 1 := by
          unfold incidence
          refine Fin.cases (by simp) (fun a ↦ ?_) i.2
          by_cases hs : s a = i.1.1 <;> by_cases ht : t a = i.1.1 <;> simp [hs, ht]
        rcases hinc with h | h | h <;> simp [h]
      · have hinc : incidence s t i.1.1 i.2 = -1 ∨ incidence s t i.1.1 i.2 = 0 ∨
            incidence s t i.1.1 i.2 = 1 := by
          unfold incidence
          refine Fin.cases (by simp) (fun a ↦ ?_) i.2
          by_cases hs : s a = i.1.1 <;> by_cases ht : t a = i.1.1 <;> simp [hs, ht]
        rcases hinc with h | h | h <;> simp [h]
      · exact Or.inr (Or.inl rfl)
    · intro k
      have hblock_col : ∀ (p : Equiv.Perm (Fin v × Bool)),
          (∀ i j : Fin (e + 1), j ≠ 0 → blockSum (cutInput s t) p i j = 0) ∧
          nuclear (blockSum (cutInput s t) p) ^ 2 =
            ∑ a : Fin e,
              ((if (p (s a, false)).1 = s a then (if (p (s a, false)).2 then (-1 : ℝ) else 1) else 0) -
               (if (p (t a, false)).1 = t a then (if (p (t a, false)).2 then (-1 : ℝ) else 1) else 0)) ^ 2 := by
        intro p
        have hzero : ∀ i j : Fin (e + 1), j ≠ 0 → blockSum (cutInput s t) p i j = 0 := by
          intro i j hj
          unfold blockSum cutInput
          simp only [Matrix.of_apply]
          refine Finset.sum_eq_zero fun a _ ↦ ?_
          simp [hj]
        refine ⟨hzero, ?_⟩
        rw [NearestKronecker.nuclear_sq_of_single_col (blockSum (cutInput s t) p) hzero]
        let c : Fin v → ℝ := fun u ↦
          if (p (u, false)).1 = u then (if (p (u, false)).2 then (-1 : ℝ) else 1) else 0
        have hcol0 : ∀ l : Fin (e + 1),
            blockSum (cutInput s t) p l 0 = ∑ u : Fin v, c u * incidence s t u l := by
          intro l
          unfold blockSum cutInput
          simp only [Matrix.of_apply]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          rw [Fintype.sum_bool]
          simp only [Bool.true_eq_false, false_and, ↓reduceIte, zero_add, true_and]
          by_cases h1 : (p (u, false)).1 = u
          · dsimp only [c]; simp [h1]
          · dsimp only [c]; simp [h1, Ne.symm h1]
        rw [Fin.sum_univ_succ]
        have h0 : blockSum (cutInput s t) p 0 0 = 0 := by
          rw [hcol0 0]
          simp [incidence]
        rw [h0, zero_pow (by norm_num), zero_add]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        congr 1
        rw [hcol0 a.succ]
        simp only [incidence, Fin.cases_succ, mul_sub]
        rw [Finset.sum_sub_distrib]
        have hsum_s : ∑ u : Fin v, c u * (if s a = u then (1 : ℝ) else 0) = c (s a) := by
          rw [Finset.sum_eq_single (s a)]
          · simp
          · intro u _ hus; simp [Ne.symm hus]
          · intro h; exact absurd (Finset.mem_univ (s a)) h
        have hsum_t : ∑ u : Fin v, c u * (if t a = u then (1 : ℝ) else 0) = c (t a) := by
          rw [Finset.sum_eq_single (t a)]
          · simp
          · intro u _ hut; simp [Ne.symm hut]
          · intro h; exact absurd (Finset.mem_univ (t a)) h
        rw [hsum_s, hsum_t]
      constructor
      · rintro ⟨p, hp⟩
        rw [(hblock_col p).2] at hp
        let c : Fin v → ℝ := fun u ↦
          if (p (u, false)).1 = u then (if (p (u, false)).2 then (-1 : ℝ) else 1) else 0
        have hc : ∀ u, c u = -1 ∨ c u = 0 ∨ c u = 1 := fun u ↦ by
          dsimp [c]
          split_ifs <;> simp
        obtain ⟨b, hb⟩ :=
          NearestKronecker.exists_bool_cut_ge s t (Fintype.card (Fin v)) c hc
            (Finset.card_le_univ _)
        refine ⟨b, ?_⟩
        have h4 : (4 : ℝ) * (k : ℝ) ≤ 4 * (cut s t b : ℝ) := hp.trans hb
        have hle : (k : ℝ) ≤ (cut s t b : ℝ) := by linarith
        exact_mod_cast hle
      · rintro ⟨b, hb⟩
        let p : Equiv.Perm (Fin v × Bool) :=
          { toFun := fun x ↦ (x.1, xor x.2 (b x.1))
            invFun := fun x ↦ (x.1, xor x.2 (b x.1))
            left_inv := fun ⟨u, f⟩ ↦ by cases f <;> cases h : b u <;> simp [h]
            right_inv := fun ⟨u, f⟩ ↦ by cases f <;> cases h : b u <;> simp [h] }
        refine ⟨p, ?_⟩
        rw [(hblock_col p).2]
        have heval : ∀ u : Fin v,
            (if (p (u, false)).1 = u then (if (p (u, false)).2 then (-1 : ℝ) else 1) else 0) =
              if b u then (-1 : ℝ) else 1 := fun u ↦ by
          cases hbu : b u <;> simp [p, hbu]
        simp_rw [heval]
        have hsum_eq : ∑ a : Fin e,
            ((if b (s a) then (-1 : ℝ) else 1) - (if b (t a) then (-1 : ℝ) else 1)) ^ 2 =
              4 * (cut s t b : ℝ) := by
          unfold cut
          rw [Nat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          cases b (s a) <;> cases b (t a) <;> norm_num
        rw [hsum_eq]
        have hbr : (k : ℝ) ≤ (cut s t b : ℝ) := by exact_mod_cast hb
        linarith
