import OMAStatements.S_mo_492407

open OMA.S_mo_492407 Matrix

namespace MatrixCoordinateFit

lemma froSq_nonneg {m d : ℕ} (U : Mat m d) : 0 ≤ froSq U := by
  unfold froSq
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma froSq_eq_zero_iff {m d : ℕ} (U : Mat m d) : froSq U = 0 ↔ U = 0 := by
  constructor
  · intro h
    ext i j
    unfold froSq at h
    have hi : ∑ j' : Fin d, (U i j') ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i' _ ↦
        Finset.sum_nonneg fun j' _ ↦ sq_nonneg (U i' j')).mp h i (Finset.mem_univ i)
    have hij : (U i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j' _ ↦ sq_nonneg (U i j')).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · rintro rfl
    unfold froSq
    simp

lemma froSq_add_smul {m d : ℕ} (U V : Mat m d) (s : ℝ) :
    froSq (U + s • V) = froSq U + 2 * s * froInner U V + s ^ 2 * froSq V := by
  unfold froSq froInner
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm : ∀ i j, (U i j + s * V i j) ^ 2 =
      (U i j) ^ 2 + 2 * s * (U i j * V i j) + s ^ 2 * (V i j) ^ 2 := fun i j ↦ by ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma froSq_sub_smul {m d : ℕ} (U V : Mat m d) (s : ℝ) :
    froSq (U - s • V) = froSq U - 2 * s * froInner U V + s ^ 2 * froSq V := by
  have h : U - s • V = U + (-s) • V := by ext i j; simp [sub_eq_add_neg]
  rw [h, froSq_add_smul]
  ring

lemma froSq_le_two_mul_sub_add {m d : ℕ} (U V : Mat m d) :
    froSq V ≤ 2 * froSq (U - V) + 2 * froSq U := by
  unfold froSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (2 * U i j - V i j)]

lemma abs_entry_mul_le {m d : ℕ} (L : Mat d m) (W : Mat m d) (i j : Fin d) :
    |(L * W) i j| ≤ (froSq L + froSq W) / 2 := by
  rw [Matrix.mul_apply]
  calc
    |∑ k : Fin m, L i k * W k j|
        ≤ ∑ k : Fin m, |L i k * W k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin m, ((L i k) ^ 2 + (W k j) ^ 2) / 2 := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          rw [abs_mul]
          nlinarith [sq_nonneg (|L i k| - |W k j|), sq_abs (L i k), sq_abs (W k j)]
    _ = (∑ k : Fin m, (L i k) ^ 2 + ∑ k : Fin m, (W k j) ^ 2) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ (froSq L + froSq W) / 2 := by
          have hL : ∑ k : Fin m, (L i k) ^ 2 ≤ froSq L := by
            unfold froSq
            exact Finset.single_le_sum (fun i' _ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg (L i' k))
              (Finset.mem_univ i)
          have hW : ∑ k : Fin m, (W k j) ^ 2 ≤ froSq W := by
            unfold froSq
            refine Finset.sum_le_sum fun k _ ↦ ?_
            exact Finset.single_le_sum (fun j' _ ↦ sq_nonneg (W k j')) (Finset.mem_univ j)
          linarith

lemma rank_eq_one_of_ne_zero {M : Mat 1 2} (hM : M ≠ 0) : M.rank = 1 := by
  have hle : M.rank ≤ 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range M.mulVecLin)
    simpa [Matrix.rank] using h1
  have hpos : 0 < M.rank := by
    have hne : ∃ j : Fin 2, M 0 j ≠ 0 := by
      by_contra hall; push Not at hall
      apply hM
      ext i j
      fin_cases i
      exact hall j
    rcases hne with ⟨j, hj⟩
    have hmem : M.mulVecLin (Pi.single j 1) ∈ LinearMap.range M.mulVecLin := ⟨Pi.single j 1, rfl⟩
    have hvne : M.mulVecLin (Pi.single j 1) ≠ 0 := by
      intro hz
      have h0 := congr_fun hz 0
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Pi.zero_apply] at h0
      fin_cases j <;> simp at h0 <;> exact hj h0
    have hne_bot : LinearMap.range M.mulVecLin ≠ ⊥ := fun hbot ↦ by
      rw [hbot, Submodule.mem_bot] at hmem
      exact hvne hmem
    exact Nat.pos_of_ne_zero fun h0 ↦ hne_bot (Submodule.finrank_eq_zero.mp h0)
  omega

lemma part1 :
    ∃ X₁ X₂ Y₁ Y₂ : Mat 1 2, X₁.rank = 1 ∧ X₂.rank = 1 ∧ Y₁.rank = 1 ∧ Y₂.rank = 1 ∧
      (∀ A B, inversePair A B → 0 < loss X₁ X₂ Y₁ Y₂ A B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A B, inversePair A B ∧ loss X₁ X₂ Y₁ Y₂ A B < ε := by
  let X₁ : Mat 1 2 := ![![1, 0]]
  let X₂ : Mat 1 2 := ![![1, 0]]
  let Y₁ : Mat 1 2 := ![![0, 1]]
  let Y₂ : Mat 1 2 := ![![1, 0]]
  have hX₁ : X₁.rank = 1 := rank_eq_one_of_ne_zero fun h ↦ by
    have h0 := congr_fun (congr_fun h 0) 0; simp [X₁] at h0
  have hX₂ : X₂.rank = 1 := hX₁
  have hY₁ : Y₁.rank = 1 := rank_eq_one_of_ne_zero fun h ↦ by
    have h0 := congr_fun (congr_fun h 0) 1; simp [Y₁] at h0
  have hY₂ : Y₂.rank = 1 := hX₁
  refine ⟨X₁, X₂, Y₁, Y₂, hX₁, hX₂, hY₁, hY₂, ?_, ?_⟩
  · intro A B hAB
    have hnn : 0 ≤ loss X₁ X₂ Y₁ Y₂ A B := by
      unfold loss
      linarith [froSq_nonneg (X₁ - X₂ * A), froSq_nonneg (Y₁ - Y₂ * B)]
    refine lt_of_le_of_ne hnn fun h0 ↦ ?_
    have hsum0 : froSq (X₁ - X₂ * A) + froSq (Y₁ - Y₂ * B) = 0 := by
      unfold loss at h0; linarith
    have hf1 : froSq (X₁ - X₂ * A) = 0 := by
      linarith [froSq_nonneg (X₁ - X₂ * A), froSq_nonneg (Y₁ - Y₂ * B)]
    have hf2 : froSq (Y₁ - Y₂ * B) = 0 := by
      linarith [froSq_nonneg (X₁ - X₂ * A), froSq_nonneg (Y₁ - Y₂ * B)]
    have hAeq : X₁ - X₂ * A = 0 := (froSq_eq_zero_iff _).mp hf1
    have hBeq : Y₁ - Y₂ * B = 0 := (froSq_eq_zero_iff _).mp hf2
    have hA00 : A 0 0 = 1 := by
      have h := congr_fun (congr_fun hAeq 0) 0
      rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
      simp [X₁, X₂] at h
      linarith
    have hA01 : A 0 1 = 0 := by
      have h := congr_fun (congr_fun hAeq 0) 1
      rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
      simp [X₁, X₂] at h
      linarith
    have hB00 : B 0 0 = 0 := by
      have h := congr_fun (congr_fun hBeq 0) 0
      rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at h
      simp [Y₁, Y₂] at h
      linarith
    have hAB00 : (A * B) 0 0 = 1 := by
      have h := congr_fun (congr_fun hAB.1 0) 0
      simpa using h
    rw [Matrix.mul_apply, Fin.sum_univ_two, hA00, hA01, hB00] at hAB00
    norm_num at hAB00
  · intro ε hε
    let δ : ℝ := Real.sqrt ε
    have hδpos : 0 < δ := Real.sqrt_pos.mpr hε
    have hδne : δ ≠ 0 := hδpos.ne'
    let A : Mat 2 2 := ![![1, δ], ![1, 0]]
    let B : Mat 2 2 := ![![0, 1], ![1 / δ, -1 / δ]]
    refine ⟨A, B, ⟨?_, ?_⟩, ?_⟩
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j
      · simp [A, B]; field_simp [hδne]
      · simp [A, B]; field_simp [hδne]; ring
      · simp [A, B]
      · simp [A, B]
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j
      · simp [A, B]
      · simp [A, B]
      · simp [A, B]; field_simp [hδne]; ring
      · simp [A, B]; field_simp [hδne]
    · unfold loss froSq
      simp only [Fin.sum_univ_one, Fin.sum_univ_two]
      have h10 : (X₁ - X₂ * A) 0 0 = 0 := by
        rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; simp [X₁, X₂, A]
      have h11 : (X₁ - X₂ * A) 0 1 = -δ := by
        rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; simp [X₁, X₂, A]
      have h20 : (Y₁ - Y₂ * B) 0 0 = 0 := by
        rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; simp [Y₁, Y₂, B]
      have h21 : (Y₁ - Y₂ * B) 0 1 = 0 := by
        rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; simp [Y₁, Y₂, B]
      rw [h10, h11, h20, h21]
      have hsq : δ ^ 2 = ε := Real.sq_sqrt hε.le
      nlinarith

lemma continuous_entry_mat {m d : ℕ} (i : Fin m) (j : Fin d) :
    Continuous fun M : Mat m d ↦ M i j :=
  (continuous_apply j).comp (continuous_apply i)

lemma continuous_mul_mat {d : ℕ} : Continuous fun p : Mat d d × Mat d d ↦ p.1 * p.2 := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  simp only [Matrix.mul_apply]
  refine continuous_finsetSum _ fun k _ ↦ ?_
  have h1 : Continuous fun p : Mat d d × Mat d d ↦ p.1 i k :=
    (continuous_entry_mat i k).comp continuous_fst
  have h2 : Continuous fun p : Mat d d × Mat d d ↦ p.2 k j :=
    (continuous_entry_mat k j).comp continuous_snd
  exact h1.mul h2

lemma continuous_froSq {m d : ℕ} : Continuous (froSq : Mat m d → ℝ) := by
  unfold froSq
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
  exact (continuous_entry_mat i j).pow 2

lemma continuous_loss {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d) :
    Continuous fun p : Mat d d × Mat d d ↦ loss X₁ X₂ Y₁ Y₂ p.1 p.2 := by
  unfold loss
  have h1 : Continuous fun A : Mat d d ↦ X₁ - X₂ * A := by
    refine continuous_const.sub (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_)
    simp only [Matrix.mul_apply]
    refine continuous_finsetSum _ fun k _ ↦
      continuous_const.mul (continuous_entry_mat k j)
  have h2 : Continuous fun B : Mat d d ↦ Y₁ - Y₂ * B := by
    refine continuous_const.sub (continuous_pi fun i ↦ continuous_pi fun j ↦ ?_)
    simp only [Matrix.mul_apply]
    refine continuous_finsetSum _ fun k _ ↦
      continuous_const.mul (continuous_entry_mat k j)
  exact ((continuous_froSq.comp (h1.comp continuous_fst)).add
    (continuous_froSq.comp (h2.comp continuous_snd))).div_const 2

lemma exists_optimal {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    (hX₂ : ∃ L : Mat d m, L * X₂ = 1) (hY₂ : ∃ L : Mat d n, L * Y₂ = 1) :
    ∃ A B, optimal X₁ X₂ Y₁ Y₂ A B := by
  rcases hX₂ with ⟨L₁, hL₁⟩
  rcases hY₂ with ⟨L₂, hL₂⟩
  let c0 : ℝ := loss X₁ X₂ Y₁ Y₂ (1 : Mat d d) (1 : Mat d d)
  let S : Set (Mat d d × Mat d d) :=
    {p | inversePair p.1 p.2 ∧ loss X₁ X₂ Y₁ Y₂ p.1 p.2 ≤ c0}
  have hS_ne : S.Nonempty := ⟨(1, 1), ⟨⟨mul_one 1, mul_one 1⟩, le_rfl⟩⟩
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {p : Mat d d × Mat d d | p.1 * p.2 = 1} :=
      isClosed_eq continuous_mul_mat continuous_const
    have h2 : IsClosed {p : Mat d d × Mat d d | p.2 * p.1 = 1} :=
      isClosed_eq (continuous_mul_mat.comp continuous_swap) continuous_const
    have h3 : IsClosed {p : Mat d d × Mat d d | loss X₁ X₂ Y₁ Y₂ p.1 p.2 ≤ c0} :=
      isClosed_le (continuous_loss X₁ X₂ Y₁ Y₂) continuous_const
    exact (h1.inter h2).inter h3
  let R : ℝ := (froSq L₁ + froSq L₂ + 4 * c0 + 2 * froSq X₁ + 2 * froSq Y₁) / 2
  let box0 : Set (Fin d → Fin d → ℝ) :=
    Set.pi Set.univ fun _ : Fin d ↦ Set.pi Set.univ fun _ : Fin d ↦ (Set.Icc (-R) R : Set ℝ)
  have hbox0_compact : IsCompact box0 :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hof_cont : Continuous (Matrix.of : (Fin d → Fin d → ℝ) → Mat d d) :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ (continuous_apply j).comp (continuous_apply i)
  let box : Set (Mat d d) := Matrix.of '' box0
  have hbox_compact : IsCompact box := hbox0_compact.image hof_cont
  have hK_compact : IsCompact (box ×ˢ box) := hbox_compact.prod hbox_compact
  have hS_sub : S ⊆ box ×ˢ box := by
    rintro ⟨A, B⟩ ⟨_, hle⟩
    have hf1 : froSq (X₁ - X₂ * A) ≤ 2 * c0 := by
      unfold loss at hle
      linarith [froSq_nonneg (Y₁ - Y₂ * B)]
    have hf2 : froSq (Y₁ - Y₂ * B) ≤ 2 * c0 := by
      unfold loss at hle
      linarith [froSq_nonneg (X₁ - X₂ * A)]
    have hX₂A : froSq (X₂ * A) ≤ 4 * c0 + 2 * froSq X₁ := by
      linarith [froSq_le_two_mul_sub_add X₁ (X₂ * A)]
    have hY₂B : froSq (Y₂ * B) ≤ 4 * c0 + 2 * froSq Y₁ := by
      linarith [froSq_le_two_mul_sub_add Y₁ (Y₂ * B)]
    have hA_eq : A = L₁ * (X₂ * A) := by rw [← Matrix.mul_assoc, hL₁, Matrix.one_mul]
    have hB_eq : B = L₂ * (Y₂ * B) := by rw [← Matrix.mul_assoc, hL₂, Matrix.one_mul]
    refine ⟨⟨fun i j ↦ A i j, fun i _ j _ ↦ ?_, rfl⟩, ⟨fun i j ↦ B i j, fun i _ j _ ↦ ?_, rfl⟩⟩
    · have habs : |A i j| ≤ R := by
        rw [hA_eq]
        have h := abs_entry_mul_le L₁ (X₂ * A) i j
        dsimp [R]
        linarith [froSq_nonneg L₂, froSq_nonneg Y₁]
      exact abs_le.mp habs
    · have habs : |B i j| ≤ R := by
        rw [hB_eq]
        have h := abs_entry_mul_le L₂ (Y₂ * B) i j
        dsimp [R]
        linarith [froSq_nonneg L₁, froSq_nonneg X₁]
      exact abs_le.mp habs
  have hS_compact : IsCompact S := hK_compact.of_isClosed_subset hS_closed hS_sub
  obtain ⟨⟨A, B⟩, hAB_mem, hAB_min⟩ :=
    hS_compact.exists_isMinOn hS_ne (continuous_loss X₁ X₂ Y₁ Y₂).continuousOn
  refine ⟨A, B, hAB_mem.1, fun U V hUV ↦ ?_⟩
  by_cases hle : loss X₁ X₂ Y₁ Y₂ U V ≤ c0
  · exact isMinOn_iff.mp hAB_min (U, V) ⟨hUV, hle⟩
  · push Not at hle
    exact hAB_mem.2.trans hle.le

lemma single_mul_single_eq {d : ℕ} (i j : Fin d) :
    Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) =
      if i = j then Matrix.single i j (1 : ℝ) else 0 := by
  ext a b
  rw [Matrix.mul_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · by_cases ha : i = a <;> by_cases hb : i = b <;> simp [Matrix.single, ha, hb]
    · intro k _ hk; simp [Matrix.single, hk.symm]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases h1 : k = j
    · subst h1; simp [Matrix.single, h]
    · simp [Matrix.single, Ne.symm h1]

lemma eq_of_linear_quad_bound {b e M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, |t| ≤ 1 / 2 → 2 * t * (b - e) ≤ M * t ^ 2) : b = e := by
  by_contra hne
  let d : ℝ := b - e
  have hdne : d ≠ 0 := sub_ne_zero.mpr hne
  have hdabs : 0 < |d| := abs_pos.mpr hdne
  let D : ℝ := M + 2 * |d| + 1
  have hDpos : 0 < D := by dsimp [D]; linarith
  let t : ℝ := d / D
  have ht_abs : |t| ≤ 1 / 2 := by
    dsimp [t]
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    dsimp [D]
    linarith
  have hineq := h t ht_abs
  have hMt : M * t ^ 2 < D * t ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero (div_ne_zero hdne hDpos.ne')
    have hMD : M < D := by dsimp [D]; linarith
    nlinarith
  have hDt : D * t ^ 2 = t * d := by
    dsimp [t]; field_simp [hDpos.ne']
  have htd : 0 < t * d := by
    dsimp [t]
    have hsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
    have : d / D * d = d ^ 2 / D := by ring
    rw [this]
    exact div_pos hsq hDpos
  have : 2 * t * d ≤ M * t ^ 2 := hineq
  linarith

lemma critical_of_optimal {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    {A B : Mat d d} (hopt : optimal X₁ X₂ Y₁ Y₂ A B) :
    critical X₁ X₂ Y₁ Y₂ A B := by
  refine ⟨hopt.1, fun i j ↦ ?_⟩
  let E : Mat d d := Matrix.single i j (1 : ℝ)
  let U : Mat m d := X₁ - X₂ * A
  let V : Mat m d := (X₂ * A) * E
  let P : Mat n d := Y₁ - Y₂ * B
  let Q : Mat n d := (Y₂ * E) * B
  by_cases hij : i = j
  · have hE2 : E * E = E := by dsimp [E]; rw [single_mul_single_eq, if_pos hij]
    let M : ℝ := 5 * |froInner U V| + 4 * froSq V + 2 * |froInner P Q| + froSq Q + 1
    have hM_nn : 0 ≤ M := by
      dsimp [M]
      linarith [abs_nonneg (froInner U V), froSq_nonneg V, abs_nonneg (froInner P Q),
        froSq_nonneg Q]
    refine eq_of_linear_quad_bound hM_nn fun t ht ↦ ?_
    have ht_lo : -(1 / 2 : ℝ) ≤ t := (abs_le.mp ht).1
    have ht_hi : t ≤ 1 / 2 := (abs_le.mp ht).2
    have ht1_pos : 0 < 1 + t := by linarith
    have ht1_ne : 1 + t ≠ 0 := ht1_pos.ne'
    let s : ℝ := t / (1 + t)
    let L : Mat d d := 1 + t • E
    let R : Mat d d := 1 - s • E
    have hLR : L * R = 1 := by
      dsimp [L, R]
      have h1 : (1 + t • E) * (1 - s • E) = 1 + (t - s - t * s) • E := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, hE2]
        ext a b; simp; ring
      have hcoeff : t - s - t * s = 0 := by dsimp [s]; field_simp [ht1_ne]; ring
      rw [h1, hcoeff, zero_smul, add_zero]
    have hRL : R * L = 1 := by
      dsimp [L, R]
      have h1 : (1 - s • E) * (1 + t • E) = 1 + (t - s - s * t) • E := by
        simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, hE2]
        ext a b; simp; ring
      have hcoeff : t - s - s * t = 0 := by dsimp [s]; field_simp [ht1_ne]; ring
      rw [h1, hcoeff, zero_smul, add_zero]
    have hinv : inversePair (A * L) (R * B) := by
      refine ⟨?_, ?_⟩
      · calc
          A * L * (R * B) = A * (L * R) * B := by simp only [Matrix.mul_assoc]
          _ = A * B := by rw [hLR, Matrix.mul_one]
          _ = 1 := hopt.1.1
      · calc
          R * B * (A * L) = R * (B * A) * L := by simp only [Matrix.mul_assoc]
          _ = R * L := by rw [hopt.1.2, Matrix.mul_one]
          _ = 1 := hRL
    have hXeq : X₁ - X₂ * (A * L) = U - t • V := by
      dsimp [U, V, L]
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.mul_assoc, sub_add_eq_sub_sub]
    have hYeq : Y₁ - Y₂ * (R * B) = P + s • Q := by
      dsimp [P, Q, R]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_assoc]
      ext a b; simp; ring
    have hle := hopt.2 (A * L) (R * B) hinv
    unfold loss at hle
    rw [hXeq, hYeq, froSq_sub_smul, froSq_add_smul] at hle
    have hdiff : 0 ≤ -2 * t * froInner U V + t ^ 2 * froSq V +
        2 * s * froInner P Q + s ^ 2 * froSq Q := by
      dsimp [U, P] at hle ⊢
      linarith
    have hmul : 0 ≤ (-2 * t * froInner U V + t ^ 2 * froSq V +
        2 * s * froInner P Q + s ^ 2 * froSq Q) * (1 + t) ^ 2 :=
      mul_nonneg hdiff (sq_nonneg (1 + t))
    have hexp : (-2 * t * froInner U V + t ^ 2 * froSq V +
        2 * s * froInner P Q + s ^ 2 * froSq Q) * (1 + t) ^ 2 =
        2 * t * (froInner P Q - froInner U V) +
        t ^ 2 * ((-4 - 2 * t) * froInner U V + (1 + t) ^ 2 * froSq V +
          2 * froInner P Q + froSq Q) := by
      dsimp [s]; field_simp [ht1_ne]; ring
    rw [hexp] at hmul
    have hcoef_le : (-4 - 2 * t) * froInner U V + (1 + t) ^ 2 * froSq V +
        2 * froInner P Q + froSq Q ≤ M := by
      have h1 : (-4 - 2 * t) * froInner U V ≤ 5 * |froInner U V| := by
        have hab : |(-4 - 2 * t) * froInner U V| = |-4 - 2 * t| * |froInner U V| := abs_mul _ _
        have hlin : |-4 - 2 * t| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hle1 : (-4 - 2 * t) * froInner U V ≤ |(-4 - 2 * t) * froInner U V| := le_abs_self _
        nlinarith [abs_nonneg (froInner U V)]
      have h2 : (1 + t) ^ 2 * froSq V ≤ 4 * froSq V := by
        have hsq : (1 + t) ^ 2 ≤ 4 := by nlinarith
        nlinarith [froSq_nonneg V]
      have h3 : 2 * froInner P Q ≤ 2 * |froInner P Q| := by linarith [le_abs_self (froInner P Q)]
      dsimp [M]
      linarith
    nlinarith [sq_nonneg t]
  · have hE2 : E * E = 0 := by dsimp [E]; rw [single_mul_single_eq, if_neg hij]
    let M : ℝ := froSq V + froSq Q
    have hM_nn : 0 ≤ M := by dsimp [M]; linarith [froSq_nonneg V, froSq_nonneg Q]
    refine eq_of_linear_quad_bound hM_nn fun t _ ↦ ?_
    let L : Mat d d := 1 + t • E
    let R : Mat d d := 1 - t • E
    have hLR : L * R = 1 := by
      dsimp [L, R]
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hE2, smul_zero]
      ext a b; simp
    have hRL : R * L = 1 := by
      dsimp [L, R]
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hE2, smul_zero]
      ext a b; simp
    have hinv : inversePair (A * L) (R * B) := by
      refine ⟨?_, ?_⟩
      · calc
          A * L * (R * B) = A * (L * R) * B := by simp only [Matrix.mul_assoc]
          _ = A * B := by rw [hLR, Matrix.mul_one]
          _ = 1 := hopt.1.1
      · calc
          R * B * (A * L) = R * (B * A) * L := by simp only [Matrix.mul_assoc]
          _ = R * L := by rw [hopt.1.2, Matrix.mul_one]
          _ = 1 := hRL
    have hXeq : X₁ - X₂ * (A * L) = U - t • V := by
      dsimp [U, V, L]
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul,
        Matrix.mul_assoc, sub_add_eq_sub_sub]
    have hYeq : Y₁ - Y₂ * (R * B) = P + t • Q := by
      dsimp [P, Q, R]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
        Matrix.mul_assoc]
      ext a b; simp; ring
    have hle := hopt.2 (A * L) (R * B) hinv
    unfold loss at hle
    rw [hXeq, hYeq, froSq_sub_smul, froSq_add_smul] at hle
    dsimp [U, P, M] at hle ⊢
    linarith

lemma part2 {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    (hX₂ : ∃ L : Mat d m, L * X₂ = 1) (hY₂ : ∃ L : Mat d n, L * Y₂ = 1) :
    (∃ A B, optimal X₁ X₂ Y₁ Y₂ A B) ∧
      ∀ A B, optimal X₁ X₂ Y₁ Y₂ A B ↔ critical X₁ X₂ Y₁ Y₂ A B ∧
        ∀ U V, critical X₁ X₂ Y₁ Y₂ U V → loss X₁ X₂ Y₁ Y₂ A B ≤ loss X₁ X₂ Y₁ Y₂ U V := by
  have hex : ∃ A B, optimal X₁ X₂ Y₁ Y₂ A B := exists_optimal X₁ X₂ Y₁ Y₂ hX₂ hY₂
  refine ⟨hex, fun A B ↦ ⟨fun hopt ↦ ⟨critical_of_optimal X₁ X₂ Y₁ Y₂ hopt,
    fun U V hcrit ↦ hopt.2 U V hcrit.1⟩, fun ⟨hcrit, hmin⟩ ↦ ?_⟩⟩
  rcases hex with ⟨A₀, B₀, hopt₀⟩
  have hcrit₀ : critical X₁ X₂ Y₁ Y₂ A₀ B₀ := critical_of_optimal X₁ X₂ Y₁ Y₂ hopt₀
  exact ⟨hcrit.1, fun U V hUV ↦ (hmin A₀ B₀ hcrit₀).trans (hopt₀.2 U V hUV)⟩

lemma part3 :
    ∃ a : ℝ, a ^ 2 = 1 ∧ (∀ b : ℝ, b ^ 2 = 1 → scalarOrthogonalLoss a ≤ scalarOrthogonalLoss b) ∧
      1 * a + a * 1 ≠ 1 * 2 + 2 * 1 := by
  refine ⟨1, by norm_num, fun b hb ↦ ?_, by norm_num⟩
  have hcase : b = 1 ∨ b = -1 := by
    have hfac : (b - 1) * (b + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left; linarith
    · right; linarith
  rcases hcase with rfl | rfl <;> unfold scalarOrthogonalLoss <;> norm_num

end MatrixCoordinateFit

theorem OMA.solution : type_of% @OMA.S_mo_492407.main :=
  ⟨MatrixCoordinateFit.part1,
   fun X₁ X₂ Y₁ Y₂ hX₂ hY₂ ↦ MatrixCoordinateFit.part2 X₁ X₂ Y₁ Y₂ hX₂ hY₂,
   MatrixCoordinateFit.part3⟩
