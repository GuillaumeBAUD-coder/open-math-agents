import OMAStatements.S_mo_243037

-- Problem: Measures on a unit sphere of a Hilbert space
-- Upstream: statements/mo-243037.lean (declaration OMA.S_mo_243037.main)
-- Credit: @FrancoisCharroin
-- Counting measure invariance, non-existence of non-zero finite-on-open invariant measures via
-- Householder transitivity and infinite packing of disjoint balls, and antipodal line law.

namespace OMA.Mo243037

open MeasureTheory Metric Set OMA.S_mo_243037
open scoped ENNReal

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma act_continuous (e : H ≃ₗᵢ[ℝ] H) : Continuous (act e) :=
  Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _

lemma act_measurable [MeasurableSpace H] [BorelSpace H] (e : H ≃ₗᵢ[ℝ] H) :
    Measurable (act e) :=
  (act_continuous e).measurable

lemma act_bijective (e : H ≃ₗᵢ[ℝ] H) : Function.Bijective (act e) := by
  refine ⟨fun x y h => ?_, fun y => ⟨act e.symm y, ?_⟩⟩
  · ext
    exact e.injective (congrArg Subtype.val h)
  · ext
    simp [act]

lemma act_isometry (e : H ≃ₗᵢ[ℝ] H) : Isometry (act e) := by
  intro x y
  change edist (e x.val) (e y.val) = edist x.val y.val
  exact e.isometry x.val y.val

lemma act_preimage_ball (e : H ≃ₗᵢ[ℝ] H) (x y : S H) (hxy : act e x = y) (r : ℝ) :
    act e ⁻¹' ball y r = ball x r := by
  ext z
  simp only [mem_preimage, mem_ball]
  rw [← hxy, (act_isometry e).dist_eq z x]

lemma act_antipode (e : H ≃ₗᵢ[ℝ] H) (x : S H) : act e (antipode x) = antipode (act e x) := by
  ext
  simp [act, antipode]

lemma antipode_antipode (x : S H) : antipode (antipode x) = x := by
  ext
  simp [antipode]

noncomputable def householder (v : H) (hv : v ≠ 0) : H ≃ₗᵢ[ℝ] H := by
  let f : H →ₗ[ℝ] H :=
    { toFun := fun z => z - (2 * inner ℝ v z / ‖v‖ ^ 2) • v
      map_add' := fun x y => by
        rw [inner_add_right, mul_add, add_div, add_smul]
        abel
      map_smul' := fun c x => by
        rw [inner_smul_right, RingHom.id_apply, smul_sub, smul_smul]
        congr 2
        ring }
  have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have hf_apply : ∀ z : H, f z = z - (2 * inner ℝ v z / ‖v‖ ^ 2) • v := fun _ => rfl
  have hinv : ∀ z : H, f (f z) = z := by
    intro z
    have hinner : inner ℝ v (f z) = -inner ℝ v z := by
      rw [hf_apply, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hv2]
      ring
    rw [hf_apply, hinner, hf_apply]
    have hcoeff : 2 * -inner ℝ v z / ‖v‖ ^ 2 = -(2 * inner ℝ v z / ‖v‖ ^ 2) := by ring
    rw [hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]
  have hnorm : ∀ z : H, ‖f z‖ = ‖z‖ := by
    intro z
    have hsq : ‖f z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [hf_apply, norm_sub_sq_real, inner_smul_right, real_inner_comm z v, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp [hv2]
      ring
    nlinarith [norm_nonneg (f z), norm_nonneg z]
  exact
    { toLinearEquiv :=
        { toLinearMap := f
          invFun := f
          left_inv := hinv
          right_inv := hinv }
      norm_map' := hnorm }

lemma exists_isometry_sending (x y : S H) : ∃ e : H ≃ₗᵢ[ℝ] H, act e x = y := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨LinearIsometryEquiv.refl ℝ H, by ext; rfl⟩
  · have hv : x.val - y.val ≠ 0 := by
      intro h0
      apply hxy
      ext
      exact sub_eq_zero.mp h0
    refine ⟨householder (x.val - y.val) hv, ?_⟩
    ext
    have hx1 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    have hy1 : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    have hnum : 2 * inner ℝ (x.val - y.val) x.val = ‖x.val - y.val‖ ^ 2 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm y.val x.val,
        hx1, hy1]
      ring
    have hv2 : ‖x.val - y.val‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    change x.val - (2 * inner ℝ (x.val - y.val) x.val / ‖x.val - y.val‖ ^ 2) • (x.val - y.val) =
      y.val
    rw [hnum, div_self hv2, one_smul, sub_sub_cancel]

lemma count_invariant [MeasurableSpace H] [BorelSpace H] (e : H ≃ₗᵢ[ℝ] H) :
    (Measure.count : Measure (S H)).map (act e) = Measure.count := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (act_measurable e) hs, Measure.count_apply (act_measurable e hs),
    Measure.count_apply hs]
  let eqv : (act e ⁻¹' s) ≃ s :=
    { toFun := fun z => ⟨act e z.val, z.property⟩
      invFun := fun z => ⟨act e.symm z.val, by
        change act e (act e.symm z.val) ∈ s
        have h : act e (act e.symm z.val) = z.val := by ext; simp [act]
        rw [h]
        exact z.property⟩
      left_inv := fun z => by ext; simp [act]
      right_inv := fun z => by ext; simp [act] }
  exact congrArg ENat.toENNReal (Set.encard_congr eqv)

lemma lineLaw_prob [MeasurableSpace H] [BorelSpace H] (x : S H) :
    IsProbabilityMeasure (lineLaw x) := by
  refine ⟨?_⟩
  simp only [lineLaw, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    indicator_univ, Pi.one_apply, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma lineLaw_invariant [MeasurableSpace H] [BorelSpace H] (x : S H) (e : H ≃ₗᵢ[ℝ] H)
    (he : act e x = x ∨ act e x = antipode x) :
    (lineLaw x).map (act e) = lineLaw x := by
  have hm : Measurable (act e) := act_measurable e
  rw [lineLaw, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm, act_antipode]
  rcases he with h | h
  · rw [h]
  · rw [h, antipode_antipode, add_comm]

lemma exists_unit_orth_of_finset [CompleteSpace H] (hinf : ¬ FiniteDimensional ℝ H)
    (F : Finset H) : ∃ u : H, ‖u‖ = 1 ∧ ∀ w ∈ F, inner ℝ w u = 0 := by
  let K : Submodule ℝ H := Submodule.span ℝ (F : Set H)
  have hKfd : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ F.finite_toSet
  have hKcomp : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hKne : K ≠ ⊤ := by
    intro htop
    apply hinf
    have heq : (⊤ : Submodule ℝ H) ≃ₗ[ℝ] H := Submodule.topEquiv
    have htopfd : FiniteDimensional ℝ (⊤ : Submodule ℝ H) := by rwa [← htop]
    exact LinearEquiv.finiteDimensional heq
  have hKorth_ne : Kᗮ ≠ ⊥ := by
    intro hbot
    apply hKne
    have hcl : IsClosed (K : Set H) := Submodule.closed_of_finiteDimensional K
    have := Submodule.orthogonal_orthogonal K
    rw [hbot, Submodule.bot_orthogonal_eq_top] at this
    exact this.symm
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKorth_ne
  refine ⟨(‖v‖⁻¹) • v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · intro w hw
    rw [inner_smul_right, hvK w (Submodule.subset_span hw), mul_zero]

lemma exists_orth_seq [CompleteSpace H] (hinf : ¬ FiniteDimensional ℝ H) (x₀ : S H) :
    ∃ seq : ℕ → H, (∀ n, ‖seq n‖ = 1) ∧ (∀ n, inner ℝ x₀.val (seq n) = 0) ∧
      ∀ i j, i ≠ j → inner ℝ (seq i) (seq j) = 0 := by
  have step : ∀ (n : ℕ) (prev : Fin n → H),
      ∃ u : H, ‖u‖ = 1 ∧ inner ℝ x₀.val u = 0 ∧ ∀ i : Fin n, inner ℝ (prev i) u = 0 := by
    intro n prev
    classical
    let F : Finset H := insert x₀.val (Finset.univ.image prev)
    obtain ⟨u, hu1, huorth⟩ := exists_unit_orth_of_finset hinf F
    refine ⟨u, hu1, huorth x₀.val (Finset.mem_insert_self _ _), fun i => ?_⟩
    exact huorth (prev i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem prev (Finset.mem_univ i)))
  let next : ∀ n : ℕ, (Fin n → H) → H := fun n prev => Classical.choose (step n prev)
  have hnext : ∀ (n : ℕ) (prev : Fin n → H),
      ‖next n prev‖ = 1 ∧ inner ℝ x₀.val (next n prev) = 0 ∧
        ∀ i : Fin n, inner ℝ (prev i) (next n prev) = 0 :=
    fun n prev => Classical.choose_spec (step n prev)
  let pref : ∀ n : ℕ, Fin n → H :=
    Nat.rec Fin.elim0 (fun n f => Fin.snoc (α := fun _ => H) f (next n f))
  have hpref_succ_cast : ∀ (n : ℕ) (i : Fin n), pref (n + 1) i.castSucc = pref n i :=
    fun n i => Fin.snoc_castSucc (α := fun _ => H) (next n (pref n)) (pref n) i
  have hpref_succ_last : ∀ n : ℕ, pref (n + 1) (Fin.last n) = next n (pref n) :=
    fun n => Fin.snoc_last (α := fun _ => H) (next n (pref n)) (pref n)
  have hagree : ∀ (n m : ℕ) (hn : n < m),
      pref m ⟨n, hn⟩ = pref (n + 1) (Fin.last n) := by
    intro n m hn
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hnm : n = m
      · subst hnm; rfl
      · have hlt : n < m := by omega
        have heq : (⟨n, hn⟩ : Fin (m + 1)) = (⟨n, hlt⟩ : Fin m).castSucc := rfl
        rw [heq, hpref_succ_cast m ⟨n, hlt⟩, ih hlt]
  let seq : ℕ → H := fun n => pref (n + 1) (Fin.last n)
  refine ⟨seq, ?_, ?_, ?_⟩
  · intro n
    dsimp only [seq]
    rw [hpref_succ_last]
    exact (hnext n (pref n)).1
  · intro n
    dsimp only [seq]
    rw [hpref_succ_last]
    exact (hnext n (pref n)).2.1
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · dsimp only [seq]
      rw [← hagree i j hlt, hpref_succ_last j]
      exact (hnext j (pref j)).2.2 ⟨i, hlt⟩
    · rw [real_inner_comm]
      dsimp only [seq]
      rw [← hagree j i hgt, hpref_succ_last i]
      exact (hnext i (pref i)).2.2 ⟨j, hgt⟩

lemma invariant_open_eq_top [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    [MeasurableSpace H] [BorelSpace H] (hinf : ¬ FiniteDimensional ℝ H)
    (μ : Measure (S H)) (hμ0 : μ ≠ 0) (hinv : ∀ e : H ≃ₗᵢ[ℝ] H, μ.map (act e) = μ)
    (U : Set (S H)) (hUopen : IsOpen U) (hUne : U.Nonempty) : μ U = ⊤ := by
  have hball_eq : ∀ (x y : S H) (r : ℝ), μ (ball x r) = μ (ball y r) := by
    intro x y r
    obtain ⟨e, he⟩ := exists_isometry_sending x y
    have h1 := hinv e
    have hmeas : MeasurableSet (ball y r) := isOpen_ball.measurableSet
    have h2 : μ (ball y r) = μ (act e ⁻¹' ball y r) := by
      calc
        μ (ball y r) = (μ.map (act e)) (ball y r) := by rw [h1]
        _ = μ (act e ⁻¹' ball y r) := Measure.map_apply (act_measurable e) hmeas
    rw [h2, act_preimage_ball e x y he r]
  have hball_pos : ∀ (x : S H) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 := by
    intro x r hr hzero
    obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (S H)
    have huniv : (Set.univ : Set (S H)) = ⋃ d ∈ D, ball d r := by
      ext y
      simp only [mem_univ, mem_iUnion, mem_ball, true_iff]
      obtain ⟨d, hdD, hdy⟩ := Metric.mem_closure_iff.mp (hDdense y) r hr
      exact ⟨d, hdD, hdy⟩
    have hnull : μ (Set.univ : Set (S H)) = 0 := by
      rw [huniv, measure_biUnion_null_iff hDcount]
      intro d _
      rw [hball_eq d x r, hzero]
    exact hμ0 (Measure.measure_univ_eq_zero.mp hnull)
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hUopen x₀ hx₀
  obtain ⟨seq, hseq_norm, hseq_x0, hseq_orth⟩ := exists_orth_seq hinf x₀
  let t : ℝ := min (ε / 4) (1 / 2)
  have htpos : 0 < t := lt_min (by linarith) (by norm_num)
  have htle1 : t ≤ 1 / 2 := min_le_right _ _
  have htleε : t ≤ ε / 4 := min_le_left _ _
  have h1t2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hx0_norm : ‖x₀.val‖ = 1 := mem_sphere_zero_iff_norm.mp x₀.property
  let z : ℕ → S H := fun k =>
    ⟨Real.sqrt (1 - t ^ 2) • x₀.val + t • seq k, by
      rw [mem_sphere_zero_iff_norm]
      have hsq : ‖Real.sqrt (1 - t ^ 2) • x₀.val + t • seq k‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, inner_smul_left, inner_smul_right, hseq_x0 k, norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
          Real.sq_sqrt h1t2, hx0_norm, hseq_norm k]
        ring
      nlinarith [norm_nonneg (Real.sqrt (1 - t ^ 2) • x₀.val + t • seq k)]⟩
  have hz_dist : ∀ k : ℕ, dist (z k) x₀ ≤ 2 * t := by
    intro k
    have hsub : (z k).val - x₀.val = (Real.sqrt (1 - t ^ 2) - 1) • x₀.val + t • seq k := by
      dsimp only [z]
      rw [sub_smul, one_smul]
      abel
    have hsq : dist (z k) x₀ ^ 2 ≤ (2 * t) ^ 2 := by
      rw [Subtype.dist_eq, dist_eq_norm, hsub, norm_add_sq_real, inner_smul_left, inner_smul_right,
        hseq_x0 k, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
        sq_abs, sq_abs, hx0_norm, hseq_norm k]
      have hsqrt_ge : 1 - t ^ 2 ≤ Real.sqrt (1 - t ^ 2) := by
        have hle1 : 1 - t ^ 2 ≤ 1 := by nlinarith
        nlinarith [Real.sq_sqrt h1t2, Real.sqrt_nonneg (1 - t ^ 2)]
      nlinarith [Real.sq_sqrt h1t2]
    nlinarith [dist_nonneg (x := z k) (y := x₀)]
  have hsub_ball : ∀ k : ℕ, ball (z k) (t / 2) ⊆ U := by
    intro k y hy
    apply hεsub
    rw [mem_ball] at hy ⊢
    have htri := dist_triangle y (z k) x₀
    have hk := hz_dist k
    linarith
  have hdisj : Pairwise (fun i j : ℕ => Disjoint (ball (z i) (t / 2)) (ball (z j) (t / 2))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    rw [mem_ball] at hyi hyj
    have hdiff : (z i).val - (z j).val = t • (seq i - seq j) := by
      dsimp only [z]
      rw [smul_sub]
      abel
    have hdist_sq : dist (z i) (z j) ^ 2 = 2 * t ^ 2 := by
      rw [Subtype.dist_eq, dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        norm_sub_sq_real, hseq_norm i, hseq_norm j, hseq_orth i j hij]
      ring
    have htri : dist (z i) (z j) < t := by
      have h := dist_triangle (z i) y (z j)
      rw [dist_comm (z i) y] at h
      linarith
    nlinarith [dist_nonneg (x := z i) (y := z j)]
  have hle : (∑' k : ℕ, μ (ball (z k) (t / 2))) ≤ μ U := by
    rw [← measure_iUnion hdisj (fun k => isOpen_ball.measurableSet)]
    exact measure_mono (iUnion_subset hsub_ball)
  have hconst : ∀ k : ℕ, μ (ball (z k) (t / 2)) = μ (ball x₀ (t / 2)) :=
    fun k => hball_eq (z k) x₀ (t / 2)
  simp_rw [hconst] at hle
  rw [ENNReal.tsum_const_eq_top_of_ne_zero (hball_pos x₀ (t / 2) (by linarith))] at hle
  exact top_le_iff.mp hle

end

end OMA.Mo243037

theorem OMA.solution : type_of% @OMA.S_mo_243037.main := by
  intro H _ _ _ _ _ _ hinf
  refine ⟨OMA.Mo243037.count_invariant, OMA.Mo243037.invariant_open_eq_top hinf, fun x =>
    ⟨OMA.Mo243037.lineLaw_prob x, OMA.Mo243037.lineLaw_invariant x⟩⟩
