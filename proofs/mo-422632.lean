import OMAStatements.S_mo_422632

open MeasureTheory
open scoped ENNReal

namespace Claude422632

open OMA.S_mo_422632

theorem part1 (Ω E : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
      (μ : Measure Ω) (X : Ω → E) (z : E) (f : E → WithTop ℝ) (g : Ω → ℝ)
      (hC : EpigraphCone f) (hP : PettisValue μ X z) (hg : Integrable g μ)
      (hfg : ∀ᵐ ω ∂μ, f (X ω) ≤ (g ω : WithTop ℝ)) : f z ≤ ((∫ ω, g ω ∂μ : ℝ) : WithTop ℝ) := by
  obtain ⟨C, hCf⟩ := hC
  rw [← hCf]
  by_contra hnot
  have hconv : Convex ℝ (C : Set (E × ℝ)) := C.toPointedCone.convex
  have hclosed : IsClosed (C : Set (E × ℝ)) := C.isClosed
  obtain ⟨φ, u, hφ, hu⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  have h0 : (0 : E × ℝ) ∈ C := C.zero_mem
  have hu0 : 0 < u := by simpa using hφ 0 h0
  have hneg : ∀ c ∈ C, φ c ≤ 0 := by
    intro c hc
    by_contra h
    push Not at h
    have hmem : (u / φ c) • c ∈ C := C.smul_mem hc (by positivity)
    have := hφ _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne'] at this
    exact lt_irrefl _ this
  set L : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hL
  set a : ℝ := φ (0, 1) with ha
  have hdecomp : ∀ (x : E) (r : ℝ), φ (x, r) = L x + r * a := by
    intro x r
    have : (x, r) = (x, (0 : ℝ)) + r • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul]
    simp [hL, ha]
  obtain ⟨hLint, hLz⟩ := hP L
  have hpt : ∀ᵐ ω ∂μ, L (X ω) + g ω * a ≤ 0 := by
    filter_upwards [hfg] with ω hω
    rw [← hdecomp]
    exact hneg _ ((hCf _ _).2 hω)
  have hint : ∫ ω, (L (X ω) + g ω * a) ∂μ ≤ 0 := integral_nonpos_of_ae hpt
  rw [integral_add hLint (hg.mul_const a), integral_mul_const, ← hLz, ← hdecomp] at hint
  linarith

theorem part2 (Ω E : Type) [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] (μ : Measure Ω) (X : Ω → E) (hX : Integrable X μ) :
      PettisValue μ X (∫ ω, X ω ∂μ) := fun L =>
  ⟨L.integrable_comp hX, (L.integral_comp_comm hX).symm⟩

noncomputable def a (n : ℕ) : ℝ := if n = 0 then 0 else (1 / 2 : ℝ) ^ n

noncomputable def X (n : ℕ) : H := a n • (lp.single 2 n (1 : ℝ) : H)

noncomputable def μ : Measure ℕ := Measure.count + (⊤ : ℝ≥0∞) • Measure.dirac 0

lemma X_apply (n k : ℕ) : (X n : ℕ → ℝ) k = if k = n then a n else 0 := by
  by_cases h : k = n
  · subst h; simp [X]
  · simp [X, h]

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by unfold a; split_ifs <;> positivity

lemma norm_X (n : ℕ) : ‖X n‖ = a n := by
  rw [X, norm_smul, lp.norm_single (by norm_num), Real.norm_eq_abs, abs_of_nonneg (a_nonneg n)]
  simp

lemma integrable_X : Integrable X μ := by
  refine Integrable.add_measure ?_ ?_
  · rw [integrable_count_iff]
    simp only [norm_X]
    refine Summable.of_nonneg_of_le a_nonneg (fun n => ?_)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    unfold a; split_ifs <;> first | positivity | exact le_rfl
  · have h0 : X =ᵐ[(⊤ : ℝ≥0∞) • Measure.dirac 0] (fun _ => (0 : H)) := by
      rw [Filter.EventuallyEq, ae_iff]
      have h00 : (0 : ℕ) ∉ {n | ¬ X n = 0} := by simp [X, a]
      simp [Measure.smul_apply, h00]
    exact (integrable_zero _ _ _).congr h0.symm

lemma mu_real_singleton {k : ℕ} (hk : k ≠ 0) : μ.real {k} = 1 := by
  simp [μ, Measure.real, hk.symm]

lemma integral_apply {k : ℕ} (hk : k ≠ 0) : ((∫ n, X n ∂μ : H) : ℕ → ℝ) k = a k := by
  have h1 := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k).integral_comp_comm integrable_X
  have h2 : (fun n => (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k) (X n)) =
      Set.indicator {k} (fun _ => a k) := by
    funext n
    change (X n : ℕ → ℝ) k = _
    rw [X_apply]
    by_cases h : k = n
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [h2, integral_indicator_const _ (measurableSet_singleton k), mu_real_singleton hk] at h1
  have h3 : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k) (∫ n, X n ∂μ) = ((∫ n, X n ∂μ : H) : ℕ → ℝ) k := rfl
  rw [← h3, ← h1]; simp

lemma not_mem_span : (∫ n, X n ∂μ : H) ∉ Submodule.span ℝ (Set.range X) := by
  intro hmem
  have key : ∀ y ∈ Submodule.span ℝ (Set.range X), ∃ N : ℕ, ∀ k, N ≤ k → (y : ℕ → ℝ) k = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      refine ⟨n + 1, fun k hk => ?_⟩
      rw [X_apply, if_neg (by omega)]
    | zero => exact ⟨0, fun k _ => rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨N, hN⟩ := hy
      obtain ⟨M, hM⟩ := hz
      refine ⟨max N M, fun k hk => ?_⟩
      have h1 := hN k (le_trans (le_max_left _ _) hk)
      have h2 := hM k (le_trans (le_max_right _ _) hk)
      simp [h1, h2]
    | smul c y _ hy =>
      obtain ⟨N, hN⟩ := hy
      exact ⟨N, fun k hk => by simp [hN k hk]⟩
  obtain ⟨N, hN⟩ := key _ hmem
  have h := hN (N + 1) (by omega)
  rw [integral_apply (by omega)] at h
  have : (0 : ℝ) < a (N + 1) := by unfold a; rw [if_neg (by omega)]; positivity
  linarith

lemma not_sigmaFinite : ¬ SigmaFinite μ := by
  intro h
  have hmem : (0 : ℕ) ∈ ⋃ i, spanningSets μ i := by rw [iUnion_spanningSets]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem
  have h1 : μ {0} ≤ μ (spanningSets μ i) := measure_mono (Set.singleton_subset_iff.2 hi)
  have h2 : μ {0} = ⊤ := by simp [μ]
  exact absurd (measure_spanningSets_lt_top μ i) (by rw [h2] at h1; exact not_lt.2 h1)

theorem part3 : ∃ (μ : Measure ℕ) (X : ℕ → H) (F : H →ₗ[ℝ] ℝ),
      ¬SigmaFinite μ ∧ Integrable X μ ∧ (∀ n, F (X n) = 0) ∧
      F (∫ n, X n ∂μ) = 1 ∧ (∫ n, F (X n) ∂μ) < F (∫ n, X n ∂μ) := by
  obtain ⟨F0, hF0, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem not_mem_span inferInstance
  have hz : ∀ n, F0 (X n) = 0 := by
    intro n
    have : F0 (X n) ∈ (Submodule.span ℝ (Set.range X)).map F0 :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, rfl⟩)
    rw [hmap] at this
    simpa using this
  set F : H →ₗ[ℝ] ℝ := (F0 (∫ n, X n ∂μ))⁻¹ • F0 with hF
  have hzF : ∀ n, F (X n) = 0 := fun n => by simp [hF, hz n]
  have hone : F (∫ n, X n ∂μ) = 1 := by simp [hF, inv_mul_cancel₀ hF0]
  refine ⟨μ, X, F, not_sigmaFinite, integrable_X, hzF, hone, ?_⟩
  rw [hone]
  simp [hzF]

end Claude422632

theorem OMA.solution : type_of% @OMA.S_mo_422632.main :=
  ⟨Claude422632.part1, Claude422632.part2, Claude422632.part3⟩
