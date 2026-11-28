import OMAStatements.S_mo_369944

-- Problem: Extension of positive functionals
-- Upstream: formal-conjectures statements/mo-369944.lean:0 (declaration OMA.S_mo_369944.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_mo_369944.main := by
  let f : C(unitInterval, ℝ) := ⟨fun x => (x : ℝ), continuous_subtype_val⟩
  let p : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  let Φ : C(unitInterval, ℝ) →L[ℝ] ℝ :=
    (4 : ℝ) • ContinuousMap.evalCLM ℝ p - ContinuousMap.evalCLM ℝ (1 : unitInterval)
  have hΦf : Φ f = 1 := by
    simp [Φ, f, p]; norm_num
  have hΦg : Φ (f * f) = 0 := by
    simp [Φ, f, p]; norm_num
  refine ⟨unitInterval, inferInstance, inferInstance, Submodule.span ℝ {f, f * f},
    Φ.comp (Submodule.subtypeL _), ?_, ?_⟩
  · rintro ⟨h, hh⟩ hpos
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hh
    have hL : Φ (a • f + b • (f * f)) = a := by
      rw [map_add, map_smul, map_smul, hΦf, hΦg]; simp
    show 0 ≤ Φ (a • f + b • (f * f))
    rw [hL]
    by_contra hneg
    have hneg : a < 0 := not_le.1 hneg
    have hb := le_abs_self b
    have hb0 := abs_nonneg b
    have hc : 0 < |b| + 1 - a := by linarith
    have hx := hpos ⟨-a / (|b| + 1 - a), by
      constructor
      · exact div_nonneg (by linarith) hc.le
      · rw [div_le_one hc]; linarith⟩
    have hx' : 0 ≤ a * (-a / (|b| + 1 - a)) + b * ((-a / (|b| + 1 - a)) * (-a / (|b| + 1 - a))) := by
      simpa [f] using hx
    have e : a * (-a / (|b| + 1 - a)) + b * ((-a / (|b| + 1 - a)) * (-a / (|b| + 1 - a)))
        = -(a ^ 2 * (|b| + 1 - a - b)) / (|b| + 1 - a) ^ 2 := by
      field_simp
      ring
    rw [e] at hx'
    have hnum : 0 < a ^ 2 * (|b| + 1 - a - b) := by
      apply mul_pos
      · nlinarith
      · linarith
    have : -(a ^ 2 * (|b| + 1 - a - b)) / (|b| + 1 - a) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith
  · rintro ⟨E, hE, hext⟩
    have hf : E f = 1 := by
      have := hext ⟨f, Submodule.subset_span (by simp)⟩
      simpa [hΦf] using this
    have hg : E (f * f) = 0 := by
      have := hext ⟨f * f, Submodule.subset_span (by simp)⟩
      simpa [hΦg] using this
    have key : ∀ t : ℝ, 0 ≤ E 1 - 2 * t * E f + t ^ 2 * E (f * f) := by
      intro t
      have := hE (1 - (2 * t) • f + (t ^ 2) • (f * f)) (by
        intro x
        simp [f]
        nlinarith [sq_nonneg (1 - t * (x : ℝ))])
      simpa [map_sub, map_add, map_smul] using this
    have h0 := key 0
    have h1 := key (E 1 + 1)
    rw [hf, hg] at h0 h1
    nlinarith
