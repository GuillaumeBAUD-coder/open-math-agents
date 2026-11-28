import OMAStatements.S_mo_103590

open scoped InnerProductSpace
open Submodule

namespace CodexTwo.Mo103590

open OMA.S_mo_103590

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem line_estimate (T : E →L[ℂ] E) (C : ℝ) (x : E)
    (h : liftBound T C (ℂ ∙ x)) (hq : ⟪x, T x⟫_ℂ ≠ 0) :
    ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖ := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact hq (by simp)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let P := (ℂ ∙ x).starProjection
  have hP : P (T x) = (⟪x, T x⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ)) • x :=
    starProjection_singleton ℂ (T x)
  have hPne : P (T x) ≠ 0 := by
    rw [hP]
    apply smul_ne_zero _ hx
    exact div_ne_zero hq (by exact_mod_cast (pow_pos hn 2).ne')
  obtain ⟨y, hy, heq, hb⟩ := h x (mem_span_singleton_self x)
  obtain ⟨z, rfl⟩ := mem_span_singleton.mp hy
  have hz : z = 1 := by
    apply smul_left_injective ℂ hPne
    change P (T (z • x)) = P (T x) at heq
    simpa only [map_smul, one_smul] using heq
  subst z
  simp only [one_smul] at hb
  have hnorm : ‖P (T x)‖ * ‖x‖ = ‖⟪x, T x⟫_ℂ‖ := by
    rw [hP, norm_smul, norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖x‖)]
    field_simp [hn.ne']
  calc
    ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := sq _
    _ ≤ (C * ‖P (T x)‖) * ‖x‖ := mul_le_mul_of_nonneg_right hb hn.le
    _ = C * ‖⟪x, T x⟫_ℂ‖ := by rw [mul_assoc, hnorm]

private theorem line_dichotomy (T : E →L[ℂ] E) {C : ℝ}
    (hC : 0 < C) (h : ∀ x, liftBound T C (ℂ ∙ x)) :
    T = 0 ∨ ∀ x, ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖ := by
  by_cases hT : T = 0
  · exact Or.inl hT
  have hq : ∃ y, ⟪y, T y⟫_ℂ ≠ 0 := by
    by_contra! hq
    apply hT
    have hlin : T.toLinearMap = 0 :=
      (inner_map_self_eq_zero T.toLinearMap).mp fun y ↦ by
        rw [← inner_conj_symm]
        change starRingEnd ℂ ⟪y, T y⟫_ℂ = 0
        simp [hq y]
    ext y
    exact LinearMap.congr_fun hlin y
  obtain ⟨y, hy⟩ := hq
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp)
  let e : ℂ →ₗ[ℝ] E := (ContinuousLinearMap.toSpanSingleton ℂ y).toLinearMap.restrictScalars ℝ
  have hrank' := LinearMap.lift_rank_le_of_injective e
    (show Function.Injective e from smul_left_injective ℂ hy0)
  have hrank : 1 < Module.rank ℝ E := by
    have htwo : 2 ≤ Module.rank ℝ E := by
      simpa [Complex.rank_real_complex] using hrank'
    exact (show (1 : Cardinal) < 2 by norm_num).trans_le htwo
  let S : Set E := ({0} : Set E)ᶜ
  have hs : IsPreconnected S := (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected
  let f : E → ℝ := fun x ↦ ‖⟪x, T x⟫_ℂ‖ / ‖x‖ ^ 2
  have hf : ContinuousOn f S := by
    apply ContinuousOn.div
    · exact (continuous_id.inner T.continuous).norm.continuousOn
    · exact continuous_norm.pow 2 |>.continuousOn
    · intro x hx
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (by simpa [S] using hx))
  have hyS : y ∈ S := by simpa [S] using hy0
  have hlower : ∀ x ∈ S, ⟪x, T x⟫_ℂ ≠ 0 → 1 / C ≤ f x := by
    intro x hx hqx
    have hp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr (by simpa [S] using hx)) 2
    apply (le_div_iff₀ hp).2
    have he := line_estimate T C x (h x) hqx
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hC, mul_comm]
    exact he
  right
  intro x
  by_cases hx : x = 0
  · simp [hx]
  by_cases hqx : ⟪x, T x⟫_ℂ = 0
  · have hxS : x ∈ S := by simpa [S] using hx
    have hfx : f x = 0 := by simp [f, hqx]
    have hmid : 1 / (2 * C) ∈ Set.Icc (f x) (f y) := by
      refine ⟨hfx ▸ (one_div_pos.mpr (mul_pos (by norm_num) hC)).le, ?_⟩
      exact (one_div_le_one_div_of_le hC (by linarith)).trans (hlower y hyS hy)
    obtain ⟨z, hzS, hz⟩ := hs.intermediate_value hxS hyS hf hmid
    have hzpos : 0 < 1 / (2 * C) := one_div_pos.mpr (mul_pos (by norm_num) hC)
    have hqz : ⟪z, T z⟫_ℂ ≠ 0 := by
      intro hzero
      have : f z = 0 := by simp [f, hzero]
      rw [this] at hz
      exact hzpos.ne' hz.symm
    have hlt : 1 / (2 * C) < 1 / C := one_div_lt_one_div_of_lt hC (by linarith)
    exact (hlt.not_ge (hz ▸ hlower z hzS hqz)).elim
  · exact line_estimate T C x (h x) hqx

private theorem uniform_iff (T : E →L[ℂ] E) {C : ℝ} (hC : 0 < C) :
    uniformBound T C ↔ T = 0 ∨ ∀ x, ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖ := by
  constructor
  · intro h
    exact line_dichotomy T hC fun x ↦ h (ℂ ∙ x)
  · rintro (rfl | h) G _ x hx
    · exact ⟨0, G.zero_mem, by simp, by simp⟩
    refine ⟨x, hx, rfl, ?_⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hinner : ⟪x, T x⟫_ℂ = ⟪x, G.starProjection (T x)⟫_ℂ := by
      rw [← G.inner_starProjection_left_eq_right, G.starProjection_eq_self_iff.mpr hx]
    apply (le_of_mul_le_mul_left _ hp)
    calc
      ‖x‖ * ‖x‖ = ‖x‖ ^ 2 := (sq _).symm
      _ ≤ C * ‖⟪x, T x⟫_ℂ‖ := h x
      _ ≤ C * (‖x‖ * ‖G.starProjection (T x)‖) :=
        mul_le_mul_of_nonneg_left (hinner ▸ norm_inner_le_norm x (G.starProjection (T x))) hC.le
      _ = ‖x‖ * (C * ‖G.starProjection (T x)‖) := by ring

private theorem unit_to_line (T : E →L[ℂ] E) (C : ℝ)
    (h : ∀ x : E, ‖x‖ = 1 → liftBound T C (ℂ ∙ x)) (x : E) :
    liftBound T C (ℂ ∙ x) := by
  by_cases hx : x = 0
  · subst x
    intro y hy
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hy
    simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let a : ℂ := ((‖x‖ : ℝ) : ℂ)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
    have hunit : ‖a • x‖ = 1 := by
      rw [norm_smul, show ‖a‖ = ‖x‖⁻¹ by simp [a], inv_mul_cancel₀ hn.ne']
    simpa only [span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha)] using h (a • x) hunit

private theorem swap_example :
    let V := EuclideanSpace ℂ (Fin 2)
    ∃ T : V ≃ₗᵢ[ℂ] V, Function.Involutive T ∧
      ∀ C : ℝ, 0 < C → ∃ x : V, ‖x‖ = 1 ∧
        ¬ liftBound T.toLinearIsometry.toContinuousLinearMap C (ℂ ∙ x) := by
  let e : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  have he : e.symm = e := Equiv.symm_swap _ _
  have hT : T.symm = T := by
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm = _
    rw [LinearIsometryEquiv.piLpCongrLeft_symm, he]
  refine ⟨T, fun x ↦ ?_, ?_⟩
  · rw [← congrArg (fun S : _ ≃ₗᵢ[ℂ] _ ↦ S (T x)) hT]
    exact T.symm_apply_apply x
  · intro C hC
    by_contra! habs
    let A := T.toLinearIsometry.toContinuousLinearMap
    obtain hA | hA := line_dichotomy A hC (unit_to_line A C habs)
    · let x := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
      have hnorm : ‖A x‖ = 1 := by
        change ‖T x‖ = 1
        simp [x]
      simp [hA] at hnorm
    · let x := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
      have hq : ⟪x, A x⟫_ℂ = 0 := by
        change ⟪x, T x⟫_ℂ = 0
        rw [show T x = EuclideanSpace.single (1 : Fin 2) (1 : ℂ) by
          simp [T, x, e]]
        simp [x, EuclideanSpace.inner_single_left]
      have hbad : (1 : ℝ) ≤ 0 := by simpa [x, hq] using hA x
      exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hbad

end CodexTwo.Mo103590

theorem OMA.solution : type_of% @OMA.S_mo_103590.main := by
  exact ⟨fun _ _ _ T _ hC ↦ CodexTwo.Mo103590.uniform_iff T hC,
    CodexTwo.Mo103590.swap_example⟩
