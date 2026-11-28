import OMAStatements.S_mo_103590
import Mathlib

namespace H103590
open scoped InnerProductSpace
open OMA.S_mo_103590

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem lineBound (T : E →L[ℂ] E) (C : ℝ) (x : E) (h : liftBound T C (ℂ ∙ x))
    (hq : ⟪x, T x⟫_ℂ ≠ 0) : ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖ := by
  have hx : x ≠ 0 := by
    rintro rfl; simp at hq
  have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨y, hy, hPy, hnorm⟩ := h x (Submodule.mem_span_singleton_self x)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp only [Submodule.starProjection_singleton] at hPy hnorm
  have hn2 : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1 : ⟪x, T (c • x)⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ) = ⟪x, T x⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ) :=
    smul_left_injective ℂ hx hPy
  rw [div_left_inj' hn2, map_smul, inner_smul_right] at h1
  have hc : c = 1 := by
    have := mul_right_cancel₀ hq (h1.trans (one_mul _).symm)
    exact this
  subst hc
  rw [one_smul, norm_smul, norm_div] at hnorm
  rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at hnorm
  have e : ‖⟪x, T x⟫_ℂ‖ / ‖x‖ ^ 2 * ‖x‖ = ‖⟪x, T x⟫_ℂ‖ / ‖x‖ := by
    field_simp
  rw [e, mul_div_assoc', le_div_iff₀ hxn] at hnorm
  nlinarith [hnorm]

theorem fwd (T : E →L[ℂ] E) (C : ℝ) (hC : 0 < C)
    (h : T = 0 ∨ ∀ x : E, ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖) : uniformBound T C := by
  intro G _ x hx
  rcases h with rfl | h
  · refine ⟨0, G.zero_mem, by simp, ?_⟩
    simp
  · refine ⟨x, hx, rfl, ?_⟩
    have key : ⟪x, T x⟫_ℂ = ⟪x, G.starProjection (T x)⟫_ℂ := by
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hx]
    have h1 := h x
    rw [key] at h1
    have h2 := norm_inner_le_norm (𝕜 := ℂ) x (G.starProjection (T x))
    have h3 : ‖x‖ ^ 2 ≤ ‖x‖ * (C * ‖G.starProjection (T x)‖) := by nlinarith
    rcases (norm_nonneg x).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · rw [pow_two] at h3
      exact le_of_mul_le_mul_left h3 h0

theorem bwd (T : E →L[ℂ] E) (C : ℝ) (hU : uniformBound T C) :
    T = 0 ∨ ∀ x : E, ‖x‖ ^ 2 ≤ C * ‖⟪x, T x⟫_ℂ‖ := by
  by_cases hT : T = 0
  · exact Or.inl hT
  right
  intro x
  by_cases hq : ⟪x, T x⟫_ℂ = 0
  swap
  · exact lineBound T C x (hU _) hq
  by_cases hx : x = 0
  · subst hx; simp
  exfalso
  obtain ⟨z, hz⟩ : ∃ z : E, ⟪z, T z⟫_ℂ ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    apply hT
    have : (T : E →ₗ[ℂ] E) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro w
      rw [← inner_conj_symm]
      simp [hall w]
    ext w
    exact LinearMap.congr_fun this w
  set a := ⟪z, T z⟫_ℂ with ha
  set b := ⟪x, T z⟫_ℂ + ⟪z, T x⟫_ℂ with hb
  have hqt : ∀ t : ℝ, ⟪x + (t : ℂ) • z, T (x + (t : ℂ) • z)⟫_ℂ = (t : ℂ) * b + (t : ℂ) ^ 2 * a := by
    intro t
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hq, Complex.conj_ofReal, ha, hb]
    ring
  have hev : ∀ᶠ t : ℝ in nhdsWithin (0:ℝ) {0}ᶜ, (t : ℂ) * b + (t : ℂ) ^ 2 * a ≠ 0 := by
    by_cases hb0 : b = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hb0]
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      simp [this, hz]
    · have hc : ContinuousAt (fun t : ℝ => b + (t : ℂ) * a) 0 := by fun_prop
      have h2 : ∀ᶠ t : ℝ in nhds (0:ℝ), b + (t : ℂ) * a ≠ 0 := hc.eventually_ne (by simpa using hb0)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h2] with t ht h3
      rw [show (t : ℂ) * b + (t : ℂ) ^ 2 * a = t * (b + t * a) by ring]
      exact mul_ne_zero (by exact_mod_cast ht) h3
  have hf : ContinuousAt (fun t : ℝ => ‖x + (t : ℂ) • z‖ ^ 2 - C * ‖(t : ℂ) * b + (t : ℂ) ^ 2 * a‖) 0 := by
    fun_prop
  have hpos : ∀ᶠ t : ℝ in nhds (0:ℝ), 0 < ‖x + (t : ℂ) • z‖ ^ 2 - C * ‖(t : ℂ) * b + (t : ℂ) ^ 2 * a‖ := by
    apply (continuousAt_const (y := (0:ℝ))).eventually_lt hf
    simp [norm_pos_iff.mpr hx]
  obtain ⟨t, h1, h2⟩ := (hev.and (nhdsWithin_le_nhds hpos)).exists
  have := lineBound T C (x + (t : ℂ) • z) (hU _) (by rw [hqt]; exact h1)
  rw [hqt] at this
  linarith

theorem part2 : (let E := EuclideanSpace ℂ (Fin 2)
     ∃ T : E ≃ₗᵢ[ℂ] E, Function.Involutive T ∧
       ∀ C : ℝ, 0 < C → ∃ x : E, ‖x‖=1 ∧
         ¬liftBound T.toLinearIsometry.toContinuousLinearMap C (ℂ ∙ x)) := by
  dsimp only
  refine ⟨LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (0:Fin 2) 1), ?_, ?_⟩
  · intro v
    ext i
    fin_cases i <;> simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  · intro C hC
    set T := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap (0:Fin 2) 1) with hT
    set ε : ℝ := 1 / (4 * C) with hε
    set v : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, (ε : ℂ)] with hv
    have hqv : ⟪v, T v⟫_ℂ = 2 * (ε : ℂ) := by
      simp only [hv, hT, PiLp.inner_apply, Fin.sum_univ_two, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
      simp
      ring
    have hv1 : 1 ≤ ‖v‖ := by
      have := PiLp.norm_apply_le v 0
      simpa [hv] using this
    have hvpos : 0 < ‖v‖ := by linarith
    set c : ℝ := ‖v‖⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ hv1
    refine ⟨(c : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, hc]
      exact inv_mul_cancel₀ hvpos.ne'
    · intro h
      have hq : ⟪(c : ℂ) • v, T.toLinearIsometry.toContinuousLinearMap ((c : ℂ) • v)⟫_ℂ
          = ((c ^ 2 * (2 * ε) : ℝ) : ℂ) := by
        have e : T.toLinearIsometry.toContinuousLinearMap ((c : ℂ) • v) = (c : ℂ) • T v := by
          simp
        rw [e, inner_smul_left, inner_smul_right, hqv, Complex.conj_ofReal]
        push_cast
        ring
      have hpos : (0:ℝ) < c ^ 2 * (2 * ε) := by positivity
      have hb := lineBound _ C _ h (by rw [hq]; exact_mod_cast hpos.ne')
      rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hc0, hc, inv_mul_cancel₀ hvpos.ne', ← hc] at hb
      have : C * (c ^ 2 * (2 * ε)) = c ^ 2 / 2 := by
        rw [hε]; field_simp; ring
      rw [this] at hb
      nlinarith

end H103590

theorem OMA.solution : type_of% @OMA.S_mo_103590.main :=
  ⟨fun _ _ _ T C hC => ⟨H103590.bwd T C, H103590.fwd T C hC⟩, H103590.part2⟩
