import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

-- Problem: The Maxwell conjecture — two charges
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2607.27197/MaxwellConjecture.lean:215 (declaration Arxiv.«2607.27197».maxwell_conjecture.variants.two_charges)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.two_charges := by
  intro q a ha hq
  have hterm : ∀ (k : ℝ) (p x : EuclideanSpace ℝ (Fin 3)), x ≠ p →
      HasGradientAt (fun y => k / dist y p) ((-(k / ‖x - p‖ ^ 3)) • (x - p)) x := by
    intro k p x hxp
    have hne : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxp)
    have hsx : Real.sqrt (‖x - p‖ ^ 2) = ‖x - p‖ := Real.sqrt_sq (norm_nonneg _)
    have hN := ((hasFDerivAt_id x).sub_const p).norm_sq
    have hS := hN.sqrt (pow_ne_zero 2 hne)
    have hI : HasDerivAt (fun t : ℝ => k * t⁻¹) (k * -(‖x - p‖ ^ 2)⁻¹)
        (Real.sqrt (‖x - p‖ ^ 2)) := by
      rw [hsx]
      exact (hasDerivAt_inv hne).const_mul k
    have hcomp := hI.comp_hasFDerivAt x hS
    have hfun : (fun y => k / dist y p)
        = (fun t : ℝ => k * t⁻¹) ∘ fun y => Real.sqrt (‖y - p‖ ^ 2) := by
      funext y
      simp only [Function.comp]
      rw [Real.sqrt_sq (norm_nonneg _), dist_eq_norm, div_eq_mul_inv]
    rw [hasGradientAt_iff_hasFDerivAt, hfun]
    refine hcomp.congr_fderiv ?_
    ext w
    simp [InnerProductSpace.toDual_apply_apply, hsx]
    field_simp
  have hgrad : ∀ x ∈ Arxiv.«2607.27197».equilibria q a, x ≠ a 0 ∧ x ≠ a 1 ∧
      (q 0 / ‖x - a 0‖ ^ 3) • (x - a 0) + (q 1 / ‖x - a 1‖ ^ 3) • (x - a 1) = 0 := by
    intro x hx
    have hx' : x ∉ Set.range a ∧ gradient (Arxiv.«2607.27197».potential q a) x = 0 := hx
    have hx0 : x ≠ a 0 := fun h => hx'.1 ⟨0, h.symm⟩
    have hx1 : x ≠ a 1 := fun h => hx'.1 ⟨1, h.symm⟩
    refine ⟨hx0, hx1, ?_⟩
    have hV : HasGradientAt (Arxiv.«2607.27197».potential q a)
        ((-(q 0 / ‖x - a 0‖ ^ 3)) • (x - a 0) + (-(q 1 / ‖x - a 1‖ ^ 3)) • (x - a 1)) x := by
      rw [hasGradientAt_iff_hasFDerivAt, map_add]
      have e : Arxiv.«2607.27197».potential q a
          = fun y => q 0 / dist y (a 0) + q 1 / dist y (a 1) := by
        funext y
        simp [Arxiv.«2607.27197».potential, Fin.sum_univ_two]
      rw [e]
      exact (hterm (q 0) (a 0) x hx0).hasFDerivAt.add (hterm (q 1) (a 1) x hx1).hasFDerivAt
    have h0 : (-(q 0 / ‖x - a 0‖ ^ 3)) • (x - a 0) + (-(q 1 / ‖x - a 1‖ ^ 3)) • (x - a 1) = 0 := by
      rw [← hV.gradient]
      exact hx'.2
    calc (q 0 / ‖x - a 0‖ ^ 3) • (x - a 0) + (q 1 / ‖x - a 1‖ ^ 3) • (x - a 1)
        = -((-(q 0 / ‖x - a 0‖ ^ 3)) • (x - a 0) + (-(q 1 / ‖x - a 1‖ ^ 3)) • (x - a 1)) := by
          simp [neg_smul, add_comm]
      _ = 0 := by rw [h0, neg_zero]
  have hcex : ∃ c : ℝ, ∀ x ∈ Arxiv.«2607.27197».equilibria q a, x - a 0 = c • (x - a 1) := by
    refine ⟨-(q 1 / q 0) * Real.sqrt (|q 0| / |q 1|) ^ 3, ?_⟩
    intro x hx
    obtain ⟨hx0, hx1, h1⟩ := hgrad x hx
    have ha0 : 0 < ‖x - a 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx0)
    have hb0 : 0 < ‖x - a 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
    have ha0' : ‖x - a 0‖ ≠ 0 := ha0.ne'
    have hb0' : ‖x - a 1‖ ≠ 0 := hb0.ne'
    have hq0 : q 0 ≠ 0 := hq 0
    have hq1 : q 1 ≠ 0 := hq 1
    have hn := congrArg norm (eq_neg_of_add_eq_zero_left h1)
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
      abs_of_pos (pow_pos ha0 3), abs_of_pos (pow_pos hb0 3)] at hn
    have e1 : |q 0| / ‖x - a 0‖ ^ 3 * ‖x - a 0‖ * ‖x - a 0‖ ^ 2 = |q 0| := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (pow_pos ha0 3).ne']
      ring
    have e2 : |q 1| / ‖x - a 1‖ ^ 3 * ‖x - a 1‖ * ‖x - a 1‖ ^ 2 = |q 1| := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (pow_pos hb0 3).ne']
      ring
    have hnorm : |q 0| * ‖x - a 1‖ ^ 2 = |q 1| * ‖x - a 0‖ ^ 2 := by
      linear_combination (-(‖x - a 1‖ ^ 2)) * e1 + ‖x - a 0‖ ^ 2 * e2
        + ‖x - a 0‖ ^ 2 * ‖x - a 1‖ ^ 2 * hn
    have hρ : (‖x - a 0‖ / ‖x - a 1‖) ^ 2 = |q 0| / |q 1| := by
      rw [div_pow, div_eq_div_iff (pow_pos hb0 2).ne' (abs_pos.mpr hq1).ne']
      linear_combination -hnorm
    have hr : Real.sqrt (|q 0| / |q 1|) = ‖x - a 0‖ / ‖x - a 1‖ := by
      rw [← hρ]
      exact Real.sqrt_sq (div_nonneg ha0.le hb0.le)
    rw [hr]
    calc x - a 0 = (‖x - a 0‖ ^ 3 / q 0) • ((q 0 / ‖x - a 0‖ ^ 3) • (x - a 0)) := by
          rw [smul_smul, show ‖x - a 0‖ ^ 3 / q 0 * (q 0 / ‖x - a 0‖ ^ 3) = 1 by field_simp,
            one_smul]
      _ = (‖x - a 0‖ ^ 3 / q 0) • (-((q 1 / ‖x - a 1‖ ^ 3) • (x - a 1))) := by
          rw [eq_neg_of_add_eq_zero_left h1]
      _ = (-(q 1 / q 0) * (‖x - a 0‖ / ‖x - a 1‖) ^ 3) • (x - a 1) := by
          rw [smul_neg, smul_smul, ← neg_smul]
          congr 1
          field_simp
  rw [Set.encard_le_one_iff]
  intro x y hx hy
  obtain ⟨c, hcx⟩ := hcex
  have hxc := hcx x hx
  have hyc := hcx y hy
  have h3 : (1 - c) • (x - y) = 0 := by
    linear_combination (norm := module) hxc - hyc
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have hc1 : c = 1 := by linarith
    rw [hc1, one_smul] at hxc
    exact absurd (ha (sub_right_inj.mp hxc)) (by decide)
  · exact sub_eq_zero.mp h4
