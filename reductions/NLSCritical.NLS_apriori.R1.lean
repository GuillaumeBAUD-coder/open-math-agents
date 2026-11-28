import FormalConjectures.Paper.NLSCritical

/-!
The critical dilation multiplies the solution by a, space by a², and time by a⁴.
Energy and the spacetime tenth-power integral are invariant. Initial squared mass
and interval radius both decrease by a factor of a⁴. Thus one only needs the
uniform estimate on intervals of radius at most one with initial squared mass
at most one.
-/

open MeasureTheory Set NLSCritical
open scoped Pointwise

namespace OMA.R_NLSCritical_NLS_apriori_R1

def H1 : Prop :=
  ∀ (l a : ℝ), 0 < l → 0 < a → ∀ s : LocalSchwartzSolution l,
    ∃ v : LocalSchwartzSolution (l / a ^ 4),
      ∀ t x, v.u t x = a • s.u (a ^ 4 * t) (a ^ 2 • x)

def H2 : Prop :=
  ∃ f : ℝ → ℝ, ∀ l > 0, l ≤ 1 → ∀ s : LocalSchwartzSolution l,
    (∫ x, ‖s.u 0 x‖ ^ 2) ≤ 1 → L10_local l s.u ≤ f (energy (s.u 0))

lemma spatial_change (g : EuclideanSpace ℝ (Fin 3) → ℝ) (a : ℝ) :
    (∫ x, g (a ^ 2 • x)) = (a ^ 6)⁻¹ * ∫ x, g x := by
  simpa [smul_eq_mul, ← pow_mul] using
    (Measure.integral_comp_smul_of_nonneg volume g (a ^ 2) (hR := sq_nonneg a))

lemma moment_change (u : EuclideanSpace ℝ (Fin 3) → ℂ) {a : ℝ} (ha : 0 < a) (p : ℕ) :
    (∫ x, ‖a • u (a ^ 2 • x)‖ ^ p) = a ^ p / a ^ 6 * ∫ x, ‖u x‖ ^ p := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  rw [integral_const_mul, spatial_change (fun x => ‖u x‖ ^ p) a]
  ring

lemma energy_change (u : EuclideanSpace ℝ (Fin 3) → ℂ) (hu : Differentiable ℝ u)
    {a : ℝ} (ha : 0 < a) :
    energy (fun x => a • u (a ^ 2 • x)) = energy u := by
  let D := a ^ 2 • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))
  have grad (x y : EuclideanSpace ℝ (Fin 3)) :
      fderiv ℝ (fun z => a • u (a ^ 2 • z)) x y = a ^ 3 • fderiv ℝ u (a ^ 2 • x) y := by
    have hd := (((hu (D x)).hasFDerivAt.comp x D.hasFDerivAt).const_smul a).fderiv
    change fderiv ℝ (a • (u ∘ D)) x y = _
    rw [hd]
    simp [D, smul_smul, pow_succ, mul_comm]
  let density := fun x => (1 / 2 : ℝ) *
    (∑ j : Fin 3, ‖fderiv ℝ u x (EuclideanSpace.single j 1)‖ ^ 2) +
    (1 / 6 : ℝ) * ‖u x‖ ^ 6
  unfold energy
  calc
    _ = ∫ x, a ^ 6 * density (a ^ 2 • x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [density, grad, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        abs_of_pos (pow_pos ha 3), mul_pow, ← Finset.mul_sum]
      ring
    _ = ∫ x, density x := by
      rw [integral_const_mul, spatial_change density a]
      field_simp

lemma spacetime_change (u : ℝ → EuclideanSpace ℝ (Fin 3) → ℂ) (l : ℝ)
    {a : ℝ} (ha : 0 < a) :
    L10_local (l / a ^ 4) (fun t x => a • u (a ^ 4 * t) (a ^ 2 • x)) = L10_local l u := by
  have h4 : 0 < a ^ 4 := pow_pos ha _
  have cancel (t : ℝ) : a ^ 4 * (t / a ^ 4) = t := by field_simp
  have hs : (a ^ 4) • Icc (-(l / a ^ 4)) (l / a ^ 4) = Icc (-l) l := by
    rw [LinearOrderedField.smul_Icc h4, mul_neg, cancel]
  let g := fun t => ∫ x, ‖u t x‖ ^ 10
  have ht := Measure.setIntegral_comp_smul_of_pos volume g (Icc (-(l / a ^ 4)) (l / a ^ 4)) h4
  rw [hs] at ht
  simp only [Module.finrank_self, pow_one, smul_eq_mul] at ht
  unfold L10_local
  simp_rw [moment_change _ ha 10]
  rw [integral_const_mul, ht]
  field_simp
  ring

theorem main : H1 → H2 → type_of% @NLSCritical.NLS_apriori := by
  intro dilation normalized
  obtain ⟨f, bound⟩ := normalized
  refine ⟨f, ?_⟩
  intro l hl s
  let m := ∫ x, ‖s.u 0 x‖ ^ 2
  let a := max 1 (max l m)
  have ha1 : 1 ≤ a := le_max_left _ _
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have ha2 : a ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  have ha4 : a ≤ a ^ 4 := by nlinarith [sq_nonneg (a ^ 2 - 1)]
  have hl4 : l ≤ a ^ 4 := (le_max_left l m).trans ((le_max_right 1 _).trans ha4)
  have hm4 : m ≤ a ^ 4 := (le_max_right l m).trans ((le_max_right 1 _).trans ha4)
  obtain ⟨v, hv⟩ := dilation l a hl ha s
  have hzero : v.u 0 = fun x => a • s.u 0 (a ^ 2 • x) := funext fun x => by simpa using hv 0 x
  have hm : (∫ x, ‖v.u 0 x‖ ^ 2) ≤ 1 := by
    rw [hzero, moment_change _ ha 2]
    change a ^ 2 / a ^ 6 * m ≤ 1
    calc
      _ = m / a ^ 4 := by field_simp
      _ ≤ 1 := (div_le_one (pow_pos ha 4)).mpr hm4
  obtain ⟨sch, hsch⟩ := s.schwartz 0 ⟨by linarith, hl.le⟩
  have hu : Differentiable ℝ (s.u 0) := by
    rw [hsch]
    exact sch.differentiable
  have h := bound _ (div_pos hl (pow_pos ha _)) ((div_le_one (pow_pos ha 4)).mpr hl4) v hm
  rw [hzero, energy_change _ hu ha] at h
  rw [show v.u = _ from funext fun t => funext fun x => hv t x, spacetime_change _ _ ha] at h
  exact h

end OMA.R_NLSCritical_NLS_apriori_R1
