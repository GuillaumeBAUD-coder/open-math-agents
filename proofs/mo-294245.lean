import OMAStatements.S_mo_294245

/-!
Proof of `OMA.S_mo_294245.main` (MathOverflow 294245), following the counterexample in the comments:
in `G = ℤ/3ℤ` (written multiplicatively, discrete topology), `μ = δ₁` is infinitely divisible and
`ν = δ_g` (`g` a generator) satisfies `ν^{∗3} = μ`, but `ν` has no probability cube root: if
`ρ^{∗3} = δ_g` and `ρ{a} > 0`, then `ρ^{∗3}{a³} ≥ ρ{a}³ > 0`, while `a³ = 1 ≠ g`.
-/

namespace OMA.P_mo_294245

open MeasureTheory OMA.S_mo_294245

/-- The cyclic group of order 3, written multiplicatively. -/
abbrev G := Multiplicative (ZMod 3)

instance : TopologicalSpace G := ⊥
instance : DiscreteTopology G := ⟨rfl⟩
instance : MeasurableSpace G := ⊤
instance : MeasurableSingletonClass G := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance : BorelSpace G := ⟨borel_eq_top_of_discrete.symm⟩
instance : IsTopologicalGroup G where
  continuous_mul := continuous_of_discreteTopology
  continuous_inv := continuous_of_discreteTopology
instance : MeasurableMul₂ G := ⟨measurable_of_countable _⟩

/-- The generator `g = ofAdd 1`; `g ≠ 1` and `g³ = 1`. -/
def g : G := Multiplicative.ofAdd 1

lemma cube_eq_one (a : G) : a * (a * a) = 1 := by
  revert a; decide

lemma g_ne_one : g ≠ 1 := by decide

/-- Lower bound for a convolution at a point. -/
lemma mconv_singleton_ge (μ ν : Measure G) [SFinite ν] (a b : G) :
    μ {a} * ν {b} ≤ (μ ∗ₘ ν) {a * b} := by
  rw [Measure.mconv, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← Measure.prod_prod]
  apply measure_mono
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  simp only [Set.mem_singleton_iff] at hx hy
  simp [hx, hy]

lemma exists_pos (ρ : Measure G) [IsProbabilityMeasure ρ] : ∃ a, 0 < ρ {a} := by
  by_contra h
  push Not at h
  have h0 : ∀ a, ρ {a} = 0 := fun a => nonpos_iff_eq_zero.mp (h a)
  have : ρ Set.univ = 0 := by
    rw [← Set.iUnion_of_singleton G]
    exact measure_iUnion_null h0
  simp at this

lemma convPow_three (ρ : Measure G) [SFinite ρ] :
    convPow ρ 3 = ρ ∗ₘ (ρ ∗ₘ ρ) := by
  simp only [convPow, Measure.mconv_dirac_one]

/-- `δ_g` has no probability cube root. -/
lemma no_cube_root (ρ : Measure G) [IsProbabilityMeasure ρ] : convPow ρ 3 ≠ Measure.dirac g := by
  intro h
  obtain ⟨a, ha⟩ := exists_pos ρ
  have h1 : ρ {a} * (ρ {a} * ρ {a}) ≤ convPow ρ 3 {a * (a * a)} := by
    rw [convPow_three]
    calc ρ {a} * (ρ {a} * ρ {a}) ≤ ρ {a} * (ρ ∗ₘ ρ) {a * a} := by
          gcongr; exact mconv_singleton_ge ρ ρ a a
      _ ≤ (ρ ∗ₘ (ρ ∗ₘ ρ)) {a * (a * a)} := mconv_singleton_ge ρ (ρ ∗ₘ ρ) a (a * a)
  rw [h, cube_eq_one, Measure.dirac_apply' _ (measurableSet_singleton _)] at h1
  have hg : g ∉ ({1} : Set G) := by simpa using g_ne_one
  rw [Set.indicator_of_notMem hg] at h1
  have hpos : 0 < ρ {a} * (ρ {a} * ρ {a}) :=
    ENNReal.mul_pos ha.ne' (ENNReal.mul_pos ha.ne' ha.ne').ne'
  exact absurd h1 (not_le.mpr hpos)

lemma convPow_dirac_one (k : ℕ) : convPow (Measure.dirac (1 : G)) k = Measure.dirac 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [convPow, ih, Measure.dirac_mconv_dirac, one_mul]

theorem solution :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : MeasurableSpace G) (_ : BorelSpace G) (μ ν : Measure G) (n : ℕ),
      IsInfDiv μ ∧ 1 ≤ n ∧ IsProbabilityMeasure ν ∧ convPow ν n = μ ∧ ¬ IsInfDiv ν := by
  refine ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Measure.dirac 1, Measure.dirac g, 3, ?_, by norm_num, inferInstance, ?_, ?_⟩
  · exact ⟨inferInstance, fun k _ => ⟨Measure.dirac 1, inferInstance, convPow_dirac_one k⟩⟩
  · simp only [convPow, Measure.mconv_dirac_one, Measure.dirac_mconv_dirac, cube_eq_one]
  · rintro ⟨_, h⟩
    obtain ⟨ρ, hρ, hρ3⟩ := h 3 (by norm_num)
    exact no_cube_root ρ (hρ3.trans (by rfl))

end OMA.P_mo_294245

theorem OMA.solution : type_of% @OMA.S_mo_294245.main := OMA.P_mo_294245.solution
