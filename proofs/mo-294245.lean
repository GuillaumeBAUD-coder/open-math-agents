import OMAStatements.S_mo_294245

open MeasureTheory OMA.S_mo_294245
open scoped ENNReal

theorem OMA.solution : type_of% @OMA.S_mo_294245.main := by
  let G := Multiplicative (ZMod 2)
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  let _ : MeasurableSpace G := borel G
  let _ : BorelSpace G := ⟨rfl⟩
  let g : G := Multiplicative.ofAdd (1 : ZMod 2)
  have hg : g ≠ 1 := by decide
  have hsquare (x : G) : x * x = 1 := by
    change Multiplicative.ofAdd (Multiplicative.toAdd x + Multiplicative.toAdd x) =
      Multiplicative.ofAdd (0 : ZMod 2)
    congr 1
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hid (k : ℕ) : convPow (Measure.dirac (1 : G)) k = Measure.dirac 1 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [convPow, ih]
  refine ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Measure.dirac 1, Measure.dirac g, 2, ⟨inferInstance, ?_⟩, by decide, inferInstance, ?_, ?_⟩
  · exact fun k _ => ⟨Measure.dirac 1, inferInstance, hid k⟩
  · simp [convPow, hsquare]
  · intro hinf
    obtain ⟨ρ, hρ, hroot⟩ := hinf.2 2 (by decide)
    let _ : IsProbabilityMeasure ρ := hρ
    have hconv : ρ.mconv ρ = Measure.dirac g := by
      simpa [convPow] using hroot
    have hmass (x : G) : ρ {x} = 0 := by
      have hsub : ({x} : Set G) ×ˢ ({x} : Set G) ⊆
          (fun z : G × G => z.1 * z.2) ⁻¹' ({1} : Set G) := by
        rintro ⟨u, v⟩ huv
        have hu : u = x := huv.1
        have hv : v = x := huv.2
        subst u
        subst v
        exact hsquare x
      have hle := measure_mono (μ := ρ.prod ρ) hsub
      rw [Measure.prod_prod, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hle
      change ρ {x} * ρ {x} ≤ ρ.mconv ρ {1} at hle
      rw [hconv, Measure.dirac_apply' _ (measurableSet_singleton _)] at hle
      simp [hg, mul_eq_zero] at hle
      exact hle
    have hzero : ρ Set.univ = 0 := by
      rw [show Set.univ = ⋃ x : G, ({x} : Set G) by ext; simp]
      exact measure_iUnion_null hmass
    simp at hzero