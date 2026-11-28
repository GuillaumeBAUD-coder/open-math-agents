import OMAStatements.S_mo_142767

-- Problem: strong convergence sufficient conditions
-- Upstream: formal-conjectures statements/mo-142767.lean:0 (declaration OMA.S_mo_142767.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_142767.main) := by
  intro h
  have hx : Tendsto (fun n : ℕ => (fun _ : Fin 1 => (1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 (0 : Fin 1 → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := h 1 (fun n => Measure.dirac (fun _ => (1 : ℝ) / ((n : ℝ) + 1))) (Measure.dirac 0) (by
    intro f hf
    simp only [integral_dirac]
    exact (hf.continuous.tendsto 0).comp hx)
  have h2 := h1 {0} (measurableSet_singleton 0)
  have h3 : ∀ n : ℕ, (Measure.dirac (fun _ : Fin 1 => (1 : ℝ) / ((n : ℝ) + 1))) ({0} : Set (Fin 1 → ℝ)) = 0 := by
    intro n
    rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]
    have hne : (fun _ : Fin 1 => (1 : ℝ) / ((n : ℝ) + 1)) ≠ 0 := by
      intro he
      have := congrFun he 0
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [Pi.zero_apply] at this
      linarith
    exact Set.indicator_of_notMem (s := ({0} : Set (Fin 1 → ℝ))) (fun hm => hne hm) (1 : (Fin 1 → ℝ) → ℝ≥0∞)
  simp only [h3] at h2
  have h4 : (Measure.dirac (0 : Fin 1 → ℝ)) ({0} : Set (Fin 1 → ℝ)) = 1 := by
    simp
  rw [h4] at h2
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h2)
