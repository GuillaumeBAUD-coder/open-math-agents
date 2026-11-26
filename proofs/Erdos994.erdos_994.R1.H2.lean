import OMAReductions.R_Erdos994_erdos_994_R1

-- Credit: @steveDOTdigital

open Filter MeasureTheory Set
open scoped ENNReal

theorem OMA.solution : OMA.R_Erdos994_erdos_994_R1.H2 := by
  intro B hB hmeas mass vanish
  let U (n : ℕ) := ⋃ j ≥ n, B j
  have anti : Antitone U := by
    intro m n hmn x hx
    obtain ⟨j, hj, hb⟩ := mem_iUnion₂.1 hx
    exact mem_iUnion₂.2 ⟨j, hmn.trans hj, hb⟩
  have bounded : U 0 ⊆ Ioo 0 1 := by
    intro x hx
    obtain ⟨j, _, hb⟩ := mem_iUnion₂.1 hx
    exact hB j hb
  have finite : volume (U 0) ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono bounded)
  have low : (2 : ℝ≥0∞)⁻¹ ≤ volume (⋂ n, U n) := by
    rw [anti.measure_iInter (fun n => (MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => hmeas j).nullMeasurableSet) ⟨0,finite⟩]
    apply le_iInf
    intro n
    exact (mass n).trans (measure_mono (fun x hx => mem_iUnion₂.2 ⟨n,le_rfl,hx⟩))
  have null : volume (⋂ n, U n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.2
    filter_upwards [vanish] with x h
    obtain ⟨N, hN⟩ := eventually_atTop.1 h
    intro hx
    obtain ⟨j, hj, hb⟩ := mem_iUnion₂.1 (mem_iInter.1 hx N)
    exact hN j hj hb
  rw [null] at low
  norm_num at low
