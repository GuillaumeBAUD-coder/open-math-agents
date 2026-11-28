import OMAReductions.R_wp_rokhlin_s_R1
import Mathlib

open MeasureTheory Filter Topology

theorem OMA.solution : OMA.R_wp_rokhlin_s_R1.H1 := by
  intro X _ μ _ T hT hmix k hk d hd A hA
  have hpres : ∀ n (s : Set X), MeasurableSet s → μ ((T^[n]) ⁻¹' s) = μ s :=
    fun n s hs => (hT.iterate n).measure_preimage hs.nullMeasurableSet
  interval_cases k
  · simp
  · have h1 : ∀ r, (⋂ i, (T^[d r i]) ⁻¹' A i) = (T^[d r 0]) ⁻¹' A 0 := by
      intro r; ext x; simp [Fin.forall_fin_one]
    simp only [h1, hpres _ _ (hA 0)]
    simp
  · have hlim : Tendsto (fun r => d r 1 - d r 0) atTop atTop :=
      tendsto_atTop_mono (fun r => by have := hd r 0 1 (by decide); simp only [id]; omega) tendsto_id
    have h2 := (hmix (A 0) (A 1) (hA 0) (hA 1)).comp hlim
    have h3 : ∀ r, μ (⋂ i, (T^[d r i]) ⁻¹' A i) = μ (A 0 ∩ (T^[d r 1 - d r 0]) ⁻¹' A 1) := by
      intro r
      have hlt := hd r 0 1 (by decide)
      rw [← hpres (d r 0) _ ((hA 0).inter ((T.measurable.iterate _) (hA 1)))]
      congr 1
      ext x
      simp only [Set.mem_iInter, Fin.forall_fin_two, Set.mem_preimage, Set.mem_inter_iff]
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    simp only [h3, Fin.prod_univ_two]
    exact h2
