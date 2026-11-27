import OMAReductions.R_Erdos298_erdos_298_variants_natural_density_R1

-- Step Erdos298.erdos_298.variants.natural_density.R1.H3: hypothesis H3 of reduction Erdos298.erdos_298.variants.natural_density.R1

/-!
If the partial densities of `A` converge to `α > 0`, their limsup, which is the upper density, is
also `α`.
-/

theorem OMA.solution : OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H3 := by
  unfold OMA.R_Erdos298_erdos_298_variants_natural_density_R1.H3
  intro A hA
  obtain ⟨α, hα, hd⟩ := hA
  have h : Filter.limsup (fun b : ℕ => A.partialDensity Set.univ b) Filter.atTop = α :=
    Filter.Tendsto.limsup_eq hd
  have h2 : A.upperDensity = α := h
  rw [h2]
  exact hα
