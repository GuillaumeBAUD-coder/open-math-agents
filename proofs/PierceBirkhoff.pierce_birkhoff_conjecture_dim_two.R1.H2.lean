import OMAReductions.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1

theorem OMA.solution : OMA.R_PierceBirkhoff_pierce_birkhoff_conjecture_dim_two_R1.H2 := by
  intro f ι P g q hfin hclosed hcover hdiag hmaj hmin hpiece x
  have hx : x ∈ ⋃ i, P i := by rw [hcover]; trivial
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  haveI : Nonempty ι := ⟨k⟩
  apply le_antisymm
  · refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
    refine le_ciInf fun j => ?_
    rw [hpiece k x hk]
    exact hmaj k j x hk
  · refine ciSup_le fun i => ?_
    refine le_trans (ciInf_le (Set.finite_range _).bddBelow k) ?_
    rw [hpiece k x hk]
    exact hmin i k x hk
