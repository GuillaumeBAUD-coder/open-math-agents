import OMAReductions.R_Erdos373_erdos_373_variants_maximal_solution_R1

-- Step Erdos373.erdos_373.variants.maximal_solution.R1.H1: hypothesis H1 of reduction Erdos373.erdos_373.variants.maximal_solution.R1
-- Credit: @JamesSlash. 16! = 14! * 5! * 2!, the list is non-increasing, 14 < 15 and all entries exceed 1.

theorem OMA.solution : OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1.H1 := by
  unfold OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1.H1
  simp only [Erdos373.S, Set.mem_ofPred_eq]
  decide
