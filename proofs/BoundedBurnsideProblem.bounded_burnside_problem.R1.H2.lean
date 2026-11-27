import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

/-! A quotient of the finitely generated group FreeGroup (Fin 2) is finitely generated, and
the class of x raised to n is the class of x^n, which lies in the normal closure of the
n-th powers. -/

theorem OMA.solution : OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1.H2 := by
  intro n
  refine ⟨inferInstance, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨x, rfl⟩
