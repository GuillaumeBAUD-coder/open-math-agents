import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

-- Step BoundedBurnsideProblem.bounded_burnside_problem.R1.H2: hypothesis H2 of reduction BoundedBurnsideProblem.bounded_burnside_problem.R1
-- Credit: @luciusacarr

theorem OMA.solution : OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1.H2 := by
  intro n
  refine ⟨?_, ?_⟩
  · exact Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  · intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.subset_normalClosure ⟨x, rfl⟩
