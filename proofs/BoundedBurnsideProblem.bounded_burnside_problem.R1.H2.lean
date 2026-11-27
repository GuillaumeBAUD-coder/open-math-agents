import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

-- Step BoundedBurnsideProblem.bounded_burnside_problem.R1.H2
-- Credit: @caa1982

private lemma freeGroup_fin2_fg : Group.FG (FreeGroup (Fin 2)) := by
  refine ⟨Finset.univ.image FreeGroup.of, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact FreeGroup.closure_range_of (Fin 2)

theorem OMA.solution : OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1.H2 := by
  intro n
  let N : Subgroup (FreeGroup (Fin 2)) :=
    Subgroup.normalClosure {y : FreeGroup (Fin 2) | ∃ x : FreeGroup (Fin 2), y = x ^ n}
  constructor
  · have : Group.FG (FreeGroup (Fin 2)) := freeGroup_fin2_fg
    exact Group.fg_of_surjective (QuotientGroup.mk'_surjective N)
  · intro g
    refine QuotientGroup.induction_on g fun x => ?_
    change (QuotientGroup.mk' N x) ^ n = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩
