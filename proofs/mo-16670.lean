import OMAStatements.S_mo_16670

/-!
# Infinitely many compatible nilpotent matrices

Combines @Genbox's zero-eigenvalue counterexample (PR #26456) with the
fixed-dimension construction in @etaubman's companion to statement PR #20521,
commit e7841e8447179c0c9145f381d47c478bee740d2d. The nilpotent family below
has the same probability eigenvector in dimension two. The registered
statement cites Pavel Etingof's related zero-padding counterexample.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_16670.main) := by
  intro h
  let B (m : ℕ) : OMA.S_mo_16670.NatMatrix 2 := !![0, m; 0, 0]
  let v : Fin 2 → ℝ := ![1, 0]
  have hp (m : ℕ) : OMA.S_mo_16670.probabilityPerron (B m) 0 v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num [v]
    · norm_num [v, Fin.sum_univ_two]
    · ext i
      fin_cases i <;>
        norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, B, v]
    · intro z hz
      have hz' : z ^ 2 = 0 := by
        simpa [Matrix.det_fin_two, Matrix.map_apply, B, pow_two] using hz
      simp [eq_zero_of_pow_eq_zero hz']
  let f (m : ℕ) : Σ k : ℕ, OMA.S_mo_16670.NatMatrix k := ⟨2, B m⟩
  have hf : Function.Injective f := by
    intro m n hmn
    have heq : B m = B n := eq_of_heq (Sigma.mk.inj_iff.mp hmn).2
    simpa [B] using congrArg (fun C => C 0 1) heq
  apply Set.infinite_range_of_injective hf
  apply (h 2 (B 0) 0 v (hp 0)).subset
  rintro _ ⟨m, rfl⟩
  exact ⟨v, hp m, rfl⟩
