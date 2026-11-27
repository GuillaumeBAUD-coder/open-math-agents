import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1

-- Step LatinSquare.oddOrderLeq9LatinSquareTransversal.R1.H3
-- Credit: @caa1982

open LatinSquare

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H3 := by
  intro n _ L
  let π : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (L.mat 0) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨L.row_injective 0, rfl⟩)
  have hcol_inj : Function.Injective (fun i : Fin n => π.symm (L.mat i 0)) :=
    π.symm.injective.comp (L.col_injective 0)
  let ρ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun i : Fin n => π.symm (L.mat i 0))
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hcol_inj, rfl⟩)
  have hρ0 : ρ 0 = 0 := by
    change π.symm (L.mat 0 0) = 0
    have hπ0 : π 0 = L.mat 0 0 := rfl
    rw [← hπ0, π.symm_apply_apply]
  have hρsymm0 : ρ.symm 0 = 0 := (Equiv.symm_apply_eq ρ).mpr hρ0.symm
  let M : LatinSquare n :=
    { mat := Matrix.of fun i j => π.symm (L.mat (ρ.symm i) j)
      row_injective := fun i => by
        intro j₁ j₂ h
        simp only [Matrix.of_apply] at h
        exact L.row_injective (ρ.symm i) (π.symm.injective h)
      col_injective := fun j => by
        intro i₁ i₂ h
        simp only [Matrix.transpose_apply, Matrix.of_apply] at h
        exact ρ.symm.injective (L.col_injective j (π.symm.injective h)) }
  refine ⟨M, ?_, ?_, ?_⟩
  · intro j
    simp only [M, Matrix.of_apply, hρsymm0]
    exact π.symm_apply_apply j
  · intro i
    simp only [M, Matrix.of_apply]
    change ρ (ρ.symm i) = i
    exact ρ.apply_symm_apply i
  · rintro ⟨σ, hσ_inj, hσ_sym⟩
    refine ⟨fun i => σ (ρ i), hσ_inj.comp ρ.injective, ?_⟩
    intro i₁ i₂ h
    have h1 : M.mat (ρ i₁) (σ (ρ i₁)) = M.mat (ρ i₂) (σ (ρ i₂)) := by
      simp only [M, Matrix.of_apply, ρ.symm_apply_apply]
      exact congrArg π.symm h
    exact ρ.injective (hσ_sym h1)
