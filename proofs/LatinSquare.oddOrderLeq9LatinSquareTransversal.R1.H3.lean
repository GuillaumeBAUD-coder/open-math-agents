import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1

namespace OMA.LatinNormalize

/-- Permute rows and columns of a latin square: `(i, j) ↦ L (r i) (c j)`. -/
def reindex {n : ℕ} (L : LatinSquare n) (r c : Fin n ≃ Fin n) : LatinSquare n where
  mat := Matrix.of fun i j => L.mat (r i) (c j)
  row_injective := fun i a b h => c.injective (L.row_injective (r i) h)
  col_injective := fun j a b h => r.injective (L.col_injective (c j) h)

theorem normalize (n : ℕ) [NeZero n] (L : LatinSquare n) : ∃ M : LatinSquare n,
    (∀ i, M.mat 0 i = i) ∧ (∀ i, M.mat i 0 = i) ∧
    ((∃ σ, IsTransversal M σ) → ∃ σ, IsTransversal L σ) := by
  -- columns: symbol in row 0
  let ec : Fin n ≃ Fin n := Equiv.ofBijective (L.mat 0) (L.row_injective 0).bijective_of_finite
  let c := ec.symm
  -- rows: symbol in column `c 0`
  let er : Fin n ≃ Fin n :=
    Equiv.ofBijective (fun i => L.mat i (c 0)) (L.col_injective (c 0)).bijective_of_finite
  let r := er.symm
  have hr0 : r 0 = 0 := by
    apply er.injective
    simp only [r, Equiv.apply_symm_apply]
    show 0 = L.mat 0 (c 0)
    exact (ec.apply_symm_apply 0).symm
  refine ⟨reindex L r c, ?_, ?_, ?_⟩
  · intro j
    show L.mat (r 0) (c j) = j
    rw [hr0]
    exact ec.apply_symm_apply j
  · intro i
    show L.mat (r i) (c 0) = i
    exact er.apply_symm_apply i
  · rintro ⟨σ, hσ, hs⟩
    refine ⟨fun k => c (σ (er k)), ?_, ?_⟩
    · exact c.injective.comp (hσ.comp er.injective)
    · intro a b h
      have h' : L.mat (r (er a)) (c (σ (er a))) = L.mat (r (er b)) (c (σ (er b))) := by
        simpa [r] using h
      exact er.injective (hs h')

end OMA.LatinNormalize

theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1.H3 :=
  fun n _ L => OMA.LatinNormalize.normalize n L
