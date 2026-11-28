import OMAStatements.S_mo_16670

open OMA.S_mo_16670

namespace OMA.PerronZeroMatrices

private def indicator (n : ℕ) : Fin (n + 1) → ℝ := Pi.single 0 1

private theorem generated (n : ℕ) :
    generatedGroup (indicator n) = AddSubgroup.closure ({1} : Set ℝ) := by
  unfold generatedGroup
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hone : (1 : ℝ) ∈ AddSubgroup.closure ({1} : Set ℝ) :=
      AddSubgroup.subset_closure (Set.mem_singleton 1)
    by_cases hi : i = 0
    · simp [indicator, hi, hone]
    · simp [indicator, hi]
  · rw [AddSubgroup.closure_le]
    intro y hy
    have hy' : y = 1 := Set.mem_singleton_iff.mp hy
    subst y
    apply AddSubgroup.subset_closure
    exact ⟨0, by simp [indicator]⟩

private theorem perron (n : ℕ) :
    probabilityPerron (0 : NatMatrix (n + 1)) 0 (indicator n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simp [indicator]
    · simp [indicator, hi]
  · simp [indicator]
  · rw [Matrix.map_zero _ (by simp)]
    simp
  · intro z hz
    rw [Matrix.map_zero _ (by simp), sub_zero, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at hz
    have hz0 : z = 0 := by
      by_contra hne
      exact (pow_ne_zero _ hne) hz
    simp [hz0]

end OMA.PerronZeroMatrices

open OMA.PerronZeroMatrices in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_16670.main) := by
  intro h
  have hfinite := h 1 0 0 (indicator 0) (perron 0)
  let f (n : ℕ) : Σ k : ℕ, NatMatrix k := ⟨n + 1, 0⟩
  have hf : Function.Injective f := by
    intro n m hnm
    exact Nat.succ.inj (congrArg Sigma.fst hnm)
  apply (Set.infinite_range_of_injective hf)
  apply hfinite.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨indicator n, perron n, (generated n).trans (generated 0).symm⟩