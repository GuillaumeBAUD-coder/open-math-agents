import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1

-- Step Erdos406.erdos_406.variants.one_two.R1.H1: hypothesis H1 of reduction Erdos406.erdos_406.variants.one_two.R1
-- Credit: @Ciphore
-- H1 := ∀ k : ℕ, 15 < k → k ≤ 1000 → ¬ Nat.digits 3 (2 ^ k) ⊆ [1, 2]

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 1000000 in
theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1.H1 := by
  have key : ∀ k ∈ Finset.Icc 16 1000, ¬ Nat.digits 3 (2 ^ k) ⊆ [1, 2] := by
    decide +kernel
  intro k h15 h1000
  exact key k (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
