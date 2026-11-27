import OMAReductions.R_PartitionParity_subbarao_even_R1

-- Step PartitionParity.subbarao.even.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_PartitionParity_subbarao_even_R1.H2 := by
  intro S hO hfin
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hC
  let M : ℝ := max C 0 * (S.ncard : ℝ) + 1
  have hMpos : 0 < M := by positivity
  let X : ℝ := max X₀ (M ^ 2)
  have hX0 : X₀ ≤ X := le_max_left _ _
  have hXM : M ^ 2 ≤ X := le_max_right _ _
  have hbound := hX₀ X hX0
  have hsqrt_nonneg : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hcard_nonneg : (0 : ℝ) ≤ ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hsqrt_nonneg, Real.norm_of_nonneg hcard_nonneg] at hbound
  have hsub : {n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S} ⊆ S := fun _ h => h.2
  have hcard_le : ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) ≤ (S.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have hC_le : C * ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) ≤ max C 0 * (S.ncard : ℝ) := by
    calc C * ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ)
        ≤ max C 0 * ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) hcard_nonneg
      _ ≤ max C 0 * (S.ncard : ℝ) :=
          mul_le_mul_of_nonneg_left hcard_le (le_max_right C 0)
  have hsqrt_ge : M ≤ Real.sqrt X := by
    rw [← Real.sqrt_sq hMpos.le]
    exact Real.sqrt_le_sqrt hXM
  linarith
