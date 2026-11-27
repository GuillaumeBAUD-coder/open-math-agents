import OMAReductions.R_PartitionParity_subbarao_even_R1
import Mathlib

-- Step PartitionParity.subbarao.even.R1.H2: hypothesis H2 of reduction PartitionParity.subbarao.even.R1
-- Credit: @ivillar

/-!
If `S` were finite, its counting function would be bounded by `|S|`, so `√X = O(1)`; but
`√X → ∞`.
-/

open Filter Asymptotics in
theorem OMA.solution : OMA.R_PartitionParity_subbarao_even_R1.H2 := by
  unfold OMA.R_PartitionParity_subbarao_even_R1.H2
  intro S hS
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨C, hC⟩ := hS.bound
  have hcount : ∀ X : ℝ, ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) ≤ S.ncard := by
    intro X
    have h : {n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S} ⊆ S := fun n (hn : (n : ℝ) ≤ X ∧ n ∈ S) => hn.2
    exact_mod_cast Set.ncard_le_ncard h hfin
  have hsq : Tendsto (fun X : ℝ => Real.sqrt X) atTop atTop := by
    simpa using Real.tendsto_sqrt_atTop
  obtain ⟨X, hX1, hX2⟩ := ((hC.and (hsq.eventually_gt_atTop (|C| * S.ncard)))).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _)] at hX1
  have h1 : C * ({n : ℕ | (n : ℝ) ≤ X ∧ n ∈ S}.ncard : ℝ) ≤ |C| * S.ncard :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left (hcount X) (abs_nonneg C))
  linarith
