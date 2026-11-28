import OMAStatements.S_mo_178688
import Mathlib

-- Problem: mo-178688, for rationally independent reals x_1..x_n the sums of p of them
-- (with repetition) determine the multiset of summands.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- A linearly independent family is injective. If two multiplicity vectors u, v give the same
-- sum then the rational combination with coefficients u_i - v_i vanishes, so u = v.

open OMA.S_mo_178688 in
theorem OMA.solution : type_of% @OMA.S_mo_178688.main := by
  intro n x hx
  refine ⟨hx.injective, ?_⟩
  intro p u v _ _ h
  unfold combinationSum at h
  have h' : ∑ i, ((u i : ℝ) - (v i : ℝ)) * x i = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  have hsum : ∑ i, ((u i : ℚ) - (v i : ℚ)) • x i = 0 := by
    rw [← h']
    apply Finset.sum_congr rfl
    intro i _
    first
      | (rw [Rat.smul_def]; push_cast; ring)
      | (rw [Rat.smul_def]; push_cast)
      | simp [Rat.smul_def]
  have hzero := Fintype.linearIndependent_iff.mp hx (fun i => (u i : ℚ) - (v i : ℚ)) hsum
  funext i
  have hi : (u i : ℚ) - (v i : ℚ) = 0 := hzero i
  have hq : (u i : ℚ) = (v i : ℚ) := by linarith
  exact_mod_cast hq
