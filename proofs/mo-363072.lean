import OMAStatements.S_mo_363072
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic

namespace OptimalAssignment

variable {n : ℕ}
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

private noncomputable def pairing (B : Mat n) : Mat n →ₗ[ℝ] ℝ where
  toFun M := ∑ i, ∑ j, M i j * B i j
  map_add' M N := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a M := by simp [mul_assoc, Finset.mul_sum]

private theorem pairing_perm (B : Mat n) (σ : Equiv.Perm (Fin n)) :
    pairing B (σ.permMatrix ℝ) = ∑ i, B i (σ i) := by
  change (∑ i, ∑ j, (σ.permMatrix ℝ) i j * B i j) = _
  simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, ite_mul]

/-- The assignment bound holds for every real weight matrix B. The stochastic
matrix used in the proof is the normalized difference between the maximizing
permutation matrix and the given zero-line-sum direction. -/
theorem nonnegative {A B : Mat n}
    (hrow : ∀ i, ∑ j, A i j = 0) (hcol : ∀ j, ∑ i, A i j = 0)
    (σ : Equiv.Perm (Fin n)) (hon : ∀ i, 0 ≤ A i (σ i))
    (hoff : ∀ i j, j ≠ σ i → A i j ≤ 0)
    (hmax : ∀ τ : Equiv.Perm (Fin n), ∑ i, B i (τ i) ≤ ∑ i, B i (σ i)) :
    0 ≤ ∑ i, ∑ j, A i j * B i j := by
  classical
  let s := ∑ i, A i (σ i)
  let P := σ.permMatrix ℝ
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ => hon i
  have hp : P ∈ doublyStochastic ℝ (Fin n) := permMatrix_mem_doublyStochastic
  obtain ⟨C, hC, heq⟩ : ∃ C ∈ doublyStochastic ℝ (Fin n), s • P - A = s • C := by
    apply (exists_mem_doublyStochastic_eq_smul_iff hs).2
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : j = σ i
      · subst j
        have hi : A i (σ i) ≤ s := Finset.single_le_sum (fun k _ => hon k) (Finset.mem_univ i)
        simpa [P, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, sub_nonneg] using hi
      · simpa [P, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, h, Ne.symm h] using hoff i j h
    · intro i
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, sum_row_of_mem_doublyStochastic hp]
    · intro j
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hcol, sum_col_of_mem_doublyStochastic hp]
  obtain ⟨w, hw, hsum, hcomb⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hC
  have hbound : pairing B C ≤ pairing B P := by
    rw [← hcomb, map_sum]
    simp only [map_smul, smul_eq_mul, P, pairing_perm]
    calc
      _ ≤ ∑ τ, w τ * ∑ i, B i (σ i) := Finset.sum_le_sum fun τ _ =>
        mul_le_mul_of_nonneg_left (hmax τ) (hw τ)
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]
  have hpairs := congrArg (pairing B) heq
  simp only [map_sub, map_smul, smul_eq_mul] at hpairs
  change 0 ≤ pairing B A
  linarith [mul_le_mul_of_nonneg_left hbound hs]

end OptimalAssignment

theorem OMA.solution : type_of% @OMA.S_mo_363072.main := by
  intro n A B hrow hcol _ σ hon hoff hmax
  exact OptimalAssignment.nonnegative hrow hcol σ hon hoff hmax
