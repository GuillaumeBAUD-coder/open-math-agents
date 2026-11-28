import OMAStatements.S_mo_363072
import Mathlib.Analysis.Convex.Birkhoff

open Finset
theorem OMA.solution : type_of% @OMA.S_mo_363072.main := by
  intro n A B hrow hcol hB σ hon hoff hmax
  classical
  set m : ℝ := 1 + ∑ i, A i (σ i) with hm
  have hdiag : ∀ i, A i (σ i) ≤ ∑ k, A k (σ k) :=
    fun i => single_le_sum (f := fun k => A k (σ k)) (fun k _ => hon k) (mem_univ i)
  have hsum0 : 0 ≤ ∑ k, A k (σ k) := sum_nonneg (fun k _ => hon k)
  have mpos : 0 < m := by rw [hm]; linarith
  let S : Matrix (Fin n) (Fin n) ℝ := fun i j => (if j = σ i then 1 else 0) - A i j / m
  have hS : S ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : j = σ i
      · subst h
        have := hdiag i
        simp only [S, if_true]
        rw [sub_nonneg, div_le_one mpos]; rw [hm]; linarith
      · simp only [S, h, if_false]
        have := hoff i j h
        have : A i j / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg this mpos.le
        linarith
    · intro i
      simp only [S, sum_sub_distrib, ← sum_div, hrow i]
      simp
    · intro j
      simp only [S, sum_sub_distrib, ← sum_div, hcol j]
      have e : ∀ x, (j = σ x) ↔ (σ.symm j = x) := fun x => (Equiv.symm_apply_eq σ).symm
      simp only [e, sum_ite_eq, mem_univ, if_true]
      simp
  have hle : ∑ i, ∑ j, S i j * B i j ≤ ∑ i, B i (σ i) := by
    obtain ⟨w, hw0, hw1, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
    have hSij : ∀ i j, S i j = ∑ τ, w τ * (if τ i = j then 1 else 0) := by
      intro i j
      have := congrFun (congrFun hw3 i) j
      rw [← this]
      simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have h1 : ∀ i, ∑ j, S i j * B i j = ∑ τ, w τ * B i (τ i) := by
      intro i
      simp only [hSij, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun τ _ => ?_
      simp [ite_mul, sum_ite_eq]
    have h2 : ∑ i, ∑ j, S i j * B i j = ∑ τ, w τ * ∑ i, B i (τ i) := by
      simp only [h1]
      rw [sum_comm]
      refine sum_congr rfl fun τ _ => ?_
      rw [mul_sum]
    rw [h2]
    calc ∑ τ, w τ * ∑ i, B i (τ i) ≤ ∑ τ, w τ * ∑ i, B i (σ i) :=
          sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hmax τ) (hw0 τ)
      _ = ∑ i, B i (σ i) := by rw [← sum_mul, hw1, one_mul]
  have key : ∑ i, ∑ j, A i j * B i j = m * (∑ i, B i (σ i) - ∑ i, ∑ j, S i j * B i j) := by
    have e : ∑ i, ∑ j, S i j * B i j = ∑ i, B i (σ i) - (∑ i, ∑ j, A i j * B i j) / m := by
      simp only [S, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
        sum_ite_eq', mem_univ, if_true, div_mul_eq_mul_div, ← sum_div]
    rw [e]
    field_simp
    ring
  rw [key]
  exact mul_nonneg mpos.le (by linarith)
