import OMAReductions.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1
import Mathlib

/-! Step H1 of the reduction of the invariant subspace problem: eigenlines and range closures. -/

-- Step InvariantSubspaceProblem.Invariant_subspace_problem.R1.H1: hypothesis H1 of reduction InvariantSubspaceProblem.Invariant_subspace_problem.R1
-- Credit: @ivillar
-- If T - z is not injective, the line through an eigenvector is invariant, and it is proper
-- because the first two coordinate vectors are not both multiples of one vector. If T - z is
-- injective with nondense range, the closure of its range is invariant because T commutes
-- with T - z, it is not everything, and it is nonzero because T - z is injective.

open scoped lp
open InvariantSubspaceProblem

theorem OMA.solution : OMA.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1.H1 := by
  intro T z h
  set S : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) := T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ) with hS
  have hSapp : ∀ x, S x = T x - z • x := fun x => by simp [hS]
  have hcomm : ∀ x, T (S x) = S (T x) := fun x => by
    rw [hSapp, hSapp, map_sub, map_smul]
  by_cases hinj : Function.Injective S
  · have hnd : ¬ DenseRange S := by
      rcases h with h | h
      · exact absurd hinj h
      · exact h
    refine ⟨⟨(LinearMap.range S.toLinearMap).topologicalClosure, ?_, ?_,
      Submodule.isClosed_topologicalClosure _, ?_⟩⟩
    · intro hbot
      have e0 : (lp.single 2 (0 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 0) h0
        simp at h1
      have hmem : S (lp.single 2 (0 : ℕ) (1 : ℂ)) ∈
          (LinearMap.range S.toLinearMap).topologicalClosure :=
        Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
      rw [hbot, Submodule.mem_bot] at hmem
      exact e0 (hinj (hmem.trans (map_zero S).symm))
    · intro htop
      apply hnd
      have hd : Dense ((LinearMap.range S.toLinearMap : Submodule ℂ ℓ²(ℕ, ℂ)) : Set ℓ²(ℕ, ℂ)) :=
        (Submodule.dense_iff_topologicalClosure_eq_top).mpr htop
      exact hd
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · rintro y ⟨x, rfl⟩
        show T (S x) ∈ (LinearMap.range S.toLinearMap).topologicalClosure
        rw [hcomm]
        exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
      · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  · obtain ⟨x, y, hxy, hne⟩ : ∃ x y, S x = S y ∧ x ≠ y := by
      by_contra hcon
      apply hinj
      intro x y hxy
      by_contra hne
      exact hcon ⟨x, y, hxy, hne⟩
    have hv0 : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hSv : S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hTv : T (x - y) = z • (x - y) := by
      have h1 := hSapp (x - y)
      rw [hSv] at h1
      exact sub_eq_zero.mp h1.symm
    refine ⟨⟨Submodule.span ℂ {x - y}, ?_, ?_, Submodule.closed_of_finiteDimensional _, ?_⟩⟩
    · rw [Ne, Submodule.span_singleton_eq_bot]
      exact hv0
    · intro htop
      have h0 : (lp.single 2 (0 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈ Submodule.span ℂ {x - y} :=
        htop ▸ Submodule.mem_top
      have h1 : (lp.single 2 (1 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈ Submodule.span ℂ {x - y} :=
        htop ▸ Submodule.mem_top
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
      have ha0 : a * (x - y : ℓ²(ℕ, ℂ)) 0 = 1 := by
        have h2 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 0) ha
        have h3 : (lp.single 2 (0 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) 0 = 1 := lp.single_apply_self 2 0 1
        exact h2.trans h3
      have ha1 : a * (x - y : ℓ²(ℕ, ℂ)) 1 = 0 := by
        have h2 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 1) ha
        have h3 : (lp.single 2 (0 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) 1 = 0 :=
          lp.single_apply_ne 2 0 1 (by norm_num)
        exact h2.trans h3
      have hb1 : b * (x - y : ℓ²(ℕ, ℂ)) 1 = 1 := by
        have h2 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 1) hb
        have h3 : (lp.single 2 (1 : ℕ) (1 : ℂ) : ℓ²(ℕ, ℂ)) 1 = 1 := lp.single_apply_self 2 1 1
        exact h2.trans h3
      have hane : a ≠ 0 := by
        rintro rfl
        rw [zero_mul] at ha0
        exact zero_ne_one ha0
      have hv1 : (x - y : ℓ²(ℕ, ℂ)) 1 = 0 := by
        rcases mul_eq_zero.mp ha1 with h2 | h2
        · exact absurd h2 hane
        · exact h2
      rw [hv1, mul_zero] at hb1
      exact zero_ne_one hb1
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      show T (x - y) ∈ Submodule.span ℂ {x - y}
      rw [hTv]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
