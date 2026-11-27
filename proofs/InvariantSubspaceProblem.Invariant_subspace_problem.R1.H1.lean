import OMAReductions.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1

-- Step InvariantSubspaceProblem.Invariant_subspace_problem.R1.H1: hypothesis H1 of reduction InvariantSubspaceProblem.Invariant_subspace_problem.R1
-- Credit: @luciusacarr

/-! Let `A = T - z • id`. If `A = 0`, the line through `e₀` is invariant. Otherwise `ker A`
(when `A` is not injective) or the closure of `range A` (when `A` does not have dense range) is a
nontrivial closed subspace, invariant because `T` commutes with `A`. -/

open scoped lp
open InvariantSubspaceProblem

namespace OMA.InvariantSubspaceH1

theorem scalar_case (T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) (z : ℂ) (hT : ∀ x, T x = z • x) :
    Nonempty (ClosedInvariantSubspace T) := by
  have hv : (lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ)) ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 0) h
    simp at h0
  refine ⟨⟨Submodule.span ℂ {(lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ))}, ?_, ?_,
    Submodule.closed_of_finiteDimensional _, ?_⟩⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]
    exact hv
  · intro htop
    have hw : (lp.single 2 1 (1 : ℂ) : ℓ²(ℕ, ℂ)) ∈
        Submodule.span ℂ {(lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ))} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    have h1 := congrArg (fun f : ℓ²(ℕ, ℂ) => f 1) hc
    simp at h1
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show T (lp.single 2 0 (1 : ℂ)) ∈ Submodule.span ℂ {(lp.single 2 0 (1 : ℂ) : ℓ²(ℕ, ℂ))}
    rw [hT]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem commute_case (T A : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) (hcomm : ∀ x, A (T x) = T (A x))
    (hA0 : A ≠ 0) (h : ¬ Function.Injective A ∨ ¬ DenseRange A) :
    Nonempty (ClosedInvariantSubspace T) := by
  rcases h with hinj | hdense
  · refine ⟨⟨LinearMap.ker A.toLinearMap, ?_, ?_, A.isClosed_ker, ?_⟩⟩
    · intro hb
      apply hinj
      intro x y hxy
      have hk : x - y ∈ LinearMap.ker A.toLinearMap := by
        show A (x - y) = 0
        rw [map_sub, hxy, sub_self]
      rw [hb, Submodule.mem_bot, sub_eq_zero] at hk
      exact hk
    · intro ht
      apply hA0
      refine ContinuousLinearMap.ext fun x => ?_
      have hk : x ∈ LinearMap.ker A.toLinearMap := by
        rw [ht]
        exact Submodule.mem_top
      have hk' : A x = 0 := hk
      simp [hk']
    · rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : A x = 0 := hx
      show A (T x) = 0
      rw [hcomm, hx', map_zero]
  · refine ⟨⟨(LinearMap.range A.toLinearMap).topologicalClosure, ?_, ?_,
      Submodule.isClosed_topologicalClosure _, ?_⟩⟩
    · intro hb
      apply hA0
      refine ContinuousLinearMap.ext fun x => ?_
      have hk : A x ∈ (LinearMap.range A.toLinearMap).topologicalClosure :=
        Submodule.le_topologicalClosure _ (LinearMap.mem_range_self A.toLinearMap x)
      rw [hb, Submodule.mem_bot] at hk
      simp [hk]
    · intro ht
      apply hdense
      intro x
      have hk : x ∈ (LinearMap.range A.toLinearMap).topologicalClosure := by
        rw [ht]
        exact Submodule.mem_top
      have hk' : x ∈ ((LinearMap.range A.toLinearMap).topologicalClosure : Set ℓ²(ℕ, ℂ)) := hk
      simpa [Submodule.topologicalClosure_coe, LinearMap.coe_range] using hk'
    · calc Submodule.map T.toLinearMap (LinearMap.range A.toLinearMap).topologicalClosure
          ≤ (Submodule.map T.toLinearMap (LinearMap.range A.toLinearMap)).topologicalClosure :=
            Submodule.topologicalClosure_map T _
        _ ≤ (LinearMap.range A.toLinearMap).topologicalClosure := by
            apply Submodule.topologicalClosure_mono
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
            obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hw
            exact LinearMap.mem_range.mpr ⟨T x, hcomm x⟩

end OMA.InvariantSubspaceH1

theorem OMA.solution : OMA.R_InvariantSubspaceProblem_Invariant_subspace_problem_R1.H1 := by
  intro T z h
  by_cases hA0 : T - z • ContinuousLinearMap.id ℂ ℓ²(ℕ, ℂ) = 0
  · refine OMA.InvariantSubspaceH1.scalar_case T z fun x => ?_
    have hx := DFunLike.congr_fun hA0 x
    simpa [sub_eq_zero] using hx
  · exact OMA.InvariantSubspaceH1.commute_case T _ (fun x => by simp) hA0 h
