import OMAStatements.S_mo_409678
import Mathlib

-- Problem mo-409678: the statement claims that a compact convex subset K of R^n (n >= 1) that meets every
-- facet of the cube [-1, 1]^n (inside the cube) contains the origin.
-- Upstream: statements/mo-409678.lean (declaration OMA.S_mo_409678.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: it fails for n = 3. Let K be the part of the cube [-1, 1]^3 where x0 + x1 + x2 >= 1. It is
-- compact and convex. It contains (1, 1, 1), which lies on the three facets x_i = 1, and the three points with
-- one coordinate -1 and the other two equal to 1 (coordinate sum 1), which lie on the facets x_i = -1. But the
-- origin has coordinate sum 0 < 1, so it is not in K.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_409678.main) := by
  intro h
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Fin 3 → ℝ),
      K = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∩ {x | 1 ≤ x 0 + x 1 + x 2} := ⟨_, rfl⟩
  have hmem : ∀ x : Fin 3 → ℝ, x ∈ K ↔ (∀ j, -1 ≤ x j ∧ x j ≤ 1) ∧ 1 ≤ x 0 + x 1 + x 2 := by
    intro x
    rw [hKdef]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq, Pi.le_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨fun j => ⟨h1 j, h2 j⟩, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨fun j => (h1 j).1, fun j => (h1 j).2⟩, h3⟩
  have hcomp : IsCompact K := by
    rw [hKdef]
    apply IsCompact.inter_right isCompact_Icc
    exact isClosed_le continuous_const
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hconv : Convex ℝ K := by
    rw [hKdef]
    apply Convex.inter (convex_Icc _ _)
    intro x hx y hy a b ha hb hab
    have hx' : 1 ≤ x 0 + x 1 + x 2 := hx
    have hy' : 1 ≤ y 0 + y 1 + y 2 := hy
    show 1 ≤ (a • x + b • y) 0 + (a • x + b • y) 1 + (a • x + b • y) 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx'), mul_nonneg hb (sub_nonneg.mpr hy')]
  have htouch : ∀ (i : Fin 3) (s : ℝ), (s = 1 ∨ s = -1) → ∃ x ∈ K, x i = s ∧ ∀ j, |x j| ≤ 1 := by
    intro i s hs
    rcases hs with rfl | rfl
    · refine ⟨fun _ => 1, (hmem _).mpr ⟨fun j => by norm_num, by norm_num⟩, rfl, fun j => by norm_num⟩
    · refine ⟨fun j => if j = i then -1 else 1, (hmem _).mpr ⟨fun j => ?_, ?_⟩, by simp, fun j => ?_⟩
      · split_ifs <;> norm_num
      · fin_cases i <;> simp <;> norm_num
      · show |(if j = i then (-1 : ℝ) else 1)| ≤ 1
        split_ifs <;> norm_num
  have h0 := h 3 (by norm_num) K hcomp hconv htouch
  have h1 := ((hmem 0).mp h0).2
  norm_num at h1
