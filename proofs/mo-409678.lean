import OMAStatements.S_mo_409678
import Mathlib

-- Problem: mo-409678, does a compact convex subset of R^n that meets every facet of the cube
-- [-1, 1]^n contain the origin?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No, already for n = 3. Let K be the convex hull of (-1, 1, 1), (1, -1, 1), (1, 1, -1) and
-- (1, 1, 1). These four points lie in the cube and on the six facets (the last one on the
-- three facets x_i = 1), but every point of K satisfies x_0 + x_1 + x_2 >= 1, so 0 is not in K.

namespace MO409678

abbrev pts : Set (Fin 3 → ℝ) := {![-1, 1, 1], ![1, -1, 1], ![1, 1, -1], ![1, 1, 1]}

theorem half_convex : Convex ℝ {x : Fin 3 → ℝ | 1 ≤ x 0 + x 1 + x 2} := by
  intro x hx y hy a b ha hb hab
  have hx' : 1 ≤ x 0 + x 1 + x 2 := hx
  have hy' : 1 ≤ y 0 + y 1 + y 2 := hy
  show 1 ≤ (a • x + b • y) 0 + (a • x + b • y) 1 + (a • x + b • y) 2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx' ha, mul_le_mul_of_nonneg_left hy' hb]

theorem pts_sub : pts ⊆ {x : Fin 3 → ℝ | 1 ≤ x 0 + x 1 + x 2} := by
  intro x hx
  simp only [pts, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · show (1 : ℝ) ≤ -1 + 1 + 1
    norm_num
  · show (1 : ℝ) ≤ 1 + -1 + 1
    norm_num
  · show (1 : ℝ) ≤ 1 + 1 + -1
    norm_num
  · show (1 : ℝ) ≤ 1 + 1 + 1
    norm_num

theorem facets : ∀ (i : Fin 3) (s : ℝ), (s = 1 ∨ s = -1) →
    ∃ x ∈ convexHull ℝ pts, x i = s ∧ ∀ j, |x j| ≤ 1 := by
  intro i s hs
  rcases hs with rfl | rfl
  · refine ⟨![1, 1, 1], subset_convexHull ℝ pts (by simp [pts]), ?_, ?_⟩
    · fin_cases i <;> simp
    · intro j
      fin_cases j <;> simp
  · fin_cases i
    · refine ⟨![-1, 1, 1], subset_convexHull ℝ pts (by simp [pts]), by simp, ?_⟩
      intro j
      fin_cases j <;> simp
    · refine ⟨![1, -1, 1], subset_convexHull ℝ pts (by simp [pts]), by simp, ?_⟩
      intro j
      fin_cases j <;> simp
    · refine ⟨![1, 1, -1], subset_convexHull ℝ pts (by simp [pts]), by simp, ?_⟩
      intro j
      fin_cases j <;> simp

end MO409678

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_409678.main) := by
  intro h
  have h0 := h 3 (by norm_num) (convexHull ℝ MO409678.pts)
    (Set.Finite.isCompact_convexHull ℝ (Set.toFinite MO409678.pts)) (convex_convexHull ℝ _)
    MO409678.facets
  have h1 := convexHull_min MO409678.pts_sub MO409678.half_convex h0
  have h2 : (1 : ℝ) ≤ (0 : Fin 3 → ℝ) 0 + (0 : Fin 3 → ℝ) 1 + (0 : Fin 3 → ℝ) 2 := h1
  norm_num at h2
