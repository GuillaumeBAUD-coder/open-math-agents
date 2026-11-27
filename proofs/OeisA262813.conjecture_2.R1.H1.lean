import OMAReductions.R_OeisA262813_conjecture_2_R1
import Mathlib

/-! The seven finite counts for sums of cubes, squares, and triangular numbers. -/
open Finset

namespace A262813Finite

private def term (n x y z : ℕ) : ℕ :=
  if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0

private def clipped (n : ℕ) : ℕ :=
  ∑ x ∈ range (min (n + 1) 7), ∑ y ∈ range (min (n + 1) 18),
    ∑ z ∈ Ico 1 (min (n + 1) 25), term n x y z

private theorem clipRange (N k : ℕ) (f : ℕ → ℕ) (h : ∀ j, k ≤ j → f j = 0) :
    (∑ j ∈ range N, f j) = ∑ j ∈ range (min N k), f j := by
  symm
  apply sum_subset (range_mono (min_le_left _ _))
  intro j hj hnot
  apply h
  have hj' := mem_range.mp hj
  have hnot' : ¬j < min N k := fun h => hnot (mem_range.mpr h)
  omega

private theorem triangleLarge (z : ℕ) (hz : 25 ≤ z) : 325 ≤ Nat.triangular z := by
  have hm : 25 * 26 ≤ z * (z + 1) := Nat.mul_le_mul hz (by omega)
  change 325 ≤ z * (z + 1) / 2
  omega

private theorem a_eq (n : ℕ) (hn : n ≤ 306) : OeisA262813.a n = clipped n := by
  change (∑ x ∈ range (n + 1), ∑ y ∈ range (n + 1),
    ∑ z ∈ Ico 1 (n + 1), term n x y z) = clipped n
  unfold clipped
  calc
    _ = ∑ x ∈ range (min (n + 1) 7), ∑ y ∈ range (n + 1),
        ∑ z ∈ Ico 1 (n + 1), term n x y z := by
      apply clipRange
      intro x hx
      have hcube : 343 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
      simp [term, show ∀ y z : ℕ, x ^ 3 + y ^ 2 + Nat.triangular z ≠ n by
        intro y z; omega]
    _ = _ := by
      apply sum_congr rfl
      intro x _
      calc
        _ = ∑ y ∈ range (min (n + 1) 18), ∑ z ∈ Ico 1 (n + 1), term n x y z := by
          apply clipRange
          intro y hy
          have hsquare : 324 ≤ y ^ 2 := Nat.pow_le_pow_left hy 2
          simp [term, show ∀ z : ℕ, x ^ 3 + y ^ 2 + Nat.triangular z ≠ n by
            intro z; omega]
        _ = _ := by
          apply sum_congr rfl
          intro y _
          symm
          apply sum_subset (Ico_subset_Ico_right (min_le_left _ _))
          intro z hz hnot
          have hz' := mem_Ico.mp hz
          have hmin : 25 ≤ z := by
            by_contra! hlt
            exact hnot (mem_Ico.mpr ⟨hz'.1, lt_min hz'.2 hlt⟩)
          have hzbig := triangleLarge z hmin
          simp [term, show x ^ 3 + y ^ 2 + Nat.triangular z ≠ n by omega]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem ones (n : ℕ) (hn : n ∈ ({1, 9, 21, 35, 98, 152, 306} : Finset ℕ)) :
    OeisA262813.a n = 1 := by
  simp only [mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [a_eq _ (by decide)]; decide +kernel

end A262813Finite

theorem OMA.solution : OMA.R_OeisA262813_conjecture_2_R1.H1 := A262813Finite.ones