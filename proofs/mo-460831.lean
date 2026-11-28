import OMAStatements.S_mo_460831
import Mathlib

/-! The projection is 1-Lipschitz, so it does not increase the Hausdorff measure of dimension
n - 2. A set of finite Hausdorff measure in dimension n - 2 has zero Hausdorff measure in any
larger dimension, in particular in dimension n - 1. -/

namespace OMA.Helpers

theorem mo460831_proj_lip (n : ℕ) : LipschitzWith 1 (OMA.S_mo_460831.proj n) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  rw [NNReal.coe_one, one_mul]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc (f := fun i => dist (x i) (y i) ^ 2)]
  have h : ∀ i : Fin n, dist ((OMA.S_mo_460831.proj n x) i) ((OMA.S_mo_460831.proj n y) i)
      = dist (x (Fin.castSucc i)) (y (Fin.castSucc i)) := fun i => rfl
  simp only [h]
  have := sq_nonneg (dist (x (Fin.last n)) (y (Fin.last n)))
  linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_460831.main := by
  intro n hn S hS
  have hd : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have h2n : ((2 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    norm_num at h2n
    linarith
  have himg := (OMA.Helpers.mo460831_proj_lip n).hausdorffMeasure_image_le hd S
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at himg
  have hfin : MeasureTheory.Measure.hausdorffMeasure ((n : ℝ) - 2)
      (OMA.S_mo_460831.proj n '' S) ≠ ⊤ := (lt_of_le_of_lt himg hS).ne
  rcases MeasureTheory.Measure.hausdorffMeasure_zero_or_top
    (show (n : ℝ) - 2 < (n : ℝ) - 1 by linarith) (OMA.S_mo_460831.proj n '' S) with h | h
  · exact h
  · exact absurd h hfin
