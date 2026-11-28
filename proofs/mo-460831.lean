import OMAStatements.S_mo_460831

open MeasureTheory

namespace Claude460831

open OMA.S_mo_460831

theorem proj_lip (n : ℕ) : LipschitzWith 1 (proj n) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_castSucc (f := fun i => dist (x i) (y i) ^ 2)]
  have : ∀ i : Fin n, dist (proj n x i) (proj n y i) = dist (x i.castSucc) (y i.castSucc) := fun i => rfl
  simp only [this]
  have := sq_nonneg (dist (x (Fin.last n)) (y (Fin.last n)))
  linarith

end Claude460831

open Claude460831 OMA.S_mo_460831 in
theorem OMA.solution : type_of% @OMA.S_mo_460831.main := by
  intro n hn S hS
  have h0 : μH[(n : ℝ) - 1] S = 0 := by
    rcases Measure.hausdorffMeasure_zero_or_top (show (n:ℝ) - 2 < (n:ℝ) - 1 by linarith) S with h | h
    · exact h
    · exact absurd h hS.ne
  have hd : (0:ℝ) ≤ (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have := (proj_lip n).hausdorffMeasure_image_le hd S
  simpa [h0] using this
