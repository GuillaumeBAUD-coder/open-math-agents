import FormalConjectures.Wikipedia.MoserWorm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Reduction of the exact-area statement to Norwood–Poole's bounded cover. -/

-- Reduction MoserWorm.mosers_worm_problem_upper_bound.R1 of Moser's Worm — mosers worm problem upper bound
-- Credit: @AaronRai123

namespace OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1

open EuclideanGeometry MeasureTheory
open scoped ENNReal

/-- The genuinely geometric part of the Norwood–Poole construction. -/
def H1 : Prop :=
  ∃ (X : Set ℝ²) (R : ℝ), X ∈ MoserWorm.WormCovers ∧ 0 ≤ R ∧
    X ⊆ Metric.closedBall 0 R ∧ volume X ≤ (0.260437 : ℝ≥0∞)

/-- A bounded worm cover can be enlarged to any prescribed finite area above its own. -/
def H2 : Prop :=
  ∀ (X : Set ℝ²), X ∈ MoserWorm.WormCovers → ∀ {R : ℝ}, 0 ≤ R →
    X ⊆ Metric.closedBall 0 R → ∀ {b : ℝ≥0∞}, b ≠ ⊤ → volume X ≤ b →
      ∃ Y ∈ MoserWorm.WormCovers, volume Y = b

theorem padding : H2 := by
  intro X hX R hR hbounded b hb hvol
  let r := Real.sqrt ((b - volume X).toReal / Real.pi)
  let c : ℝ² := EuclideanSpace.single 0 (R + r + 1)
  let D := Metric.ball c r
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hc : dist 0 c = R + r + 1 := by
    rw [dist_comm, dist_zero_right]
    simp [c, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R + r + 1)]
  have hdisj : Disjoint X D :=
    (Metric.closedBall_disjoint_ball (by rw [hc]; linarith)).mono_left hbounded
  have hD : MeasurableSet D := measurableSet_ball
  have hvolD : volume D = b - volume X := by
    have harea : r ^ 2 * Real.pi = (b - volume X).toReal := by
      dsimp [r]
      rw [Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg Real.pi_pos.le),
        div_mul_cancel₀ _ Real.pi_ne_zero]
    change volume (Metric.ball c r) = b - volume X
    rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (sq_nonneg r), harea, ENNReal.ofReal_toReal (ENNReal.sub_ne_top hb)]
  obtain ⟨hm, hcover⟩ := hX
  refine ⟨X ∪ D, ⟨hm.union hD, ?_⟩, ?_⟩
  · intro w hw
    obtain ⟨e, v, hd, hsub⟩ := hcover w hw
    exact ⟨e, v, hd, hsub.trans (Set.image_mono Set.subset_union_left)⟩
  · rw [measure_union hdisj hD, hvolD, add_tsub_cancel_of_le hvol]

theorem main : H1 → H2 → type_of% @MoserWorm.mosers_worm_problem_upper_bound := by
  rintro ⟨X, R, hX, hR, hbounded, hvol⟩ pad
  have hb : (0.260437 : ℝ≥0∞) ≠ ∞ := by
    exact ne_of_lt (ENNReal.coe_lt_top (r := (0.260437 : NNReal)))
  exact pad X hX hR hbounded (b := (0.260437 : ℝ≥0∞)) hb hvol

end OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1
