import OMAReductions.R_itp_courtade_kumar_R1
import Mathlib

-- Step itp-courtade-kumar.R1.H2: finite-sum entropy decomposition of mutual information.

namespace CourtadeKumarBridge

open OMA.S_itp_courtade_kumar
open scoped BigOperators

lemma bitFlipKernel_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (x y : Cube n) : 0 < bitFlipKernel p x y := by
  unfold bitFlipKernel
  apply Finset.prod_pos
  intro i _
  split_ifs
  · linarith
  · exact hp

lemma jointProbability_nonneg {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    0 ≤ jointProbability p f b y := by
  unfold jointProbability cubeAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact (bitFlipKernel_pos hp hp' x y).le
    · exact le_rfl
  · positivity

lemma mi_term_eq {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    (if 0 < jointProbability p f b y then
      jointProbability p f b y * Real.log (jointProbability p f b y /
        (functionMarginal p f b * observationMarginal p f y))
     else 0) =
      jointProbability p f b y * Real.log (jointProbability p f b y) -
        jointProbability p f b y * Real.log (functionMarginal p f b) -
        jointProbability p f b y * Real.log (observationMarginal p f y) := by
  by_cases hpos : 0 < jointProbability p f b y
  · rw [if_pos hpos]
    have hfb : 0 < functionMarginal p f b := by
      have hle : jointProbability p f b y ≤ functionMarginal p f b := by
        unfold functionMarginal
        exact Finset.single_le_sum (fun y' _ => jointProbability_nonneg hp hp' f b y')
          (Finset.mem_univ y)
      exact lt_of_lt_of_le hpos hle
    have hob : 0 < observationMarginal p f y := by
      have hle : jointProbability p f b y ≤ observationMarginal p f y := by
        unfold observationMarginal
        exact Finset.single_le_sum (fun b' _ => jointProbability_nonneg hp hp' f b' y)
          (Finset.mem_univ b)
      exact lt_of_lt_of_le hpos hle
    rw [Real.log_div hpos.ne' (mul_pos hfb hob).ne', Real.log_mul hfb.ne' hob.ne']
    ring
  · rw [if_neg hpos]
    have hzero : jointProbability p f b y = 0 :=
      le_antisymm (not_lt.mp hpos) (jointProbability_nonneg hp hp' f b y)
    simp [hzero]

end CourtadeKumarBridge

open OMA.S_itp_courtade_kumar CourtadeKumarBridge in
open scoped BigOperators in
theorem OMA.solution : OMA.R_itp_courtade_kumar_R1.H2 := by
  intro n p hp hp' f
  unfold mutualInformation
  congr 1
  simp_rw [mi_term_eq hp hp' f, Finset.sum_sub_distrib]
  have hB : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * Real.log (functionMarginal p f b)) =
      -∑ b : Bool, Real.negMulLog (functionMarginal p f b) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_mul, Real.negMulLog]
    unfold functionMarginal
    ring
  have hY : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * Real.log (observationMarginal p f y)) =
      -∑ y : Cube n, Real.negMulLog (observationMarginal p f y) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul, Real.negMulLog]
    unfold observationMarginal
    ring
  have hJ : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * Real.log (jointProbability p f b y)) =
      -∑ z : Bool × Cube n, Real.negMulLog (jointProbability p f z.1 z.2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [hB, hY, hJ]
  ring
