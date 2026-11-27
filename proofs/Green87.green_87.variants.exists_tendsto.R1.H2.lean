import OMAReductions.R_Green87_green_87_variants_exists_tendsto_R1
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The running averages have summable successive differences. The bounded error
in the hypothesis then makes the original sequence converge to their limit. -/
-- Credit: @Halldon

open Filter Finset
open scoped Topology

theorem OMA.solution : OMA.R_Green87_green_87_variants_exists_tendsto_R1.H2 := by
  intro a C hC hError
  let total (n : ℕ) := ∑ j ∈ range n, a j
  let mean (n : ℕ) := total n / (n : ℝ)
  have step (n : ℕ) (hn : 0 < n) :
      mean (n + 1) - mean n = ((n : ℝ) * a n - total n) / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hs' : (n : ℝ) + 1 ≠ 0 := by positivity
    have ht : total (n + 1) = total n + a n := Finset.sum_range_succ _ _
    simp only [mean, ht, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  have hSeries : Summable (fun n : ℕ ↦ C / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left C
  have hShift : Summable (fun n : ℕ ↦ C / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hSeries
  have hCauchy : CauchySeq (fun n : ℕ ↦ mean (n + 1)) := by
    refine cauchySeq_of_dist_le_of_summable _ ?_ hShift
    intro n
    change dist (mean (n + 1)) (mean ((n + 1) + 1)) ≤ C / ((n + 1 : ℕ) : ℝ) ^ 2
    have hden : 0 < ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) := by positivity
    rw [dist_comm, Real.dist_eq, step (n + 1) (by omega), abs_div, abs_of_pos hden]
    refine (div_le_div_of_nonneg_right (hError (n + 1)) hden.le).trans ?_
    have hx : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    exact div_le_div_of_nonneg_left hC (by positivity) (by nlinarith)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hMean : Tendsto mean atTop (𝓝 L) := (tendsto_add_atTop_iff_nat 1).mp hL
  have hZero : Tendsto (fun n : ℕ ↦ a n - mean n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ ↦ C / (n : ℝ))
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have herr : a n - mean n = ((n : ℝ) * a n - total n) / (n : ℝ) := by
        dsimp only [mean]
        field_simp
        <;> ring
      rw [Real.norm_eq_abs, herr, abs_div, abs_of_pos hn']
      exact div_le_div_of_nonneg_right (hError n) hn'.le
    · exact tendsto_const_div_atTop_nhds_zero_nat C
  exact ⟨L, by simpa only [sub_add_cancel, zero_add] using hZero.add hMean⟩
