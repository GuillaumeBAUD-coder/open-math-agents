import OMAStatements.S_oeis_a001953
import Mathlib

namespace OMA.S_oeis_a001953

theorem zeta3_le : (riemannZeta 3).re ≤ 2 := by
  have h3 : riemannZeta 3 = ((∑' n : ℕ, 1 / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    have := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
    rw [Complex.ofReal_tsum]
    simpa using this
  rw [h3, Complex.ofReal_re]
  have hs3 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hs2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hle : ∑' n : ℕ, 1 / (n : ℝ) ^ 3 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    refine hs3.tsum_le_tsum (fun n => ?_) hs2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_pos (lt_of_lt_of_le one_pos h1) 2]
  rw [hasSum_zeta_two.tsum_eq] at hle
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

theorem a_one : a 1 = 2 := by
  unfold a
  rw [Nat.floor_eq_iff (by positivity)]
  have h1 : (4 / 3 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor <;> norm_num <;> linarith

end OMA.S_oeis_a001953

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001953.main) := by
  intro h
  have h1 := (h 1 (le_refl 1)).2
  rw [OMA.S_oeis_a001953.a_one] at h1
  have hz := OMA.S_oeis_a001953.zeta3_le
  simp [OMA.S_oeis_a001953.s] at h1
  linarith
