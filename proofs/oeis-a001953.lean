import OMAStatements.S_oeis_a001953
import Mathlib

namespace OMA.A001953Proof

open OMA.S_oeis_a001953

lemma a_one : a 1 = 2 := by
  unfold a
  rw [Nat.floor_eq_iff (by positivity)]
  have h2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h43 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  push_cast
  constructor <;> nlinarith

lemma zeta3_re : (riemannZeta 3).re = ∑' n : ℕ, 1 / (n : ℝ) ^ 3 := by
  have hz := zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < 3)
  push_cast at hz
  rw [hz]
  rw [Complex.re_tsum]
  · congr 1
    ext n
    simp [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_one,
      ← Complex.ofReal_div]
  · have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
    have := (Complex.summable_ofReal.mpr this)
    convert this using 1
    ext n
    push_cast
    rfl

lemma zeta3_lt_two : (riemannZeta 3).re < 2 := by
  rw [zeta3_re]
  have hs3 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hle : ∑' n : ℕ, 1 / (n : ℝ) ^ 3 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    apply hs3.tsum_le_tsum _ hs2
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
  rw [hasSum_zeta_two.tsum_eq] at hle
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

theorem main_disproof :
    ¬ (∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1)) := by
  intro h
  have h1 := (h 1 le_rfl).2
  rw [a_one] at h1
  simp [s] at h1
  linarith [zeta3_lt_two]

end OMA.A001953Proof

open OMA.A001953Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001953.main) := main_disproof
