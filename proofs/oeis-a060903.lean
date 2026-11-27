import OMAStatements.S_oeis_a060903
import Mathlib

/-!
Complementing each divisor and enlarging the reciprocal sum gives
σ(n) ≤ n Hₙ. A tangent bound for log at √n / 8 suffices from 256
onward. For smaller n the squared rational bound is decidable in ℕ.
-/

namespace DivisorHarmonic

open Real

private theorem harmonicBound (n : ℕ) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℝ) ≤ n * (1 + log n) := by
  rw [Nat.cast_sum]
  calc ∑ d ∈ n.divisors, (d : ℝ)
      = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) := (Nat.sum_div_divisors n _).symm
    _ = ∑ d ∈ n.divisors, (n : ℝ) * (d : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'), div_eq_mul_inv]
    _ ≤ ∑ d ∈ Finset.Icc 1 n, (n : ℝ) * (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)⟩
      · intros
        positivity
    _ = (n : ℝ) * (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)

private theorem logBound {x : ℝ} (hx : 0 < x) : 1 + log x ≤ √x / 4 + 5 := by
  have h := log_le_sub_one_of_pos (div_pos (sqrt_pos.2 hx) (by norm_num : (0 : ℝ) < 8))
  rw [log_div (sqrt_pos.2 hx).ne' (by norm_num), log_sqrt hx.le] at h
  have h8 : log (8 : ℝ) ≤ 3 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, log_pow]
    norm_num
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem small : ∀ k : Fin 256, 12 < k.val →
    ((∑ d ∈ k.val.divisors, d) + 1)^2 * 25 ≤ 9 * k.val^3 := by
  decide +kernel

private theorem rationalBound (n : ℕ) (hn : 12 < n) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1 ≤ 3 * n * √n / 5 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs := Real.sq_sqrt hn0.le
  by_cases h : n < 256
  · have hk := small ⟨n, h⟩ hn
    have hr : (((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1)^2 * 25 ≤ 9 * (n : ℝ)^3 := by
      exact_mod_cast hk
    have hsq : (3 * (n : ℝ) * √n)^2 = 9 * (n : ℝ)^3 := by
      rw [mul_pow, hs]; ring
    have hab : 5 * (((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1) ≤ 3 * (n : ℝ) * √n :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp (by nlinarith [hsq])
    linarith
  · have hn256 : (256 : ℝ) ≤ n := by exact_mod_cast (show 256 ≤ n by omega)
    have hs16 : (16 : ℝ) ≤ √n := by nlinarith [sqrt_nonneg (n : ℝ)]
    have hlog := mul_le_mul_of_nonneg_left (logBound hn0) hn0.le
    nlinarith [harmonicBound n, mul_nonneg (sub_nonneg.mpr hs16) hn0.le]

end DivisorHarmonic

theorem OMA.solution : type_of% @OMA.S_oeis_a060903.main := by
  intro n hn
  apply Nat.lt_of_succ_le
  apply Nat.le_floor
  rw [Nat.cast_succ]
  apply (DivisorHarmonic.rationalBound n hn).trans
  apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
  have hprod := mul_nonneg (sub_nonneg.mpr Real.pi_lt_d2.le)
    (by positivity : 0 ≤ 3.15 + Real.pi)
  have hp : Real.pi^2 ≤ 10 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by positivity : 0 ≤ (n : ℝ) * √n)]
