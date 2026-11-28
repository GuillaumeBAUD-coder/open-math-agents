import OMAReductions.R_oeis_a099251_R1
import Mathlib

open scoped Interval

lemma catalanBetaKernel (j : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Real.sqrt ((1 - t) / t) * (4 * t) ^ j =
      4 ^ j * (t ^ ((j : ℝ) - 1 / 2) * (1 - t) ^ (1 / 2 : ℝ)) := by
  have h₀ : 0 < t := ht.1
  have h₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2.le
  rw [Real.sqrt_div h₁, mul_pow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    show (j : ℝ) - 1 / 2 = (j : ℝ) + -(1 / 2) by ring, Real.rpow_add h₀, Real.rpow_neg h₀.le, Real.rpow_natCast]
  ring

lemma catalanBetaIntegral (j : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t) * (4 * t) ^ j) =
      4 ^ j * (Complex.betaIntegral ((j : ℂ) + 1 / 2) (3 / 2)).re := by
  rw [show (∫ t in (0 : ℝ)..1, Real.sqrt ((1 - t) / t) * (4 * t) ^ j) =
      ∫ t in (0 : ℝ)..1, 4 ^ j * (t ^ ((j : ℝ) - 1 / 2) * (1 - t) ^ (1 / 2 : ℝ)) from
        intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun _ ht => catalanBetaKernel j ht,
    intervalIntegral.integral_const_mul]
  congr 1
  have h : Complex.betaIntegral ((j : ℂ) + 1 / 2) (3 / 2) =
      ∫ t in (0 : ℝ)..1, ((t ^ ((j : ℝ) - 1 / 2) * (1 - t) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le)]
    push_cast
    congr 1 <;> congr 1 <;> ring
  rw [h, intervalIntegral.integral_ofReal]
  simp

lemma catalanBetaValue (j : ℕ) :
    (2 / Real.pi) * (4 ^ j * (Complex.betaIntegral ((j : ℂ) + 1 / 2) (3 / 2)).re)
      = (catalan j : ℝ) := by
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (j : ℂ) + 1 / 2) (t := 3 / 2) (by simp; positivity) (by norm_num)
  have hsum : (j : ℂ) + 1 / 2 + 3 / 2 = ((j + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [hsum, Complex.Gamma_nat_eq_factorial,
    show (j : ℂ) + 1 / 2 = (((j : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbeta
  have hreal := congrArg Complex.re hbeta
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at hreal
  have hhalf : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hhalf] at hreal
  have hdup := Real.Gamma_mul_Gamma_add_half ((j : ℝ) + 1 / 2)
  rw [show (j : ℝ) + 1 / 2 + 1 / 2 = (j : ℝ) + 1 by ring,
    show 2 * ((j : ℝ) + 1 / 2) = ((j+j : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    show 1 - (((j+j : ℕ) : ℝ) + 1) = -(((j+j : ℕ) : ℝ)) by ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_add,
    ← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num] at hdup
  have hcat := Nat.add_choose_mul_factorial_mul_factorial j j
  rw [show (j+j).choose j = j.centralBinom by simp [Nat.centralBinom, two_mul],
    ← succ_mul_catalan_eq_centralBinom] at hcat
  have hcatR : ((j : ℝ) + 1) * catalan j * (j.factorial : ℝ) * j.factorial =
      ((j+j).factorial : ℝ) := by exact_mod_cast hcat
  have hfac : ((j+1).factorial : ℝ) = ((j : ℝ) + 1) * j.factorial := by
    rw [Nat.factorial_succ]; push_cast; rfl
  rw [hfac] at hreal
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hp : (0 : ℝ) < 4 ^ j := by positivity
  have hj' : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  push_cast at hreal
  have hdup' : Real.Gamma ((j : ℝ) + 1 / 2) * j.factorial * 4 ^ j =
      ((j+j).factorial : ℝ) * Real.sqrt Real.pi := by
    rw [hdup]
    field_simp [hp.ne']
  field_simp [Real.pi_pos.ne']
  apply mul_left_cancel₀ (show ((j : ℝ) + 1) * (j.factorial : ℝ) ^ 2 ≠ 0 by positivity)
  linear_combination (norm := ring_nf)
    (-(2 : ℝ) * (4 ^ j) * j.factorial) * hreal +
    Real.sqrt Real.pi * hdup' - Real.pi * hcatR +
    (((j+j).factorial : ℝ)) * hsq

theorem OMA.solution : OMA.R_oeis_a099251_R1.H1 := by
  intro j
  rw [catalanBetaIntegral, catalanBetaValue]
