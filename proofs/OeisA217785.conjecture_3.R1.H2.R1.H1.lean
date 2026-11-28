import OMAReductions.R_OeisA217785_conjecture_3_R1_H2_R1
import Mathlib

-- Step OeisA217785.conjecture_3.R1.H2.R1.H1: hypothesis H1 of reduction OeisA217785.conjecture_3.R1.H2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Write a divisor of degree at most one as `C c * X + C d`. Evaluating at `0` shows `d` is a
unit. If `c = 0` the divisor is the unit `C d`; if `c` is a unit, the reduction lemma
`PolyDisk.unit_of_unit_lead` applies. Otherwise `|c| ≥ 2`, and `r = -d / c` is a real root of
`s_n` with `|r| ≤ 1/2`. Multiplying by `(1 - r)^2` gives `1 = (n+2) r^(n+1) - (n+1) r^(n+2)`, whose
right side has absolute value at most `(3n + 5) / 2^(n+2) < 1` for `n ≥ 2`. -/

namespace P4A217785

open Polynomial OeisA217785 Finset

theorem closed (r : ℝ) (n : ℕ) : (1 - r) ^ 2 * ∑ k ∈ range (n + 1), ((k : ℝ) + 1) * r ^ k =
    1 - ((n : ℝ) + 2) * r ^ (n + 1) + ((n : ℝ) + 1) * r ^ (n + 2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem pow_bound (n : ℕ) (hn : 2 ≤ n) : 3 * n + 5 < 2 ^ (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem no_small_root (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hs : |r| ≤ 1 / 2)
    (hroot : ∑ k ∈ range (n + 1), ((k : ℝ) + 1) * r ^ k = 0) : False := by
  have hcl := closed r n
  rw [hroot, mul_zero] at hcl
  have e1 : (n + 2 : ℝ) * r ^ (n + 1) - (n + 1) * r ^ (n + 2) = 1 := by linarith
  have b1 : |r| ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ (abs_nonneg r) hs _
  have b2 : |r| ^ (n + 2) ≤ (1 / 2 : ℝ) ^ (n + 2) := pow_le_pow_left₀ (abs_nonneg r) hs _
  have habs : |(n + 2 : ℝ) * r ^ (n + 1) - (n + 1) * r ^ (n + 2)| ≤
      (n + 2) * |r| ^ (n + 1) + (n + 1) * |r| ^ (n + 2) := by
    calc _ ≤ |(n + 2 : ℝ) * r ^ (n + 1)| + |(n + 1 : ℝ) * r ^ (n + 2)| := abs_sub _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  rw [e1, abs_one] at habs
  have hp : (3 * n + 5 : ℝ) < 2 ^ (n + 2) := by exact_mod_cast pow_bound n hn
  have hu : ((1 : ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  have hu2 : ((1 : ℝ) / 2) ^ (n + 2) = ((1 : ℝ) / 2) ^ (n + 1) / 2 := by rw [pow_succ]; ring
  have h22 : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hupos : 0 < ((1 : ℝ) / 2) ^ (n + 1) := by positivity
  rw [hu2] at b2
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have c1 := mul_le_mul_of_nonneg_left b1 (show (0 : ℝ) ≤ n + 2 by positivity)
  have c2 := mul_le_mul_of_nonneg_left b2 (show (0 : ℝ) ≤ n + 1 by positivity)
  have c3 := mul_lt_mul_of_pos_left hp hupos
  nlinarith

end P4A217785

open Polynomial OeisA217785 Finset P4A217785 in
theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1_H2_R1.H1 := by
  intro n hn a hd hdeg
  have ha := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have hd1 : a.coeff 0 ∣ 1 := by
    have h := Polynomial.eval_dvd (x := 0) hd
    rw [PolyDisk.eval_zero, ← Polynomial.coeff_zero_eq_eval_zero] at h
    exact h
  have hdu : IsUnit (a.coeff 0) := isUnit_of_dvd_one hd1
  by_cases hc0 : a.coeff 1 = 0
  · rw [ha, hc0, map_zero, zero_mul, zero_add]
    exact Polynomial.isUnit_C.mpr hdu
  by_cases hcu : IsUnit (a.coeff 1)
  · apply PolyDisk.unit_of_unit_lead a hd
    have hdeg1 : a.natDegree = 1 := le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero hc0)
    rw [Polynomial.leadingCoeff, hdeg1]
    exact hcu
  exfalso
  have hc2 : 2 ≤ |a.coeff 1| := by
    have h1 : |a.coeff 1| ≠ 1 := fun h => hcu (Int.isUnit_iff_abs_eq.mpr h)
    have h2 : |a.coeff 1| ≠ 0 := abs_ne_zero.mpr hc0
    have h3 := abs_nonneg (a.coeff 1)
    omega
  have hd' : |a.coeff 0| = 1 := Int.isUnit_iff_abs_eq.mp hdu
  set c := a.coeff 1 with hc
  set d := a.coeff 0 with hdd
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  apply no_small_root n hn (-(d : ℝ) / (c : ℝ))
  · rw [abs_div, abs_neg]
    have e : |(d : ℝ)| = 1 := by rw [← Int.cast_abs, hd']; simp
    have h2 : (2 : ℝ) ≤ |(c : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hc2
    rw [e, div_le_iff₀ (by linarith)]
    linarith
  · have hm : a.map (Int.castRingHom ℝ) ∣ (polyS n).map (Int.castRingHom ℝ) :=
      Polynomial.map_dvd _ hd
    have hz : (a.map (Int.castRingHom ℝ)).eval (-(d : ℝ) / (c : ℝ)) = 0 := by
      rw [ha, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
        Polynomial.map_X]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        eq_intCast]
      field_simp
      ring
    have h2 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hm hz
    rw [Polynomial.eval_map] at h2
    simpa [polyS, eval₂_finsetSum] using h2

