import FormalConjectures.Wikipedia.RiemannZetaValues
import Mathlib

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ahhwuhu/zeta_3_irrational/blob/e8785315a01c8fbcddaa0fc03b3c8b29a61bc1f1/Zeta3Irrational/Basic.lean  (theorem zeta_3_irratoinal)
Original author: Junqi Liu and Jujian Zhang (ahhwuhu)   Licence: Apache-2.0 (LICENSE)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: started from the Apache-2.0 Lean v4.34.1 update in openai/math
(lean/patches/Zeta3Irrational-lean4341.patch at 3344da59991ed94f9ba711217b29c1d760badfa6);
files Bound, LegendrePoly, d, Integral, LinearForm, Basic inlined into one namespace (Equality
dropped, unused); the prime number theorem input (from PrimeNumberTheoremAnd, not in Mathlib) is
replaced by Chebyshev's elementary bound psi(N) <= (1.10555... + eps) N, taken pruned from
openai/math (Apache-2.0); to fit that weaker bound, the integrand bound 1/24 is sharpened to 1/32
(new lemma bound_sharp) and the constants 21 and 21/24 become 30 and 30/32.

Original file header:
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
(Paper: arXiv:2503.07625.)
-/

namespace OMAPort_Zeta3

section Zeta3_Bound

/-! Elementary bounds for the Apéry integral, ported from the Apache-2.0 proof by
Junqi Liu and Jujian Zhang. -/

open scoped _root_.Nat
open _root_.BigOperators

lemma max_value {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * √(1 - x) ≤ ((1 / 2) : ℝ) := by
  rw [← Real.sqrt_mul, le_div_iff₀, ← show √4 = 2 by rw [Real.sqrt_eq_iff_eq_sq] <;> linarith,
    ← Real.sqrt_mul, Real.sqrt_le_one, show x * (1 - x) * 4 = 1 - (2 * x - 1) ^ 2 by ring] <;>
  nlinarith [mul_self_nonneg (2 * x - 1)]

lemma max_value' {x : ℝ} (x0 : 0 < x) (x1 : x < 1) : √x * (1 - x) ≤ ((2 / 5) : ℝ) := by
  calc
  _ = √(x * (1 - x) ^ 2) := by rw [Real.sqrt_mul, pow_two, Real.sqrt_mul_self] <;> linarith
  _ ≤ √(4 / 27 : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    suffices x * (1 - x) ^ 2 - (4 / 27 : ℝ) ≤ 0 by linarith
    rw [show x * (1 - x) ^ 2 - (4 / 27 : ℝ) = (x - (4 / 3 : ℝ)) * (x - (1 / 3 : ℝ)) ^ 2 by ring,
      mul_nonpos_iff]
    right
    exact ⟨by linarith, by positivity⟩
  _ ≤ ((2 / 5) : ℝ) := by
    rw [Real.sqrt_le_left] <;> norm_num

lemma nonneg {x : ℝ} (_ : 0 < x) (_ : x < 1) : (0 : ℝ) ≤ √x * √(1 - x) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma bound_aux (x z : ℝ) (x0 : 0 < x) (x1 : x < 1) (z0 : 0 < z) (_ : z < 1) :
    2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by
  rw [← sub_pos] at x1
  have := mul_pos x0 z0
  rw [show 1 - (1 - z) * x = 1 - x + x * z by ring]
  calc
    _ ≤ (√(1 - x) - √(x * z)) * (√(1 - x) - √(x * z)) + 2 * √(1 - x) * √(x * z) :=
      by linarith [mul_self_nonneg (√(1 - x) - √(x * z))]
    _ = √(1 - x) * √(1 - x) + √(x * z) * √(x * z) := by ring
    _ = 1 - x + x * z := by rw [Real.mul_self_sqrt, Real.mul_self_sqrt] <;> linarith

lemma bound (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / ((1 - (1 - z) * x) * (1 - y * z)) < (1 / 30 : ℝ) := by
  have := mul_pos x0 z0
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by apply bound_aux <;> assumption
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (by linarith) (by linarith) using 2
    · rw [mul_comm]
    · ring
  rw [← sub_pos] at x1 y1 z1
  have : y * z < 1 := by nlinarith
  have : 0 < √(1 - x) := Real.sqrt_pos_of_pos x1
  have : 0 < √(x * z) := Real.sqrt_pos_of_pos (by linarith)
  have : 0 < 1 - y * z := by linarith
  have : 0 ≤ x.sqrt * (1 - x).sqrt := nonneg (by assumption) (by linarith)
  have : 0 ≤ y.sqrt * (1 - y).sqrt := nonneg (by assumption) (by linarith)
  calc
    _ ≤ x * (1 - x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - x) * √(x * z) * (1 - y * z)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      rwa [mul_le_mul_iff_of_pos_right]
      linarith
    _ ≤ x * (1 - x) * y * (1 - y) * z * (1 - z) /
        (2 * √(1 - x) * √(x * z) * 2 * √(1 - y) * √((1 - z) * y)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      rw [mul_assoc, mul_assoc]
      rw [mul_assoc] at h2
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt <| by positivity)
    _ = √x * √(1 - x) * (√y * √(1 - y)) * (√z * √(1 - z)) / 4 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
        calc
          _ = ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) /
              (4 * (√x * √(1 - x)) * (√y * √(1 - y)) * (√z * √(1 - z))) := by ring
          _ = (x / √x) * ((1 - x) / √(1 - x)) * (y / √y) *
              ((1 - y) / √(1 - y)) * (z / √z) * ((1 - z) / √(1 - z)) / 4 := by ring
          _ = _ := by simpa only [Real.div_sqrt] using (by ring)
    _ ≤ (1 / 2) * (1 / 2) * (1 / 2) / 4 := by
      refine div_le_div₀ (by norm_num)
        (mul_le_mul_of_nonneg (mul_le_mul_of_nonneg (max_value ?_ ?_) (max_value ?_ ?_) ?_ ?_)
          (max_value ?_ ?_) (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      linarith
    _ < (1 / 30 : ℝ) := by norm_num

lemma bound_aux' (x y z : ℝ) (x0 : 0 < x) (_ : x < 1) (y0 : 0 < y) (_ : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    2 * √(1 - z) * √(x * y * z) ≤ 1 - (1 - x * y) * z := by
  rw [← sub_pos] at z1
  have := mul_pos x0 (mul_pos y0 z0)
  rw [show 1 - (1 - x * y) * z = (1 - z) + x * y * z by ring]
  calc
    _ ≤ (√(1 - z) - √(x * y * z)) * (√(1 - z) - √(x * y * z)) + 2 * √(1 - z) * √(x * y * z) :=
      by linarith [mul_self_nonneg (√(1 - z) - √(x * y * z))]
    _ = √(1 - z) * √(1 - z) + √(x * y * z) * √(x * y * z) := by ring
    _ = 1 - z + x * y * z := by rw [Real.mul_self_sqrt, Real.mul_self_sqrt] <;> linarith

lemma bound' (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z) < (1 / 24 : ℝ) := by
  have := mul_pos x0 z0
  have h1 : 2 * √(1 - x) * √(x * z) ≤ 1 - (1 - z) * x := by apply bound_aux <;> assumption
  have h2 : 2 * √(1 - y) * √((1 - z) * y) ≤ 1 - y * z := by
    convert bound_aux y (1 - z) y0 y1 (by linarith) (by linarith) using 2
    · rw [mul_comm]
    · ring
  rw [← sub_pos] at x1 y1 z1
  have : y * z < 1 := by nlinarith
  have : 0 < √(1 - x) := Real.sqrt_pos_of_pos x1
  have : 0 < √(x * z) := Real.sqrt_pos_of_pos (by linarith)
  have : 0 < 1 - y * z := by linarith
  have : 0 ≤ x.sqrt * (1 - x) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have : 0 ≤ y.sqrt * (1 - y) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  calc
    _ ≤ x * (1 - x) * y * (1 - y) * z * (1 - z) / (2 * √(1 - z) * √(x * y * z)) := by
      refine div_le_div₀ (by positivity) (le_refl _) (by positivity) ?_
      apply bound_aux' <;> linarith
    _ = √x * (1 - x) * (√y * (1 - y)) * (√z * √(1 - z)) / 2 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
        calc
          _ = ((x * (1 - x)) * (y * (1 - y)) * (z * (1 - z))) /
              (2 * √x * √y * (√z * √(1 - z))) := by ring
          _ = (x / √x) * (1 - x) * (y / √y) * (1 - y) * (z / √z) *
              ((1 - z) / √(1 - z)) / 2 := by ring
          _ = _ := by simpa only [Real.div_sqrt] using (by ring)
    _ ≤ (2 / 5) * (2 / 5) * (1 / 2) / 2 := by
      refine div_le_div₀ (by norm_num)
        (mul_le_mul_of_nonneg (mul_le_mul_of_nonneg (max_value' ?_ ?_) (max_value' ?_ ?_) ?_ ?_)
          (max_value ?_ ?_) (mul_nonneg ?_ ?_) ?_) (by norm_num) (by norm_num) <;>
      try nlinarith
    _ < (1 / 24 : ℝ) := by
      norm_num

/- Added in this port: a sharper form of `bound'`, close to the true maximum `(√2 - 1) ^ 4` of
the integrand (Beukers), needed because Chebyshev's constant replaces the prime number theorem. -/
lemma bound_sharp (x y z : ℝ) (x0 : 0 < x) (x1 : x < 1) (y0 : 0 < y) (y1 : y < 1)
    (z0 : 0 < z) (z1 : z < 1) :
    x * (1 - x) * y * (1 - y) * z * (1 - z) / (1 - (1 - x * y) * z) < (1 / 32 : ℝ) := by
  have hxy : 0 < x * y := mul_pos x0 y0
  have hxy1 : x * y < 1 := by nlinarith
  obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = x * y :=
    ⟨√(x * y), Real.sqrt_pos.mpr hxy, Real.sq_sqrt hxy.le⟩
  have ht1 : t < 1 := by nlinarith
  have hD : 0 < 1 - (1 - x * y) * z := by nlinarith [mul_pos hxy z0]
  have hA : z * (1 - z) * (1 + t) ^ 2 ≤ 1 - (1 - x * y) * z := by
    nlinarith [sq_nonneg ((1 + t) * z - 1)]
  have hsum : 2 * t ≤ x + y := by
    by_contra hc
    push_neg at hc
    nlinarith [sq_nonneg (x - y), mul_self_lt_mul_self (by linarith : (0 : ℝ) ≤ x + y) hc]
  have hB : x * (1 - x) * y * (1 - y) ≤ t ^ 2 * (1 - t) ^ 2 := by
    have h1 : (1 - x) * (1 - y) ≤ (1 - t) ^ 2 := by nlinarith
    calc x * (1 - x) * y * (1 - y) = (x * y) * ((1 - x) * (1 - y)) := by ring
      _ ≤ (x * y) * (1 - t) ^ 2 := mul_le_mul_of_nonneg_left h1 hxy.le
      _ = t ^ 2 * (1 - t) ^ 2 := by rw [ht2]
  have hu : 0 ≤ t * (1 - t) := by nlinarith
  have hC1 : 283 / 50 * (t * (1 - t)) < 1 + t := by nlinarith [sq_nonneg (t - 233 / 566)]
  have hC2 := mul_self_lt_mul_self (by positivity) hC1
  have hC : 32 * (t ^ 2 * (1 - t) ^ 2) < (1 + t) ^ 2 := by nlinarith
  have hz : 0 < z * (1 - z) := by nlinarith
  rw [div_lt_iff₀ hD]
  calc x * (1 - x) * y * (1 - y) * z * (1 - z)
      = (x * (1 - x) * y * (1 - y)) * (z * (1 - z)) := by ring
    _ ≤ (t ^ 2 * (1 - t) ^ 2) * (z * (1 - z)) := mul_le_mul_of_nonneg_right hB hz.le
    _ < (1 / 32) * (1 + t) ^ 2 * (z * (1 - z)) := by
        apply mul_lt_mul_of_pos_right _ hz
        linarith
    _ ≤ (1 / 32) * (1 - (1 - x * y) * z) := by nlinarith

end Zeta3_Bound

section Zeta3_LegendrePoly

/-!
# Legendre Polynomials

We use the real shifted Legendre polynomials `aperyShiftedLegendre n` for `n : ℕ` as
a polynomial in `ℝ[X]`. We prove some basic properties of the aperyShiftedLegendre polynomials.

-/

open scoped _root_.Nat
open _root_.BigOperators _root_.Finset

variable {R : Type*}

namespace Polynomial
open _root_.Polynomial

/-- The real shifted Legendre polynomial, obtained from Mathlib's integer polynomial. -/
noncomputable def aperyShiftedLegendre (n : ℕ) : ℝ[X] :=
  (shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The canonical polynomial has exactly the Rodrigues normalization used in the source. -/
lemma aperyShiftedLegendre_eq_rodrigues (n : ℕ) :
    aperyShiftedLegendre n = C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (factorial_mul_shiftedLegendre_eq n)
  have h' : C (n ! : ℝ) * aperyShiftedLegendre n =
      derivative^[n] (X ^ n * (1 - X) ^ n) := by
    simpa only [aperyShiftedLegendre, Polynomial.map_mul, Polynomial.map_natCast,
      ← iterate_derivative_map, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, C_eq_natCast] using h
  rw [← h', ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by positivity), C_1, one_mul]

lemma Finsum_iterate_deriv [CommRing R] (k : ℕ) (h : ℕ → ℕ) :
    derivative^[k] (∑ m ∈ Finset.range (k + 1), (h m) • ((-1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m ∈ Finset.range (k + 1), (h m) • (-1) ^ m * derivative^[k] (X ^ (k + m)) := by
  simp only [iterate_derivative_sum]
  congr! 1 with m _
  rw [show (h m) • ((-1) ^ m : R[X]) = C ((h m : R) * (-1) ^ m) by simp,
    iterate_derivative_C_mul]

/-- The expand of `aperyShiftedLegendre n`. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : aperyShiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1),
      C ((-1) ^ k : ℝ) * (Nat.choose n k : ℝ[X]) *
        (Nat.choose (n + k) n : ℝ[X]) * X ^ k := by
  simp only [aperyShiftedLegendre, shiftedLegendre, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    map_mul, map_pow, map_neg, map_one, map_natCast,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_natCast]

/-- `aperyShiftedLegendre n` is an integer polynomial. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, aperyShiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k : ℝ[X]) * X ^ k := by
  simp_rw [shiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  congr! 1 with x
  simp

lemma deriv_one_sub_X {n i : ℕ} : (⇑derivative)^[i] ((1 - X) ^ n : ℝ[X]) =
    (-1) ^ i * (n.descFactorial i) • ((1 - X) ^ (n - i)) := by
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul, Algebra.smul_def, algebraMap_eq, map_natCast]
  simp

theorem differentiableAt_inv_special {x a : ℝ} {n : ℕ}
    (ha : a > 0) (hx : 1 - a * x = 0) :
    ¬DifferentiableAt ℝ (fun x ↦ ↑n ! * a ^ n / (1 - a * x) ^ (n + 1)) x := by
  intro h
  obtain q := h.continuousAt
  simp only [Metric.continuousAt_iff, gt_iff_lt, Real.dist_eq, hx, ne_eq,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, div_zero,
    dist_zero_right, norm_div, norm_mul, RCLike.norm_natCast, norm_pow, Real.norm_eq_abs] at q
  have h₁ : ↑n ! * |a| ^ n > 0 := by
    apply mul_pos
    · simp only [Nat.cast_pos]
      exact Nat.factorial_pos n
    · apply pow_pos
      exact abs_pos.2 (by linarith)
  specialize q (↑n ! * |a| ^ n) h₁
  rcases q with ⟨q, ⟨qq, qqq⟩⟩
  rcases lt_trichotomy (a * q) 1 with (h1 | h2 | h3)
  · have : |a * q / 2 * q + x - x| < q := by
      simp only [add_sub_cancel_right]
      calc
      _ = a * q / 2 * q := by
        rw [abs_eq_self, mul_comm, ← mul_div_assoc, ← mul_assoc]
        suffices 0 < q * a * q by linarith
        exact mul_pos (mul_pos qq ha) qq
      _ < 1 / 2 * q := by
        rw [mul_lt_mul_iff_left₀ qq]
        linarith
      _ < q := by linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (a * q / 2 * q + x)| ^ (n + 1) := by
        rwa [← mul_lt_mul_iff_right₀ h₁, mul_one]
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg] at this
      have : |a * (a * q / 2 * q)| ^ (n + 1) < 1 := by
        apply pow_lt_one₀ (abs_nonneg _) _ (by omega)
        · nth_rewrite 2 [mul_comm]
          rw [← mul_assoc, ← mul_div_assoc, ← pow_two]
          rw [show |((a * q) ^ 2 / 2 : ℝ)| = ((a * q) ^ 2 / 2 : ℝ) by
            exact abs_eq_self.2 (by positivity)]
          trans 1 / 2
          · rw [div_lt_div_iff_of_pos_right (by norm_num), ← one_pow (n := 2)]
            apply pow_lt_pow_left₀ <;> nlinarith
          · linarith
      linarith
    · apply pow_pos
      rw [abs_pos, mul_add, add_comm, ← sub_sub, hx, zero_sub]
      suffices a * (a * q / 2 * q) > 0 by linarith
      nth_rewrite 2 [mul_comm]
      rw [← mul_assoc, ← mul_div_assoc, ← pow_two]
      positivity
  · have : |q / 2 + x - x| < q := by
      simp only [add_sub_cancel_right]
      rw [show |(q / 2 : ℝ)| = (q / 2 : ℝ) by exact abs_eq_self.2 (by linarith)]
      linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (q / 2 + x)| ^ (n + 1) := by
        rwa [← mul_lt_mul_iff_right₀ h₁, mul_one]
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, h2] at this
      have : 1 < (1 / 2 : ℝ) := by
        suffices (1 : ℝ) ≥ |(1 / 2 : ℝ)| ^ (n + 1) by linarith
        rw [show |(1 / 2 : ℝ)| = (1 / 2 : ℝ) by exact abs_eq_self.2 (by linarith)]
        apply pow_le_one₀ <;> linarith
      linarith
    · apply pow_pos
      rw [abs_pos]
      linarith
  · have : |1 / a + x - x| < q := by
      simp only [add_sub_cancel_right]
      have : |(1 / a : ℝ)| = (1 / a : ℝ) := by
        rw [abs_eq_self, one_div_nonneg]
        linarith
      rw [this, div_lt_iff₀] <;> linarith
    specialize qqq this
    rw [div_lt_iff₀] at qqq
    · have : 1 <  |1 - a * (1 / a + x)| ^ (n + 1) := by
        rwa [← mul_lt_mul_iff_right₀ h₁, mul_one]
      rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, mul_one,
        div_self (by linarith)] at this
      simp only [abs_one, one_pow, lt_self_iff_false] at this
    · rw [mul_add, add_comm, ← sub_sub, hx, zero_sub, abs_neg, ← mul_div_assoc, mul_one,
        div_self (by linarith)]
      simp

lemma n_derivative {a : ℝ} (n : ℕ) (ha : a > 0) : deriv^[n] (fun x ↦ 1 / (1 - a * x)) =
    fun x ↦ (n) ! * (a ^ n) / (1 - a * x) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
    ext x
    rcases eq_or_ne (1 - a * x) 0 with (h | hne)
    · simp only [h, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, div_zero]
      rw [Function.iterate_succ_apply', hn]
      apply deriv_zero_of_not_differentiableAt
      exact differentiableAt_inv_special ha h
    · rw [Function.iterate_succ_apply', hn, deriv_fun_div]
      · simp only [deriv_const', zero_mul, zero_sub]
        rw [div_eq_div_iff]
        · rw [deriv_fun_pow, deriv_const_sub, deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
            mul_neg, neg_neg]
            norm_cast
            rw [Nat.factorial_succ, ← pow_mul', Nat.cast_mul]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.sub
            · apply differentiableAt_const
            · apply DifferentiableAt.mul
              · apply differentiableAt_const
              · apply differentiableAt_id
        · apply pow_ne_zero
          exact pow_ne_zero (n + 1) hne
        · exact pow_ne_zero (n + 1 + 1) hne
      · apply differentiableAt_const
      · apply DifferentiableAt.pow
        apply DifferentiableAt.sub
        · apply differentiableAt_const
        · apply DifferentiableAt.mul
          · apply differentiableAt_const
          · apply differentiableAt_id
      · exact pow_ne_zero (n + 1) hne

theorem differentiableAt_inv_special' (c x y z : ℝ) (n : ℕ) (hc : c ≠ 0) (hx : x ∈ Set.Ioo 0 1)
    (hz : z ∈ Set.Ioo 0 1) (h1 : 1 - (1 - x * y) * z = 0) :
    ¬DifferentiableAt ℝ (fun y ↦ c / (1 - (1 - x * y) * z) ^ (n + 1)) y := by
  intro h
  obtain q := h.continuousAt
  simp only [Metric.continuousAt_iff, gt_iff_lt, Real.dist_eq, h1, ne_eq,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, div_zero,
    dist_zero_right, norm_div, Real.norm_eq_abs, norm_pow] at q
  simp only [Set.mem_Ioo] at hx hz
  have h₁ : |c| > 0 := by simp [hc]
  specialize q (|c|) h₁
  rcases q with ⟨q, ⟨qq, qqq⟩⟩
  set d := min (q / 2 + y) (1 / |x * z| + y)
  set d' := min (q / 2) (1 / |x * z|)
  have h' : d = d' + y := by
    simp only [d, d']
    rw [min_add_add_right]
  have hd : |d - y| < q := by
    rw [h', show d' + y - y = d' by ring]
    suffices |d'| ≤ q / 2 by linarith
    rw [abs_of_nonneg (by positivity)]
    exact min_le_left (q / 2) (1 / |x * z|)
  have hd' : 1 - (1 - x * d) * z ≠ 0 := by
    suffices 1 - (1 - x * d) * z > 0 by linarith
    rw [h', show 1 - (1 - x * (d' + y)) * z =
      1 - (1 - x * y) * z + x * z * d' by ring, h1, zero_add]
    refine mul_pos (mul_pos (by linarith) (by linarith)) ?_
    simp only [d']
    apply lt_min (by positivity)
    simp only [one_div, inv_pos, abs_pos, ne_eq, mul_eq_zero, not_or]
    constructor <;> linarith
  specialize qqq hd
  rw [div_lt_iff₀] at qqq
  · rw [lt_mul_iff_one_lt_right h₁, h', show 1 - (1 - x * (d' + y)) * z =
      1 - (1 - x * y) * z + x * z * d' by ring, h1, zero_add,
      one_lt_pow_iff_of_nonneg (by positivity) (by norm_num)] at qqq
    have contra : |x * z * d'| ≤ 1 := by
      calc
      _ = |x * z| * |d'| := by rw [abs_mul]
      _ ≤ |x * z| * (1 / |x * z|) := by
        apply mul_le_mul (by linarith) _ (abs_nonneg _) (abs_nonneg _)
        rw [← abs_one_div]
        apply abs_le_abs_of_nonneg (by positivity)
        simp only [d']
        rw [abs_of_nonneg (mul_nonneg (by linarith) (by linarith) : 0 ≤ x * z)]
        exact min_le_right (q / 2) (1 / (x * z))
      _ = 1 := by
        rw [mul_div, mul_one, div_self]
        simp only [ne_eq, abs_eq_zero, mul_eq_zero, not_or]
        constructor <;> linarith
    linarith
  · apply pow_pos
    simp only [abs_pos]
    exact hd'

lemma n_derivative' {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
    (fun y ↦ (-1) ^ n * (n) ! * (x * z) ^ n / (1 - (1 - x * y) * z) ^ (n + 1)) := by
  induction n with
  | zero => simp
  | succ n hn =>
    ext y
    rcases eq_or_ne (1 - (1 - x * y) * z) 0 with (h | hne)
    · simp only [h, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, div_zero]
      simp only [Set.mem_Ioo] at hx hz
      rw [Function.iterate_succ_apply', hn]
      apply deriv_zero_of_not_differentiableAt
      set c := (-1) ^ n * ↑n ! * (x * z) ^ n
      have hc : c ≠ 0 := by
        simp only [c]
        apply mul_ne_zero
        · simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and,
            Nat.cast_eq_zero, Nat.factorial_ne_zero, or_self, not_false_eq_true]
        · apply pow_ne_zero
          nlinarith
      exact differentiableAt_inv_special' c x y z n hc hx hz h
    · rw [Function.iterate_succ_apply', hn, deriv_fun_div]
      · simp only [deriv_const', zero_mul, zero_sub]
        have h : (fun y ↦ (1 - (1 - x * y) * z) ^ (n + 1)) =
            fun y ↦ (1 - z + x * z * y) ^ (n + 1) := by
          ext _; ring
        rw [div_eq_div_iff]
        · rw [h, deriv_fun_pow, deriv_const_add, deriv_const_mul]
          · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one,
              ← neg_mul]
            rw [show -(-1) ^ n = (-1 : ℝ) ^ (n + 1) by ring,
              show ((n + 1)! : ℝ) = (((n : ℕ) + 1) : ℝ) * (n !) by
                rw [Nat.factorial_succ]; norm_cast]
            ring
          · apply differentiableAt_id
          · apply DifferentiableAt.add
            · apply differentiableAt_const
            · apply DifferentiableAt.mul
              · apply differentiableAt_const
              · apply differentiableAt_id
        · apply pow_ne_zero
          exact pow_ne_zero (n + 1) hne
        · exact pow_ne_zero (n + 1 + 1) hne
      · apply differentiableAt_const
      · apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_mul differentiableAt_id
      · exact pow_ne_zero (n + 1) hne

lemma shiftedLegendre_poly_eval_zero_eq_zero {n m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X, smul_eq_mul,
    mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff',
    ne_eq, true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := by exact h

lemma shiftedLegendre_poly_eval_one_eq_zero {n m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

lemma shiftedLegendre_continuousOn {n m : ℕ} : ContinuousOn
    (fun x ↦ eval x ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n : ℝ[X]))) (Set.uIcc 0 1) :=
  (Polynomial.continuous _).continuousOn

lemma special_deriv_div_continuousOn {m : ℕ} {x z : ℝ}
    (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    ContinuousOn (fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u) (Set.uIcc 0 1) := by
  simp_rw [n_derivative' m hx hz]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const continuousOn_id
  · intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, Set.mem_Ioo] at hy hx hz
    apply pow_ne_zero
    suffices 1 - (1 - x * y) * z > 0 by linarith
    simp only [sub_pos]
    suffices (1 - x * y) * z ≤ z by linarith
    apply mul_le_of_le_one_left (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith

lemma integral_shiftedLegendre_mul_smooth_eq_aux {x z : ℝ} (n m : ℕ) (h : m ≤ n)
    (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) : ∫ (y : ℝ) in (0)..1,
    eval y ((⇑derivative)^[n] (X ^ n * (1 - X) ^ n)) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ m * ∫ (y : ℝ) in (0)..1, eval y ((⇑derivative)^[n - m] (X ^ n * (1 - X) ^ n)) *
    (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) y:= by
  induction m with
  | zero => simp
  | succ m hm =>
    have h₀ : m < n := by linarith
    have h₁ : n - (m + 1) < n := by omega
    rw [hm (LT.lt.le h₀), pow_add, pow_one, mul_assoc]
    congr
    symm
    rw [show n - m = n - (m + 1) + 1 by omega, Function.iterate_succ_apply']
    rw [neg_one_mul, neg_eq_iff_eq_neg,
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun u ↦ eval u ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X])))
      (u' := fun u ↦ eval u (derivative ((⇑derivative)^[n - (m + 1)] (X ^ n * (1 - X) ^ n : ℝ[X]))))
      (v := fun u ↦ (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u)]
    · rw [shiftedLegendre_poly_eval_one_eq_zero h₁, shiftedLegendre_poly_eval_zero_eq_zero h₁]
      simp only [one_div, zero_mul, sub_self, zero_sub, Function.iterate_succ_apply']
    · apply shiftedLegendre_continuousOn
    · apply special_deriv_div_continuousOn hx hz
    · intro u _
      exact Polynomial.hasDerivAt _ u
    · intro y hy
      simp only [Set.mem_Ioo, zero_le_one, min_eq_left, max_eq_right] at hx hy hz
      have hh : 1 - (1 - x * y) * z ≠ 0 := by
        suffices 1 - (1 - x * y) * z > 0 by linarith
        simp only [sub_pos]
        suffices (1 - x * y) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
      have (u : ℝ) : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) u =
        Function.eval u (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z))) := by
        simp only [one_div, Function.eval]
      simp_rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval,
        n_derivative' _ hx hz]
      have : (-1) ^ (m + 1) * ↑(m + 1)! * (x * z) ^ (m + 1) / (1 - (1 - x * y) * z) ^ (m + 1 + 1)
        = (0 * (1 - (1 - x * y) * z) ^ (m + 1) -
        (-1) ^ m * ↑m ! * (x * z) ^ m * ((m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m)) /
        ((1 - (1 - x * y) * z) ^ (m + 1)) ^ 2 := by
        simp only [zero_mul, zero_sub]
        rw [div_eq_div_iff]
        · simp only [pow_add, ← neg_mul]
          rw [show -(-1 : ℝ) ^ m = (-1 : ℝ) ^ m * (-1) ^ 1 by ring,
            show ((m + 1)! : ℝ) = (((m : ℕ) + 1) : ℝ) * (m !) by rw [Nat.factorial_succ]; norm_cast]
          ring
        · apply pow_ne_zero _ hh
        · apply pow_ne_zero
          apply pow_ne_zero _ hh
      rw [this]
      apply HasDerivAt.div
      · apply hasDerivAt_const
      · have : (↑m + 1) * (x * z) * (1 - (1 - x * y) * z) ^ m =
            deriv (fun y ↦ (1 - (1 - x * y) * z) ^ (m + 1)) y := by
          simp only [show 1 - (1 - x * y) * z = 1 - z + x * z * y by ring]
          rw [deriv_fun_pow, show (fun y ↦ 1 - (1 - x * y) * z) =
            (fun y ↦ 1 - z + x * z * y) by ext _; ring]
          · rw [deriv_const_add, deriv_const_mul]
            · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one]
              norm_cast
              ring
            · exact differentiableAt_id
          · apply DifferentiableAt.const_sub
            apply DifferentiableAt.mul_const
            · apply DifferentiableAt.const_sub
              apply DifferentiableAt.const_mul differentiableAt_id
        simp only [this, hasDerivAt_deriv_iff]
        apply DifferentiableAt.pow
        apply DifferentiableAt.const_sub
        apply DifferentiableAt.mul_const
        · apply DifferentiableAt.const_sub
          apply DifferentiableAt.const_mul differentiableAt_id
      · apply pow_ne_zero _ hh
    · exact (Polynomial.continuous _).intervalIntegrable _ _
    · have : deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)) =
        (Function.eval · (deriv (deriv^[m] fun y ↦ 1 / (1 - (1 - x * y) * z)))) := by
        ext x
        simp only [one_div, Function.eval]
      rw [this]
      simp_rw [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Function.eval]
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      rw [← Set.uIcc_of_le (by norm_num)]
      apply special_deriv_div_continuousOn hx hz

lemma integral_legendre_mul_smooth_eq {x z : ℝ} (n : ℕ)
    (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (aperyShiftedLegendre n) * (fun y ↦ 1 / (1 - (1 - x * y) * z)) y =
    (- 1) ^ n / n ! * ∫ (y : ℝ) in (0)..1, y ^ n * (1 - y) ^ n *
    (deriv^[n] fun y ↦ 1 / (1 - (1 - x * y) * z)) y := by
  simp only [eval_mul, one_div, eval_C, aperyShiftedLegendre_eq_rodrigues]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_one_div, one_div]
  nth_rw 4 [mul_comm]
  rw [mul_assoc]
  congr
  obtain h := integral_shiftedLegendre_mul_smooth_eq_aux (n := n) (m := n) (by norm_num) hx hz
  simp only [one_div, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
    eval_mul, eval_pow, eval_X, eval_sub, eval_one] at h
  rw [h]
  simp_rw [← mul_assoc]

lemma legendre_integral_special {x z : ℝ} (n : ℕ) (hx : x ∈ Set.Ioo 0 1) (hz : z ∈ Set.Ioo 0 1) :
    ∫ (y : ℝ) in (0)..1, eval y (aperyShiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) =
    ∫ (y : ℝ) in (0)..1, (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
  rw [integral_legendre_mul_smooth_eq n hx hz, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_fun (by simp)
  intro y hy
  simp only
  rw [n_derivative' n hx hz]
  simp_all only [Set.mem_Ioo, Set.mem_Icc]
  rw [← mul_assoc, mul_div, div_eq_div_iff]
  · rw [mul_assoc, mul_assoc, mul_assoc, mul_comm, mul_div]
    symm
    rw [eq_div_iff]
    · symm
      calc
      _ = y ^ n * ((1 - y) ^ n * (↑n ! * (x * z) ^ n * (1 - (1 - x * y) * z) ^ (n + 1))) *
        ((-1) ^ n * (-1) ^ n) := by
        ring
      _ = (x * y * z) ^ n * (1 - y) ^ n * (1 - (1 - x * y) * z) ^ (n + 1) * ↑n ! := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp only [even_two, Even.neg_pow, one_pow, mul_one]
        ring
    · norm_cast
      exact Nat.factorial_ne_zero n
  · suffices (1 - (1 - x * y) * z) ^ (n + 1) > 0 by linarith
    apply pow_pos
    simp only [sub_pos]
    suffices (1 - x * y) * z ≤ z by linarith
    apply mul_le_of_le_one_left (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith
  · suffices (1 - (1 - x * y) * z) ^ (n + 1) > 0 by linarith
    apply pow_pos
    simp only [sub_pos]
    suffices (1 - x * y) * z ≤ z by linarith
    apply mul_le_of_le_one_left (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith

end Polynomial

end Zeta3_LegendrePoly

section Zeta3_d

/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/

/-!
# Least common multiples for the Apéry irrationality proof

We bound the least common multiple of the integers from one to `n` using prime counting.
The natural-number normalization and GCD structures are Mathlib's canonical instances.
-/

open scoped _root_.Nat
open _root_.BigOperators

/-- The least common multiple of the natural numbers in the finite set s. -/
def d (s : Finset ℕ) : ℕ := s.lcm id

theorem d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

theorem d_empty : d (∅ : Finset ℕ) = 1 := by simp [d]

theorem dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

theorem d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

theorem d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  intro r
  rw [Finset.lcm_eq_zero_iff] at r
  exact hs (by simpa using r)

theorem d_eq_zero (s : Finset ℕ) (hs : 0 ∈ s) : d s = 0 := by
  delta d
  rw [Finset.lcm_eq_zero_iff]
  simpa

theorem Nat.primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList, Finset.mem_union,
    Nat.mem_primeFactors_iff_mem_primeFactorsList, Nat.mem_primeFactors_iff_mem_primeFactorsList]
  simp only [Nat.mem_primeFactorsList', ne_eq]
  constructor
  · rintro ⟨hp1, hp2, hp3⟩
    obtain hp4|hp4 := hp1.dvd_or_dvd_of_dvd_lcm hp2
    · left; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
    · right; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
  · rintro (⟨hp1, hp2, hp3⟩|⟨hp1, hp2, hp3⟩)
    · refine ⟨hp1, hp2.trans <| dvd_lcm_left a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim id fun hb' => absurd hb' hb
    · refine ⟨hp1, hp2.trans <| dvd_lcm_right a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim (fun ha' => absurd ha' ha) id

theorem d_sq (s : Finset ℕ) : (d s) ^ 2 = d (s.image (· ^ 2)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s _ ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat.pow_lcm_pow]

theorem d_cube (s : Finset ℕ) : (d s) ^ 3 = d (s.image (· ^ 3)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s _ ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih, Nat.pow_lcm_pow]

theorem d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

theorem d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _

theorem fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

theorem lcm_factorization (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.lcm n).factorization p = max (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_lcm hm hn]
  aesop

theorem d_factorization (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    (d s).factorization p =
    (s.image fun i => i.factorization p).max' (by aesop) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s hm ih =>
    rw [d_insert, lcm_factorization _ _ _]
    · if hs : s.Nonempty
      then
      simp only [Finset.image_insert]
      rw [Finset.max'_insert (H := by aesop)]
      rw [ih hs (by aesop)]
      else
      simp only [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp [d_empty]
    · aesop
    · apply d_ne_zero
      aesop

theorem d_factorization' (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    ((d s).factorization p : ℝ) =
    (((s.image fun (i : ℕ) => (i.factorization p : ℝ)))).max' (by aesop) := by
  rw [d_factorization] <;> try aesop
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s _ ih =>
    simp_rw [Finset.image_insert]
    if hs : s.Nonempty
    then
    symm
    rw [Finset.max'_insert (H := by aesop)]
    specialize ih hs (by aesop)
    rw [← ih, ← Nat.cast_max]
    norm_cast
    rw [← Finset.max'_insert (H := by aesop)]
    else
    aesop

theorem d_primeFactors (s : Finset ℕ) (hs : 0 ∉ s) :
    (d s).primeFactors = s.sup fun i => i.primeFactors := by
   induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.bot_eq_empty, Nat.primeFactors_eq_empty]
    right
    simp only [d_empty]
  | @insert m s hm ih =>
    simp only [Finset.mem_insert, not_or] at hs
    rw [d_insert, Nat.primeFactors_lcm (by aesop) (d_ne_zero _ (by aesop))]
    simp only [Finset.sup_insert, Finset.sup_eq_union]
    rw [ih (by aesop)]

theorem d_factorization_eq_div_log'' (p : ℕ) :
    (d (Finset.Icc 1 0)).factorization p =
    ⌊Real.log 0 / Real.log p⌋₊ := by
  simp [d_empty]

theorem d_factorization_eq_div_log' (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 (n + 1))).factorization p =
    ⌊Real.log (n + 1) / Real.log p⌋₊ := by
  symm
  rw [Real.log_div_log]
  rw [Nat.floor_eq_iff]
  · rw [d_factorization']
    · constructor
      · rw [Finset.max'_le_iff]
        intro y hy
        rw [Real.le_logb_iff_rpow_le]
        · simp only [Finset.mem_image, Finset.mem_Icc] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have h := @Nat.pow_factorization_choose_le p x 1 (by omega)
          norm_cast
          simp only [Nat.choose_one_right] at h
          linarith
        · norm_cast
          exact Nat.Prime.one_lt hp
        · norm_cast
          omega
      · rw [← sub_lt_iff_lt_add]
        · by_contra! h
          rw [Finset.max'_le_iff] at h
          set y := (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))).max' (by aesop)
          have hy : (y : ℝ) ∈
              (Finset.image (fun i ↦ (i.factorization p : ℝ)) (Finset.Icc 1 (n + 1))) := by
            simp only [Finset.mem_image, Finset.mem_Icc, Nat.cast_inj]
            simp_rw [← Finset.mem_Icc]
            rw [← Finset.mem_image]
            exact Finset.max'_mem _ _
          specialize h (y : ℝ) hy
          rw [le_sub_iff_add_le, Real.le_logb_iff_rpow_le] at h
          · have h2 : y + 1 ∉
                (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))) := by
              by_contra! hy1
              suffices y + 1 ≤ y by linarith
              exact Finset.le_max' _ _ hy1
            simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and, and_imp] at h2
            norm_cast at h
            specialize h2 (p ^ (y + 1)) (by exact one_le_pow_of_one_le' (Nat.Prime.one_le hp) _) h
            aesop
          · norm_cast
            exact Nat.Prime.one_lt hp
          · norm_cast
            omega
    · aesop
    · simp
  · apply Real.logb_nonneg
    · norm_cast
      exact Nat.Prime.one_lt hp
    · norm_cast
      omega

theorem d_factorization_eq_div_log (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 n)).factorization p =
    ⌊Real.log n / Real.log p⌋₊ := by
  cases n
  · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, d_empty, Nat.factorization_one,
    Finsupp.coe_zero, Pi.zero_apply, CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.floor_zero]
  · rw [d_factorization_eq_div_log' (hp := hp)]
    simp

theorem d_eq_prod_pow' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ((Finset.Icc 1 (n + 1)).image (fun i => i.factorization p)).max' (by aesop) := by
  rw [← Nat.prod_factorization_pow_eq_self (n := d (Finset.Icc 1 (n + 1)))]
  · simp only [Finsupp.prod, Nat.support_factorization]
    rw [d_primeFactors _ (by aesop)]
    refine Finset.prod_congr ?_ ?_
    · ext p
      constructor <;> intro hp
      · rw [Finset.mem_sup] at hp
        obtain ⟨m, H, h⟩ := hp
        simp only [Finset.mem_Icc] at H
        rw [Nat.mem_primesBelow]
        simp only [Nat.mem_primeFactors, ne_eq] at h
        constructor
        · linarith [Nat.le_of_dvd (by omega) h.2.1]
        · exact h.1
      · rw [Finset.mem_sup]
        use p
        simp only [Finset.mem_Icc, Nat.mem_primeFactors, dvd_refl, ne_eq, true_and]
        rw [Nat.mem_primesBelow] at hp
        constructor
        · exact ⟨Nat.Prime.one_le hp.2, (by linarith)⟩
        · aesop
    · intro p _
      rw [d_factorization]
      · aesop
      · simp
  · apply d_ne_zero
    aesop

theorem d_eq_prod_pow'' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ⌊(Real.log ((n + 1) : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  rw [d_eq_prod_pow']
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp only [Nat.mem_primesBelow] at hp
  congr 1
  have eq := d_factorization_eq_div_log (n + 1) p
  simp only [Nat.cast_add, Nat.cast_one] at eq
  rw [← eq, d_factorization] <;> aesop

theorem d_eq_prod_pow (n : ℕ) :
    d (Finset.Icc 1 n) =
    ∏ p ∈ ((n + 1).primesBelow),
      p ^ ⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  cases n
  · simp [d_empty]
  · rw [d_eq_prod_pow'']
    simp

theorem d_le_pow_counting (n : ℕ) : d (Finset.Icc 1 n) ≤ n ^ (n.primeCounting) := by
  if h : n = 0 then
    rw [h]; aesop
  else
    have h1 : 1 ≤ n := by omega
    rw [d_eq_prod_pow n]
    calc
    _ ≤ ∏ _ ∈ ((n + 1).primesBelow), n := by
      apply Finset.prod_le_prod'
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      have h2 : 1 ≤ p := by
        by_contra! h
        have : p = 0 := by omega
        aesop
      suffices p ^ (⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ : ℝ) ≤ (n : ℝ) by norm_cast at this
      trans p ^ ((Real.log (n : ℝ)) / (Real.log (p : ℝ)))
      · apply Real.rpow_le_rpow_of_exponent_le (by norm_cast)
        · apply Nat.floor_le (R := ℝ)
          if h2 : n = 1 ∨ p = 1 then
            rcases h2 with (rfl | rfl) <;> simp
          else
            rcases (not_or.1 h2) with ⟨_, h2⟩
            have h1 : 1 < n := by omega
            have h2 : 1 < p := by omega
            suffices 0 < Real.log (n : ℝ) / Real.log (p : ℝ) by linarith
            apply div_pos <;>
            exact Real.log_pos (by norm_cast)
      · nth_rewrite 1 [← Real.exp_log (x := (p : ℝ)) (by norm_cast), ← Real.exp_one_rpow,
          ← Real.rpow_mul (by exact Real.exp_nonneg 1), mul_div, mul_comm, ← mul_div]
        if hp : p = 1 then
          rw [hp]; simp only [Nat.cast_one, Real.log_one, div_zero, mul_zero, Real.rpow_zero,
            Nat.one_le_cast, h1]
        else
          rw [div_self, mul_one, Real.exp_one_rpow, Real.exp_log (by norm_cast)]
          rw [Real.log_ne_zero]
          norm_cast
          simp only [not_false_eq_true, and_true]
          omega
    _ ≤ n ^ (n.primeCounting) := by
      rw [Finset.prod_const]
      suffices ((n + 1).primesBelow).card = n.primeCounting by
        apply Nat.pow_le_pow_right <;> linarith
      rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']

end Zeta3_d

section Zeta3_Integral

/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/

/-! Integral identities in the Apache-2.0 Apéry proof of Junqi Liu and Jujian Zhang. -/

open scoped _root_.Nat
open _root_.BigOperators _root_.Finset

/-- The real Apéry double integral with monomial weights of degrees `r` and `s`. -/
noncomputable abbrev J (r s : ℕ) : ℝ :=
  ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  -(x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s

/-- The nonnegative extended-real Apéry double integral with weights of degrees `r` and `s`. -/
noncomputable abbrev jENN (r s : ℕ) : ENNReal :=
  ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)

lemma log_rpow_integral_aux (n : ℝ) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, |-x.log * x ^ n| = ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n := by
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x hx
  simp only [Set.mem_Ioc, neg_mul, abs_neg, abs_eq_neg_self] at *
  rw [mul_nonpos_iff]
  right
  constructor
  · apply Real.log_nonpos <;> linarith
  · apply Real.rpow_nonneg
    linarith

lemma log_rpow_integral' (n : ℝ) (hn : n > -1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n =
    1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) := by
  let f := fun x : ℝ => x ^ (n + 1) /(n + 1) ^ 2 - x ^ (n + 1) * x.log /(n + 1)
  rw [show 1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) =
    f 1 - f a by simp[f], ← intervalIntegral.integral_of_le ha.2]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 (a := a) (b := 1) (f := f)
    (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_
  · simp only [f]
    refine ContinuousOn.sub (ContinuousOn.div_const ?_ (((n : ℝ) + 1) ^ 2)) ?_
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
      linarith
    · apply ContinuousOn.div_const
      apply ContinuousOn.mul
      · apply ContinuousOn.rpow_const continuousOn_id
        intro x hx
        left
        simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
        linarith
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq] at hx ⊢
        linarith
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [f]
    rw [show -x.log * x ^ n = x ^ n / (↑n + 1) - (x ^ n * x.log + x ^ n / (↑n + 1)) by ring]
    apply HasDerivAt.sub
    · have h : x ^ n / (↑n + 1) = x ^ n * (↑n + 1) / (↑n + 1) ^ 2 := by
        rw[div_eq_div_iff (by linarith)]
        · ring
        · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
          linarith
      rw [h]
      apply HasDerivAt.div_const
      rw [mul_comm]
      nth_rw 3 [show n = n + 1 - 1 by simp]
      norm_cast
      apply Real.hasDerivAt_rpow_const
      left ; linarith
    · have h : x ^ n * x.log + x ^ n / (↑n + 1) =
          ((↑n + 1) * x ^ n * x.log + x ^ n) / (↑n + 1) := by
        rw [add_div]
        congr 1
        rw [eq_div_iff (by linarith)]
        ring
      rw[h]
      apply HasDerivAt.div_const
      nth_rw 2 [show x ^ n = x ^ (n + 1) * (1 / x) by rw [mul_div, eq_div_iff (by linarith),
        Real.rpow_add (by linarith), mul_one, Real.rpow_one]]
      apply HasDerivAt.mul
      · nth_rw 3 [show n = n + 1 - 1 by simp]
        norm_cast
        apply Real.hasDerivAt_rpow_const
        left ; linarith
      · apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le ha.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le ha.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith

lemma log_rpow_integrable (n : ℝ) (hn : n > -1) :
    IntervalIntegrable (fun x ↦ -Real.log x * x ^ n) MeasureTheory.volume 0 1 := by
  let f := fun (x : ℝ) => -x.log * x ^ n
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num), integrableOn_Icc_iff_integrableOn_Ioc]
  apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (f := f)
    (l := Filter.atTop) (a := fun (n : ℕ) => 1 / (n + 1 : ℝ)) (a₀ := 0) (b := 1)
    (I := 1 / (n + 1) ^ 2)
  · intro i
    simp only [one_div, f]
    have hi :  0 < ((i : ℝ) + 1)⁻¹ ∧ ((i : ℝ) + 1)⁻¹ ≤ 1 := by
      constructor
      · simp only [inv_pos]; linarith
      · rw [← one_div, div_le_iff₀] <;> linarith
    rw [← Set.uIoc_of_le hi.2, ← intervalIntegrable_iff]
    apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le hi.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hi.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [Filter.eventually_atTop]
    use 0
    intro b _
    simp only [Real.norm_eq_abs, f]
    rw [log_rpow_integral_aux n]
    · rw [log_rpow_integral' n hn]
      · set k := _
        change _ - k ≤ _
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right,
          sub_nonneg, k]
        rw [div_le_div_iff₀ (by linarith) (by nlinarith), mul_assoc, mul_le_mul_iff_of_pos_left]
        · trans 0
          · rw [mul_nonpos_iff]
            right
            constructor
            · apply Real.log_nonpos
              · simp only [one_div, inv_nonneg]
                linarith
              · rw [div_le_iff₀] <;> linarith
            · positivity
          · linarith
        · apply Real.rpow_pos_of_pos
          simp only [one_div, inv_pos]
          linarith
      · constructor
        · positivity
        · rw [div_le_one] <;> linarith
    · constructor
      · positivity
      · rw [div_le_one] <;> linarith

lemma log_rpow_integral (n : ℝ) (hn : n > -1) :
    ∫ (x : ℝ) in (0)..1, -x.log * x ^ n = 1 / (n + 1) ^ 2 := by
  let F := fun (x : ℝ) => x ^ (n + 1) * (1 - (n + 1) * x.log) / (n + 1) ^ 2
  have h1 : 1 /(n + 1) ^ 2 = F 1 - F 0 := by
    simp only [F, Real.one_rpow, Real.log_one, mul_zero, sub_zero,
      Real.log_zero, mul_one]
    rw [Real.zero_rpow (by linarith), zero_div, sub_zero]
  rw [h1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) (a := 0) (b := 1)
    (f := F) (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [F, mul_sub, mul_one]
    have : -Real.log x * x ^ n = -Real.log x * x ^ n * (n + 1) ^ 2 / (n + 1) ^ 2 := by
      rw [eq_div_iff]
      nlinarith
    rw [this]
    apply HasDerivAt.div_const
    rw [show -Real.log x * x ^ n * (n + 1) ^ 2 =
      (n + 1) * x ^ n - ((n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2) by ring]
    apply HasDerivAt.sub
    · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
      add_sub_cancel_right]]
      apply HasDerivAt.rpow_const (hasDerivAt_id' x)
      left; linarith
    · have : (n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2 =
        (n + 1) * x ^ n * ((n + 1) * Real.log x) +  x ^ (n + 1) * ((n + 1) / x) := by
        rw [← mul_comm_div, ← Real.rpow_sub_one (by linarith)]
        ring_nf
      rw [this]
      apply HasDerivAt.mul
      · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
          add_sub_cancel_right]]
        apply HasDerivAt.rpow_const (hasDerivAt_id' x)
        left; linarith
      · apply HasDerivAt.const_mul
        rw [← one_div]
        apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · exact log_rpow_integrable n hn
  · simp only [Real.log_zero, mul_zero, sub_zero, mul_one, F]
    rw [Real.zero_rpow (by linarith), zero_div]
    simp_rw [mul_sub, sub_div]
    nth_rw 3 [show (0 : ℝ) = 0 / (n + 1) ^ 2 - 0 / (n + 1) ^ 2 by simp]
    refine Filter.Tendsto.sub (a := 0 / (n + 1) ^ 2) (b := 0 / (n + 1) ^ 2) ?_ ?_
    · apply Filter.Tendsto.div_const
      simp_rw [mul_one]
      nth_rw 3 [show (0 : ℝ) = 0 ^ (n + 1) by rw [Real.zero_rpow (by linarith)]]
      apply Filter.Tendsto.rpow_const
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        exact fun ⦃U⦄ a ↦ a
      · right; linarith
    · apply Filter.Tendsto.div_const
      simp only [← mul_assoc, ← mul_rotate (c := n + 1)]
      nth_rw 3 [show (0 : ℝ) = 0 * (n + 1) by simp]
      apply Filter.Tendsto.mul_const
      apply tendsto_log_mul_rpow_nhdsGT_zero
      linarith
  · apply tendsto_nhds_of_tendsto_nhdsWithin (s := ⊤)
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · apply ContinuousAt.continuousWithinAt
      simp only [F]
      apply ContinuousAt.div_const
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const continuousAt_id
        right; linarith
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.log continuousAt_id (by norm_num)
    · intro _ _
      simp

lemma ENN_log_rpow_integral (n : ℝ) (hn : n > -1) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  calc
  _ = ∫⁻ (x : ℝ), ENNReal.ofReal ((Set.Ioo 0 1).indicator (fun x => -Real.log x * x ^ n) x) := by
    rw [← MeasureTheory.lintegral_indicator]
    · congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      aesop
    · measurability
  _ = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · rw [MeasureTheory.integral_indicator (by measurability),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num), log_rpow_integral n hn]
    · apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact log_rpow_integrable n hn
    · refine MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
      · rintro s - -
        apply MeasureTheory.Integrable.integrableOn
        apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
        rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact log_rpow_integrable n hn
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg hs
        suffices  ∀ x, 0 ≤ (Set.Ioo 0 1).indicator (fun x ↦ -Real.log x * x ^ n) x by aesop
        intro x
        rw [Set.indicator_apply]
        by_cases h : x ∈ Set.Ioo 0 1
        · simp only [h, ↓reduceIte, neg_mul, Left.nonneg_neg_iff]
          simp only [Set.mem_Ioo] at h
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos <;> linarith
          · apply Real.rpow_nonneg; linarith
        · simp only [h, ↓reduceIte, le_refl]

lemma ENN_log_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  rw [← ENN_log_rpow_integral]
  · norm_cast
  · suffices 0 ≤ n by linarith
    omega

lemma ENN_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ n) = ENNReal.ofReal (1 / (n + 1)) := by
  have h := @integral_pow 0 1 n
  rw [zero_pow, one_pow, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  · rw [← h, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact intervalIntegral.intervalIntegrable_pow n
    · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      · rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact intervalIntegral.intervalIntegrable_pow n
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg (by measurability)
        intro x hs
        simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
        by_cases h : x ∈ s
        · simp only [h, true_and] at hs
          apply pow_nonneg
          linarith
        · tauto
  · omega

lemma AEMeasurable_aux {r s : ℕ} : AEMeasurable (fun (x : ℝ × ℝ × ℝ) ↦
    1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) MeasureTheory.volume := by
  fun_prop

lemma integral1 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp only [one_div]
  rw [intervalIntegral.integral_comp_sub_left, sub_sub_cancel, sub_zero, eq3]
  simp

lemma sub_mul_mul_ne_zero (y : ℝ) (x : ℝ × ℝ)
    (hy : y ∈ Set.Icc 0 1) (h1 : 0 < 1 - (1 - x.1 * x.2)) : 1 - (1 - x.1 * x.2) * y ≠ 0 := by
  suffices 1 - (1 - x.1 * x.2) * y > 0 by linarith
  simp only [gt_iff_lt, sub_pos]
  by_cases hy' : y = 0
  · rw [hy']
    simp
  · simp only [sub_pos, Set.mem_Icc] at *
    suffices (1 - x.1 * x.2) * y < y by linarith
    rwa [mul_lt_iff_lt_one_left]
    rcases hy with ⟨hy1, _⟩
    by_contra! h
    suffices y = 0 by tauto
    linarith

lemma integrableOn_aux (x : ℝ × ℝ)
    (h1 : 0 < 1 - (1 - x.1 * x.2)) (h2 : 1 - (1 - x.1 * x.2) < 1) :
    MeasureTheory.IntegrableOn (fun t ↦ 1 / (1 - (1 - x.1 * x.2) * t))
    (Set.Ioo 0 1) MeasureTheory.volume := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (g := fun t => -Real.log (1 - (1 - x.1 * x.2) * t) / (1 - x.1 * x.2))
  · apply ContinuousOn.div_const
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const continuousOn_id
    · intro y hy
      exact sub_mul_mul_ne_zero y x hy h1
  · intro y hy
    have h : 1 / (1 - (1 - x.1 * x.2) * y) =
      -(-(1 - x.1 * x.2)) / (1 - (1 - x.1 * x.2) * y) / (1 - x.1 * x.2) := by
      rw [neg_neg, div_div, div_eq_div_iff]
      · ring
      · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
      · apply mul_ne_zero (sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1)
        suffices 1 - x.1 * x.2 > 0 by linarith
        linarith
    rw [h]
    apply HasDerivAt.div_const
    rw [neg_div]
    apply HasDerivAt.neg
    apply HasDerivAt.log
    · apply HasDerivAt.const_sub
      nth_rw 2 [← mul_one (a := 1 - x.1 * x.2)]
      apply HasDerivAt.const_mul _ (hasDerivAt_id' y)
    · exact sub_mul_mul_ne_zero y x (Set.mem_Icc_of_Ioo hy) h1
  · intro y hy
    simp at hy
    apply div_nonneg (by norm_num)
    simp only [sub_nonneg]
    exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)

lemma JENN_eq_triple_aux' (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w)) =
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
  have h1 : 0 < 1 - (1 - x.1 * x.2) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    apply mul_pos (by linarith) (by linarith)
  have h2 : 1 - (1 - x.1 * x.2) < 1 := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    suffices x.1 * x.2 < x.2 by linarith
    aesop
  nth_rw 3 [show 1 - x.1 * x.2 = 1 - (1 - (1 - x.1 * x.2)) by simp]
  rw [←  integral1 (a := 1 - (1 - x.1 * x.2)) h1 h2,
    show 1 - (1 - (1 - x.1 * x.2)) = 1 - x.1 * x.2 by simp]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · apply MeasureTheory.IntegrableOn.integrable
    exact integrableOn_aux x h1 h2
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_aux x h1 h2
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hs
      simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
      by_cases h : y ∈ s
      · simp only [h, true_and] at hs
        apply div_nonneg (by norm_num)
        simp only [sub_nonneg]
        exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)
      · tauto

lemma JENN_eq_triple_aux {r s : ℕ} (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) =
    ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
  calc
  _ = ENNReal.ofReal (x.1 ^ r * x.2 ^ s) *
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
    rw [← JENN_eq_triple_aux' x hx]
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · congr 1
        field_simp
      rcases x with ⟨x1, x2⟩
      rcases hx with ⟨⟨hx1, hx1'⟩, ⟨hx2,hx2'⟩⟩
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.const_mul measurable_id
  _ = ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    rw [mul_comm, ← ENNReal.ofReal_mul, ← mul_assoc]
    apply div_nonneg
    · simp only [Left.nonneg_neg_iff]
      apply Real.log_nonpos
      · apply mul_nonneg (by linarith) (by linarith)
      · exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)
    · simp only [sub_nonneg]
      exact (mul_le_of_le_one_left (by linarith) (by linarith)).trans (by linarith)

lemma JENN_eq_triple (r s : ℕ) : jENN r s =
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) := by
  symm
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫⁻ (w : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod, MeasureTheory.lintegral_lintegral_swap]
    · simp only
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    apply MeasureTheory.setLIntegral_congr_fun (by measurability)
    intro x hx
    dsimp only
    rw [JENN_eq_triple_aux _ hx]

lemma AEMeasurable_aux' {k r s : ℕ} : AEMeasurable
    (fun x ↦ ENNReal.ofReal (-Real.log (x.1 * x.2) * x.1 ^ (k + r) * x.2 ^ (k + s)))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  apply AEMeasurable.ennreal_ofReal
  apply Measurable.aemeasurable
  apply Measurable.mul _ (Measurable.pow_const measurable_snd _)
  · apply Measurable.mul _ (Measurable.pow_const measurable_fst _)
    · apply Measurable.neg
      apply Measurable.log
      apply Measurable.mul measurable_fst measurable_snd

lemma aux_lintegral1 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) : ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log x * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
  calc
  _ = ENNReal.ofReal (-Real.log x * x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      rw [← ENNReal.ofReal_mul]
      · field_simp
      rcases hx with ⟨hx1, hx2⟩
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      exact ⟨Real.log_nonpos (by linarith) (by linarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      constructor
      · apply Real.log_nonpos (by linarith) (by nlinarith)
      · apply pow_nonneg (by linarith)

lemma aux_lintegral2 (k r s : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) : ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-(Real.log a * x ^ (k + r) * a ^ (k + s)))
    = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
  calc
  _ = ENNReal.ofReal (x ^ (k + r)) * ∫⁻ (a : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-a.log * a ^ (k + s)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · congr
      ext y
      cases hx
      rw [← ENNReal.ofReal_mul]
      · congr 1
        ring
      positivity
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div]
    · norm_cast
    · apply pow_nonneg (by linarith)

lemma aux_lintegral3 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1))
    = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
  calc
  _ = (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (-x.log * x ^ (k + r))) *
      ENNReal.ofReal (1 / (k + s + 1)) := by
    rw [← MeasureTheory.lintegral_mul_const]
    · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      rintro y ⟨hy1, hy2⟩
      dsimp only
      rw [← ENNReal.ofReal_mul]
      · field_simp
      simp only [neg_mul, Left.nonneg_neg_iff]
      rw [mul_nonpos_iff]
      right
      refine ⟨Real.log_nonpos (by linarith) (by nlinarith), by positivity⟩
    · apply Measurable.ennreal_ofReal
      apply Measurable.mul
      · apply Measurable.neg
        apply Measurable.log measurable_id
      · apply Measurable.pow measurable_id measurable_const
  _ = ENNReal.ofReal (1 / ((k + r + 1) ^ 2 * (k + s + 1))) := by
    rw [ENN_log_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma aux_lintegral4 (k r s : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2)
    = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) :=
  calc
  _ = (∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (x ^ (k + r))) *
      ENNReal.ofReal (1 / (k + s + 1) ^ 2) := by
      rw [← MeasureTheory.lintegral_mul_const]
      · apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro y ⟨hy1, hy2⟩
        dsimp only
        rw [← ENNReal.ofReal_mul]
        · field_simp
        positivity
      · measurability
  _ = ENNReal.ofReal (1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    rw [ENN_pow_integral, ← ENNReal.ofReal_mul, mul_one_div, div_div]
    · norm_cast
    · positivity

lemma J_ENN_rs_eq_tsum_aux_intergal (r s k : ℕ) :
    ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) = ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod]
  · calc
    _ = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
      ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2) := by
      apply MeasureTheory.setLIntegral_congr_fun (by measurability)
      intro x hx
      dsimp only
      simp only [neg_mul]
      have h2 : ∫⁻ (y : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal (-((x * y).log * x ^ (k + r) * y ^ (k + s)))
        = ∫⁻ (y : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (-(x.log * x ^ (k + r) * y ^ (k + s))) +
        ENNReal.ofReal (-(y.log * x ^ (k + r) * y ^ (k + s))) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        intro y hy
        dsimp only
        simp only [← neg_mul]
        simp only [Set.mem_Ioo] at hx hy
        rw [Real.log_mul (by linarith) (by linarith), neg_add, add_mul, add_mul,
          ENNReal.ofReal_add]
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · simp only [Set.mem_Ioo] at hx
        rw [aux_lintegral1 k r s x hx, aux_lintegral2 k r s x hx, ENNReal.ofReal_add, neg_mul]
        · apply div_nonneg _ (by positivity)
          simp only [Left.nonneg_neg_iff]
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos (by linarith) (by nlinarith)
          · apply pow_nonneg (by linarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.neg
        apply Measurable.const_mul
        exact Measurable.pow_const measurable_id _
    _ = ENNReal.ofReal
      (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
      have h2 : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal (- x.log * x ^ (k + r) / (k + s + 1) + x ^ (k + r) / (k + s + 1) ^ 2)
        = ∫⁻ (x : ℝ) in Set.Ioo 0 1,
        ENNReal.ofReal (-x.log * x ^ (k + r) / (k + s + 1)) +
        ENNReal.ofReal (x ^ (k + r) / (k + s + 1) ^ 2) := by
        apply MeasureTheory.setLIntegral_congr_fun (by measurability)
        rintro x ⟨hx1, hx2⟩
        dsimp only
        rw [ENNReal.ofReal_add]
        · apply div_nonneg _ (by positivity)
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · apply div_nonneg _ (by positivity)
          apply pow_nonneg (by linarith)
      rw [h2, MeasureTheory.lintegral_add_left']
      · rw [aux_lintegral3 k r s, aux_lintegral4 k r s, ENNReal.ofReal_add]
        · apply div_nonneg (by norm_num) (by positivity)
        · apply div_nonneg (by norm_num) (by positivity)
      · apply AEMeasurable.ennreal_ofReal
        apply Measurable.aemeasurable
        apply Measurable.div_const
        apply Measurable.mul
        · apply Measurable.neg
          apply Measurable.log measurable_id
        · exact Measurable.pow_const measurable_id _
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact AEMeasurable_aux'

lemma J_ENN_rs_eq_tsum (r s : ℕ) : jENN r s = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑' (k : ℕ), ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [jENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    congr
    ext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h1 : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h1, ↓reduceIte, div_eq_mul_inv]
      simp only [Set.mem_prod, Set.mem_Ioo] at h1
      rw [← tsum_geometric_of_lt_one]
      · rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg]
        · simp only [neg_mul, pow_add, mul_pow, ← mul_assoc]
          congr
          ext k
          nth_rw 2 [mul_assoc]
          nth_rw 4 [mul_assoc]
          nth_rw 5 [mul_comm]
        · intro n
          rw [mul_pow, ← mul_assoc]
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          apply mul_nonneg _ (by apply pow_nonneg (by linarith))
          simp only [Left.nonneg_neg_iff]
          apply Real.log_nonpos (by nlinarith) (by nlinarith)
        · simp_rw [← smul_eq_mul]
          apply Summable.smul_const (a := y.2 ^ s)
          apply Summable.smul_const (a := y.1 ^ r)
          apply Summable.const_smul (b := -(y.1 • y.2).log)
          apply summable_geometric_of_lt_one <;> rw [smul_eq_mul] <;> nlinarith
      · nlinarith
      · nlinarith
    · simp only [h1, ↓reduceIte]
  _ = ∑' (k : ℕ), ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (- (x.1 * x.2).log * x.1 ^ (k + r) * x.2 ^ (k + s)) := by
    rw [MeasureTheory.lintegral_tsum]
    intro n
    exact AEMeasurable_aux'
  _ = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ 2)) := by
    simp_rw [J_ENN_rs_eq_tsum_aux_intergal r s]

lemma J_ENN_rr (r : ℕ) : jENN r r = ENNReal.ofReal
    (2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) := by
  have h : jENN r r = ∑' (k : ℕ), ENNReal.ofReal (2 / ((k + r + 1) ^ 3)) := by
    rw [J_ENN_rs_eq_tsum r r]
    congr
    ext k
    rw [← pow_one (a := (k : ℝ) + r + 1), ← pow_mul, ← pow_add, ← pow_add, one_mul]
    simp only [Nat.reduceAdd, pow_one, ← two_mul, mul_one_div]
  rw [h]
  have h1 : ∑' (k : ℕ), 2 / (((k : ℝ) + r + 1) ^ 3) =
    2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
    symm
    apply sub_eq_of_eq_add
    rw [← Summable.sum_add_tsum_nat_add' (k := r) (f := fun k => 1 / ((k : ℝ) + 1) ^ 3),
      mul_add, add_comm, ← tsum_mul_left]
    · simp only [mul_one_div]
      congr 1
      · norm_cast
      · congr 1
        rw [← Finset.Ico_add_one_right_eq_Icc]
        have h1 := Finset.sum_Ico_eq_sum_range (m := 1) (n := r + 1) (f := fun k => 1 / (k : ℝ) ^ 3)
        simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at h1
        simp only [h1, add_comm]
    · norm_cast
      simp only [add_assoc, Nat.cast_pow]
      rw [summable_nat_add_iff (k := r + 1) (f := fun k => 1 / (k ^ 3 : ℝ)),
        Real.summable_one_div_nat_pow (p := 3)]
      norm_num
  rw [← h1, ENNReal.ofReal_tsum_of_nonneg]
  · intro n
    positivity
  · norm_cast
    simp only [add_assoc, Nat.cast_pow]
    rw [summable_nat_add_iff (k := r + 1) (f := fun k => 2 / (k ^ 3 : ℝ))]
    have h2 := Real.summable_one_div_nat_pow (p := 3)
    simp only [Nat.one_lt_ofNat] at h2
    apply Iff.symm at h2
    rw [true_iff, ← summable_mul_left_iff (a := 2) (by norm_num)] at h2
    simp only [mul_one_div] at h2
    exact h2

lemma fun_of_J_nonneg (r s : ℕ) (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    0 ≤ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s := by
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  apply mul_nonneg
  · apply mul_nonneg
    · rw [div_nonneg_iff]
      left
      constructor
      · simp only [Left.nonneg_neg_iff]
        apply Real.log_nonpos <;> nlinarith
      · nlinarith
    · apply pow_nonneg (by linarith)
  · apply pow_nonneg (by linarith)

lemma integrableOn_J_rr (r : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ r)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h := J_ENN_rr r
  simp only [jENN] at h
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ r) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            apply Real.log_nonpos <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]; nlinarith
          · simp only [abs_eq_self]; nlinarith
          · simp only [abs_eq_self]; nlinarith
        · positivity
        · exact fun_of_J_nonneg r r x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h]
    simp only [one_div, ENNReal.ofReal_lt_top]

theorem J_rr (r : ℕ) :
    J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m ∈ Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  have h := J_ENN_rr r
  simp only [jENN] at h
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h, ENNReal.toReal_ofReal_eq_iff]
  · simp only [sub_nonneg]
    apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Finset.Ico_add_one_right_eq_Icc]
    nth_rw 1 [← zero_add (a := 1)]
    rw [← Finset.sum_Ico_add' (c := 1)]
    norm_cast
    apply Summable.sum_le_tsum
    · intro i _; positivity
    · norm_cast
      simp only [Nat.cast_pow]
      rw [summable_nat_add_iff (k := 1) (f := fun k => 1 / (k ^ 3 : ℝ)),
        Real.summable_one_div_nat_pow (p := 3)]
      norm_num
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rr r
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r r y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

theorem zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [J_rr, one_div, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
    sub_zero]

lemma positivity_aux (r s : ℕ) (h : r > s) :
    ∀ (i : ℕ), 0 ≤ 1 / ((r : ℝ) - s) * (1 / (i + s + 1) ^ 2 - 1 / (i + r + 1) ^ 2) := by
  intro n
  apply mul_nonneg
  · simp only [one_div, inv_nonneg, sub_nonneg, Nat.cast_le]; linarith
  · simp only [sub_nonneg]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    apply pow_le_pow_left₀ (by linarith)
    simp only [add_le_add_iff_right, add_le_add_iff_left, Nat.cast_le]
    linarith

lemma summable_aux (r : ℕ) : Summable fun (b : ℕ) ↦ 1 / ((b : ℝ) + r + 1) ^ 2 := by
  norm_cast
  simp only [add_assoc, Nat.cast_pow]
  rw [summable_nat_add_iff (k := r + 1) (f := fun k => 1 / (k ^ 2 : ℝ)),
    Real.summable_one_div_nat_pow (p := 2)]
  norm_num

lemma J_ENN_rs (r s : ℕ) (h : r > s) :
    jENN r s = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
  calc
  _ = ∑' (k : ℕ), ENNReal.ofReal (1 / (r - s) * (1 / (k + s + 1) ^ 2 - 1 / (k + r + 1) ^ 2)) := by
    rw [J_ENN_rs_eq_tsum]
    congr
    ext k
    set x := (k : ℝ) + r + 1
    set y := (k : ℝ) + s + 1
    have hy : y > 0 := by positivity
    have hxy : x - y > 0 := by
      rw [show (x : ℝ) - y = r - s by ring]
      simp only [gt_iff_lt, sub_pos, Nat.cast_lt]
      linarith
    rw [show r - s = (x : ℝ) - y by ring, ENNReal.ofReal_eq_ofReal_iff]
    · rw [div_add_div]
      · rw [div_sub_div]
        · rw [div_mul_div_comm, div_eq_div_iff]
          · ring
          · suffices 0 < x ^ 2 * y * (x * y ^ 2) by linarith
            positivity
          · suffices (x - y) * (y ^ 2 * x ^ 2) > 0 by linarith
            positivity
        · positivity
        · positivity
      · suffices x ^ 2 * y > 0 by linarith
        positivity
      · suffices x * y ^ 2 > 0 by linarith
        positivity
    · positivity
    · apply mul_nonneg (by positivity)
      simp only [sub_nonneg]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simp only [one_mul]
      apply pow_le_pow_left₀ (by linarith) (by linarith)
  _ = ENNReal.ofReal ((∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [ENNReal.ofReal_eq_ofReal_iff]
      · simp only [mul_sub]
        · rw [Summable.tsum_sub]
          · simp only [sum_div, div_div, ← one_div_mul_one_div_rev]
            apply sub_eq_of_eq_add
            rw [← Summable.sum_add_tsum_nat_add'
              (f := fun n => 1 / (r - s) * (1 / (n + (s : ℝ) + 1) ^ 2)) (k := r - s)]
            · congr 1
              · simp only [← Nat.cast_add, add_comm]
                rw [← Finset.sum_Ico_eq_sum_range (n := r) (m := s)
                  (f := fun k => 1 / (r - s) * (1 / ((k : ℝ) + 1) ^ 2)),
                  ← Finset.Ico_add_one_add_one_eq_Ioc,
                  ← Finset.sum_Ico_add' (c := 1) (b := r) (a := s)]
                norm_cast
              · congr
                ext n
                congr 1
                norm_cast
                rw [show n + (r - s) + s + 1 = n + r + 1 by omega]
            · simp_rw [← smul_eq_mul]
              apply Summable.const_smul
              simp only [Nat.cast_add]
              rw [Nat.cast_sub (n := r) (m := s) (by linarith)]
              simp only [add_sub, sub_add_cancel]
              exact summable_aux r
          · simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux s
          · simp_rw [← smul_eq_mul]
            apply Summable.const_smul
            exact summable_aux r
      · apply tsum_nonneg
        exact positivity_aux r s h
      · rw [sum_div]
        apply sum_nonneg
        intro i _
        rw [div_nonneg_iff]
        left
        simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
          true_and]
        linarith
    · exact positivity_aux r s h
    · simp_rw [← smul_eq_mul]
      apply Summable.const_smul
      apply Summable.sub
      · exact summable_aux s
      · exact summable_aux r

lemma integrableOn_J_rs' (r s : ℕ) (h : r > s) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  have h₀ := J_ENN_rs r s h
  simp only [jENN] at h₀
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
      ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · simp only [abs_eq_neg_self]
            apply Real.log_nonpos <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]; nlinarith
          · simp only [abs_eq_self]; nlinarith
          · simp only [abs_eq_self]; nlinarith
        · positivity
        · exact fun_of_J_nonneg r s x hx
      · simp only [hx, ↓reduceIte]
    rw [h1, h₀]
    simp only [one_div, ENNReal.ofReal_lt_top]

lemma J_rs' (r s : ℕ) (h : r > s) :
    J r s = (∑ k ∈ Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s) := by
  have h₀ := J_ENN_rs r s h
  simp only [jENN] at h₀
  rw [J, MeasureTheory.integral_eq_lintegral_of_nonneg_ae, h₀, ENNReal.toReal_ofReal_eq_iff]
  · rw [sum_div]
    apply sum_nonneg
    intro i _
    rw [div_nonneg_iff]
    left
    simp only [one_div, inv_nonneg, Nat.cast_nonneg, pow_nonneg, sub_nonneg, Nat.cast_le,
      true_and]
    linarith
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs' r s h
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_ENN_rs_symm (r s : ℕ) : jENN r s = jENN s r := by
  simp only [J_ENN_rs_eq_tsum, add_comm, mul_comm]

lemma integrableOn_J_rs (r s : ℕ) : MeasureTheory.IntegrableOn
    (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)
    (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) MeasureTheory.volume := by
  by_cases h : r > s
  · exact integrableOn_J_rs' r s h
  · by_cases h1 : s = r
    · rw [h1]
      exact integrableOn_J_rr r
    · have h2 : s > r := by
        by_contra!; apply h1; linarith
      rw [MeasureTheory.IntegrableOn, MeasureTheory.Integrable]
      constructor
      · apply AEMeasurable.aestronglyMeasurable
        apply Measurable.aemeasurable
        · apply Measurable.mul
          · apply Measurable.mul
            · apply Measurable.div
              · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
              · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
            · apply Measurable.pow measurable_fst measurable_const
          · apply Measurable.pow measurable_snd measurable_const
      · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have h1 : ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal ‖-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s‖ =
          ∫⁻ (a : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
          ENNReal.ofReal (-Real.log (a.1 * a.2) / (1 - a.1 * a.2) * a.1 ^ r * a.2 ^ s) := by
          rw [← MeasureTheory.lintegral_indicator (by measurability),
            ← MeasureTheory.lintegral_indicator (by measurability)]
          congr
          ext x
          rw [Set.indicator_apply, Set.indicator_apply]
          by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
          · simp only [hx, ↓reduceIte, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, norm_pow]
            simp only [Set.mem_prod, Set.mem_Ioo] at hx
            rw [ENNReal.ofReal_eq_ofReal_iff]
            · congr 3
              · simp only [abs_eq_neg_self]
                apply Real.log_nonpos <;> nlinarith
              · simp only [abs_eq_self, sub_nonneg]; nlinarith
              · simp only [abs_eq_self]; nlinarith
              · simp only [abs_eq_self]; nlinarith
            · positivity
            · exact fun_of_J_nonneg r s x hx
          · simp only [hx, ↓reduceIte]
        have h₀ := J_ENN_rs s r h2
        rw [J_ENN_rs_symm s r] at h₀
        simp only [jENN] at h₀
        rw [h1, h₀]
        simp only [one_div, ENNReal.ofReal_lt_top]

lemma J_eq_toReal_J_ENN (r s : ℕ) : J r s = (jENN r s).toReal := by
  rw [J, jENN, MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_J_rs r s
    · rintro x hx -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hy
      by_cases h : y ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · exact fun_of_J_nonneg r s y h
      · rw [Set.mem_inter_iff] at hy
        tauto
  · apply AEMeasurable.aestronglyMeasurable
    apply Measurable.aemeasurable
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.div
          · apply Measurable.neg (Measurable.log (Measurable.mul measurable_fst measurable_snd))
          · apply Measurable.const_sub (Measurable.mul measurable_fst measurable_snd)
        · apply Measurable.pow measurable_fst measurable_const
      · apply Measurable.pow measurable_snd measurable_const

lemma J_rs_symm (r s : ℕ) : J r s = J s r := by
  rw [J_eq_toReal_J_ENN, J_eq_toReal_J_ENN, J_ENN_rs_symm]

theorem J_rs {r s : ℕ} (h : r ≠ s) : J r s =
    (∑ m ∈ Icc 1 r, 1 / (m : ℝ) ^ 2 - ∑ m ∈ Icc 1 s, 1 / (m : ℝ) ^ 2) / (r - s) := by
  by_cases h1 : r > s
  · simp only [J_rs' r s h1, sub_div, sum_div]
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [ Finset.Ico_add_one_right_eq_Icc]
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_div, zero_add]
        rw [ Finset.Ico_add_one_right_eq_Icc]
    · linarith
  · simp only [gt_iff_lt, not_lt] at h1
    have h2 : s > r := by
      by_contra!; apply h; linarith
    rw [J_rs_symm, J_rs' s r h2]
    nth_rw 2 [← neg_div_neg_eq]
    simp only [neg_sub]
    congr 1
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sub]
    · congr 1
      · rw [← Finset.sum_range_add_sum_Ico (n := s + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [ Finset.Ico_add_one_right_eq_Icc]
      · rw [← Finset.sum_range_add_sum_Ico (n := r + 1) (m := 1) _ (by omega)]
        simp only [range_one, one_div, sum_singleton, CharP.cast_eq_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, zero_add]
        rw [ Finset.Ico_add_one_right_eq_Icc]
    · linarith

end Zeta3_Integral

section Zeta3_LinearForm

/-! # Integer linear forms for the Apéry integrals -/

open scoped _root_.Nat
open _root_.BigOperators

lemma d_cube_ne_zero {r : ℕ} : ((d (Finset.Icc 1 r) ^ 3) : ℝ) ≠ (0 : ℝ) := by
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
  apply d_ne_zero; simp

lemma J_rr_linear (r : ℕ) :
    ∃ a : ℤ, J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - a / (d (Finset.Icc 1 r)) ^ 3 := by
  if h : r = 0 then
    rw [h, zeta_3]; use 0; simp
  else
    rw [J_rr]
    simp only [sub_right_inj]
    simp_rw [eq_div_iff d_cube_ne_zero, Finset.mul_sum, Finset.sum_mul]
    use ∑ i ∈ Finset.Icc 1 r, 2 * ↑(d (Finset.Icc 1 r)) ^ 3 / ↑i ^ 3
    simp only [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_assoc]
    nth_rewrite 2 [mul_comm]
    rw [mul_one_div, Int.cast_div]
    · simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, mul_div_assoc']
    · rw [← Nat.cast_pow, ← Nat.cast_pow, d_cube', Nat.cast_pow]
      apply Dvd.dvd.mul_left
      norm_cast
      apply dvd_d_of_mem
      simp_all
    · simp_all only [Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
      linarith

lemma Icc_diff_Icc {r s : ℕ} (_ : r > s) (_ : ¬s = 0) :
    Finset.Icc 1 r \ Finset.Icc 1 s = Finset.Icc (s + 1) r := by
  ext x
  constructor
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Icc, not_and, not_le, and_true]
    exact LT.lt.nat_succ_le (hx.2 hx.1.1)
  · intro hx
    simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_sdiff, and_true, not_and, not_le]
    constructor
    · linarith
    · intro
      linarith

lemma one_div_sum_eq {r s : ℕ} (h : r > s) :
    ∑ m ∈ Finset.Icc 1 r, (1 / m ^ 2 : ℝ) - ∑ m ∈ Finset.Icc 1 s, (1 / m ^ 2 : ℝ) =
    ∑ m ∈ Finset.Icc 1 (r - s), (1 / (s + m) ^ 2 : ℝ) := by
  rw [← Finset.sum_sdiff_eq_sub]
  · if h1 : s = 0 then
      simp_all
    else
      simp_rw [← Nat.cast_add]
      rw [Icc_diff_Icc h h1, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_add (f := fun (x : ℕ) => 1 / ((x ^ 2) : ℝ)) (c := s), add_comm,
        show r - s + 1 + s = r + 1 by omega]
  · exact Finset.Icc_subset_Icc_right (LT.lt.le (gt_iff_lt.1 h))

lemma J_rs_linear {r s : ℕ} (h : r > s) : ∃ a : ℤ, J r s = a / (d (Finset.Icc 1 r)) ^ 3 := by
  rw [J_rs (by linarith)]
  simp_rw [eq_div_iff d_cube_ne_zero, one_div_sum_eq h]
  use (∑ m ∈ Finset.Icc 1 (r - s), (d (Finset.Icc 1 r)) ^ 2 / (s + m) ^ 2 *
    (d (Finset.Icc 1 r)) / (r - s))
  rw [Finset.sum_div, Finset.sum_mul, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 3 = 1 + 2 by omega, pow_add, pow_one, mul_comm, mul_assoc, mul_div_assoc', mul_one_div,
    mul_div_assoc', mul_comm, ← mul_div_assoc', Int.cast_div]
  · rw [Int.cast_mul, Int.cast_div]
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_natCast, Int.cast_add,
      Int.cast_sub]
      rw [mul_div_assoc']
    · norm_cast
      rw [d_sq']
      apply dvd_d_of_mem
      simp_all only [gt_iff_lt, Finset.mem_Icc, Finset.mem_image, zero_le, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀, exists_eq_right]
      omega
    · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_pow, Int.cast_add, Int.cast_natCast,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      rw [← Nat.cast_add]
      norm_cast; omega
  · apply Dvd.dvd.mul_left
    rw [← Nat.cast_sub (by linarith)]
    norm_cast
    apply dvd_d_of_mem
    simp_all only [gt_iff_lt, Finset.mem_Icc, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le,
      and_true]
    linarith
  · simp_all only [gt_iff_lt, Finset.mem_Icc, Int.cast_sub, Int.cast_natCast]
    rw [← Nat.cast_sub (by linarith)]
    norm_cast; linarith

lemma multi_integral_sum_comm {n : ℕ} (c : ℕ → ℤ) : ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 * ↑(c x_2) * x.2 ^ x_2
    = ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
      ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 * ↑(c x_2) * x.2 ^ x_2 := by
    symm
    calc
    _ = ∑ x_1 ∈ Finset.range (n + 1), ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_2 ∈ Finset.range (n + 1),
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 * ↑(c x_2) * x.2 ^ x_2 := by
      congr! 1 with a _
      rw [← MeasureTheory.integral_finsetSum]
      intro i _
      have h : (fun (x : ℝ × ℝ) ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * ↑(c a) * x.1 ^ a *
        ↑(c i) * x.2 ^ i) = (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
          x.1 ^ a * x.2 ^ i * (↑(c i) * ↑(c a))) := by
        ext x; ring
      rw [h]
      apply MeasureTheory.Integrable.mul_const
      exact integrableOn_J_rs a i
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ∑ x_1 ∈ Finset.range (n + 1), ∑ x_2 ∈ Finset.range (n + 1),
    -(x.1 * x.2).log / (1 - x.1 * x.2) * ↑(c x_1) * x.1 ^ x_1 * ↑(c x_2) * x.2 ^ x_2 := by
      rw [← MeasureTheory.integral_finsetSum]
      intro i _
      apply MeasureTheory.integrable_finsetSum
      intro j _
      have h : (fun (x : ℝ × ℝ) ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) * ↑(c i) * x.1 ^ i *
        ↑(c j) * x.2 ^ j) = (fun x ↦ -Real.log (x.1 * x.2) / (1 - x.1 * x.2) *
          x.1 ^ i * x.2 ^ j * (↑(c i) * ↑(c j))) := by
        ext x; ring
      rw [h]
      apply MeasureTheory.Integrable.mul_const
      exact integrableOn_J_rs i j

lemma multi_integral_mul_const (c d : ℕ) (p q : ℝ) :
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
     -(x.1 * x.2).log / (1 - x.1 * x.2) * p * x.1 ^ c * q * x.2 ^ d = p * q * J c d := by
  simp only [J]
  symm
  rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
  apply MeasureTheory.setIntegral_congr_fun (by measurability)
  intro x _
  simp only [smul_eq_mul]
  ring

/-- Integer correction coefficient selected from the proved integral identities. -/
noncomputable def p (r s : ℕ) : ℤ :=
  if h : r > s then (J_rs_linear h).choose
  else if h : r < s then (J_rs_linear h).choose
  else -(J_rr_linear r).choose

/-- The zeta coefficient: two on the diagonal and zero off the diagonal. -/
noncomputable def q (r s : ℕ) : ℤ :=
  if r > s then 0
  else if r < s then 0
  else 2

lemma J_symm (r s : ℕ) : J r s = J s r := by
  if h : r = s then rw [h]
  else
    rw [J_rs (by tauto), J_rs (by tauto), ← neg_div_neg_eq]; ring

lemma linear_int_aux : ∃ a b : ℕ → ℕ → ℤ, ∀ r s : ℕ, J r s =
    b r s * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 + a r s / (d (Finset.Icc 1 (Nat.max r s))) ^ 3 := by
  use p
  use q
  intro x y
  if h : x > y then
    obtain ⟨a, ha⟩ := J_rs_linear h
    simp only [p, q]
    simp_all only [gt_iff_lt, one_div, ite_true, Int.cast_zero, zero_mul, dite_true,
      zero_add]
    rw [(J_rs_linear h).choose_spec] at ha
    rw [show x.max y = x by exact max_eq_left_iff.2 (LT.lt.le h)]
    simp_all
  else if h1 : x < y then
    obtain ⟨a, ha⟩ := J_rs_linear h1
    simp only [p, q]
    obtain h2 := J_symm x y
    simp_all only [gt_iff_lt, one_div, ite_true, ite_self, Int.cast_zero,
      zero_mul, dite_true, zero_add, dite_false]
    rw [(J_rs_linear h1).choose_spec] at ha
    simp only [not_lt] at h
    simp_all
  else
    have h : x = y := by linarith
    obtain ⟨a, ha⟩ := J_rr_linear y
    simp only [p, q]
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, ite_false,
      Int.cast_ofNat, not_isEmpty_of_nonempty, tsum_empty, mul_zero, zero_sub, sub_right_inj,
      dite_false, Int.cast_neg, max_self]
    rw [(J_rr_linear y).choose_spec, ← Mathlib.Tactic.RingNF.add_neg, ← neg_div] at ha
    simp_all

end Zeta3_LinearForm

/-
The following Chebyshev upper bound (section Zeta3_Chebyshev) replaces the prime number theorem
used by the original proof. It is taken, pruned, from openai/math
(https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/EgyptianFractions,
files ChebyshevImprovedLower.lean, ChebyshevLowerSharp.lean, DilationRecurrenceUpper.lean,
ChebyshevUpperSharp.lean), Apache-2.0 (lean/LICENSE in that repository).
-/
section Zeta3_Chebyshev
open Filter
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Problem337

/-- Chebyshev's thirty-periodic floor combination takes only the values zero
and one. This is the finite arithmetic behind the improved lower constant. -/
theorem chebyshev_thirty_weight_bounds (n : ℕ) :
    0 ≤ (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ) ∧
    (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ) ≤ 1 := by
  omega

/-- The factorial logarithm is a finite Mangoldt sum with floor weights;
the outer range may be any larger initial interval. -/
theorem log_factorial_eq_sum_mangoldt_div {m N : ℕ} (hm : m ≤ N) :
    Real.log (m.factorial : ℝ) =
      ∑ d ∈ Finset.range (N + 1), Λ d * ((m / d : ℕ) : ℝ) := by
  classical
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod,
    Real.log_prod (by intro i hi; positivity)]
  calc
    (∑ i ∈ Finset.range m, Real.log ((i + 1 : ℕ) : ℝ)) =
        ∑ i ∈ Finset.range m, ∑ d ∈ Finset.range (N + 1),
          if d ∣ i + 1 then Λ d else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiN : i + 1 ≤ N := (Finset.mem_range.mp hi |> Nat.succ_le_of_lt).trans hm
      have he : (Finset.range (N + 1)).filter (fun d => d ∣ i + 1) =
          (i + 1).divisors := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
        constructor
        · intro h
          exact ⟨h.2, by omega⟩
        · intro h
          exact ⟨by have := Nat.le_of_dvd (by omega : 0 < i + 1) h.1; omega, h.1⟩
      rw [← Finset.sum_filter, he, ArithmeticFunction.vonMangoldt_sum]
    _ = ∑ d ∈ Finset.range (N + 1), ∑ i ∈ Finset.range m,
          if d ∣ i + 1 then Λ d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter, Finset.sum_const, Nat.card_multiples]
      simp [mul_comm]

/-- Extending a Mangoldt prefix to a larger range by an indicator. -/
theorem chebyshev_psi_nat_sum_indicator {m N : ℕ} (hm : m ≤ N) :
    Chebyshev.psi m = ∑ d ∈ Finset.range (N + 1), if d ≤ m then Λ d else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range (N + 1)).filter (fun d => d ≤ m) = Finset.range (m + 1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  simp [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

/-- The complementary upper recurrence from the same thirty-periodic
kernel. Iteration gives the classical upper Chebyshev constant `6C/5`. -/
theorem chebyshev_psi_le_factorial_combination_add (N : ℕ) :
    Chebyshev.psi N ≤
      Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
        Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
        Real.log ((N / 30).factorial : ℝ) + Chebyshev.psi (N / 6 : ℕ) := by
  rw [log_factorial_eq_sum_mangoldt_div (le_refl N),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 2),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 3),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 5),
    log_factorial_eq_sum_mangoldt_div (Nat.div_le_self N 30),
    chebyshev_psi_nat_sum_indicator (Nat.div_le_self N 6)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hpsi : Chebyshev.psi N = ∑ d ∈ Finset.range (N + 1), Λ d := by
    simp [Chebyshev.psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
  rw [hpsi]
  apply Finset.sum_le_sum
  intro d hd
  have hdiv (k : ℕ) : N / k / d = N / d / k := by
    simp [Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hdiv]
  by_cases hsmall : d ≤ N / 6
  · rw [if_pos hsmall]
    have hw := (chebyshev_thirty_weight_bounds (N / d)).1
    have hn : N / d / 2 + N / d / 3 + N / d / 5 ≤ N / d + N / d / 30 := by
      omega
    have hnR : ((N / d / 2 : ℕ) : ℝ) + (N / d / 3 : ℕ) + (N / d / 5 : ℕ) ≤
        (N / d : ℕ) + (N / d / 30 : ℕ) := by exact_mod_cast hn
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := d)]
  · rw [if_neg hsmall]
    have hdpos : 0 < d := by omega
    have hdN : d ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hqpos : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).2 hdN
    have hqsmall : N / d < 6 := by
      apply (Nat.div_lt_iff_lt_mul hdpos).2
      have hNd : N / 6 < d := Nat.lt_of_not_ge hsmall
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).1 hNd
      simpa only [Nat.mul_comm] using this
    have hq : N / d = 1 ∨ N / d = 2 ∨ N / d = 3 ∨ N / d = 4 ∨ N / d = 5 := by
      omega
    rcases hq with hq | hq | hq | hq | hq <;> norm_num [hq] <;> linarith

end Problem337

namespace Problem337.ChebyshevLowerSharp
open Finset Asymptotics
open ArithmeticFunction

lemma log_factorial_eq_sum_log (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih,
      ← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le n)]
    simp [Finset.sum_insert]

/-- The linear-scale error in the logarithmic factorial estimate vanishes. -/
lemma log_factorial_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log n + n) / n)
      atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
    (by positivity : Real.sqrt Real.pi ≠ 0)).div_atTop hnat
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hc := hnat.const_div_atTop (Real.log 2)
  have hlim := hs.add ((hc.add hl).div_const 2)
  simp only [zero_add, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hf := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR,
    Real.log_div hnR (Real.exp_ne_zero 1), Real.log_exp] at hf
  dsimp only [Function.comp_def, id_eq]
  rw [hf]
  ring

/-- A scaled version with the common divergent logarithm subtracted. -/
lemma scaled_log_factorial_tendsto (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      Real.log ((a * n).factorial : ℝ) / n - (a : ℝ) * Real.log n)
      atTop (nhds ((a : ℝ) * Real.log a - a)) := by
  have hmul : Tendsto (fun n : ℕ => a * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n ha) tendsto_id
  have hlim := ((log_factorial_error_tendsto_zero.comp hmul).mul_const (a : ℝ)).add_const
    ((a : ℝ) * Real.log a - a)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp_def, Nat.cast_mul]
  rw [Real.log_mul haR hnR]
  field_simp
  ring

/-- Chebyshev's classical elementary lower constant, approximately `0.92129`. -/
noncomputable def lowerConstant : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

lemma lowerConstant_eq :
    lowerConstant = (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30 := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [lowerConstant, h30]
  ring

lemma lowerConstant_gt_921_div_1000 : (921 / 1000 : ℝ) < lowerConstant := by
  have h5 := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 1
  norm_num at h5
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0), h4] at h5
  rw [lowerConstant_eq]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

noncomputable def factorialBlock (n : ℕ) : ℝ :=
  Real.log ((30 * n).factorial : ℝ) - Real.log ((15 * n).factorial : ℝ) -
    Real.log ((10 * n).factorial : ℝ) - Real.log ((6 * n).factorial : ℝ) +
    Real.log (n.factorial : ℝ)

lemma factorialBlock_tendsto :
    Tendsto (fun n : ℕ => factorialBlock n / (30 * n)) atTop (nhds lowerConstant) := by
  have hlim := (((((scaled_log_factorial_tendsto 30 (by norm_num)).sub
    (scaled_log_factorial_tendsto 15 (by norm_num))).sub
    (scaled_log_factorial_tendsto 10 (by norm_num))).sub
    (scaled_log_factorial_tendsto 6 (by norm_num))).add
    (scaled_log_factorial_tendsto 1 (by norm_num))).div_const 30
  have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  convert hlim using 1
  · funext n
    simp only [factorialBlock, Nat.cast_ofNat, Nat.cast_one, Nat.one_mul]
    ring
  · rw [lowerConstant_eq]
    norm_num only [Nat.cast_ofNat, Nat.cast_one, Real.log_one, mul_zero,
      h15, h10, h6, h30]
    congr 1
    ring

/-- Rescaling the `30`-blocks loses only a bounded endpoint discrepancy. -/
lemma factorialBlock_div_tendsto :
    Tendsto (fun N : ℕ => factorialBlock (N / 30) / N)
      atTop (nhds lowerConstant) := by
  have hquot : Tendsto (fun N : ℕ => N / 30) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (30 * b)] with N hN
    omega
  have hratio : Tendsto (fun N : ℕ => (30 : ℝ) * (N / 30 : ℕ) / N)
      atTop (nhds 1) := by
    have h := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).sub
      (tendsto_mod_div_atTop_nhds_zero_nat (m := 30) (by norm_num))
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have heq : ((N % 30 : ℕ) : ℝ) + 30 * ((N / 30 : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N 30
    field_simp
    linarith
  have hlim := (factorialBlock_tendsto.comp hquot).mul hratio
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (30 : ℕ)] with N hN
  have hqR : ((N / 30 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < N / 30 := by omega
    exact_mod_cast this.ne'
  dsimp only [Function.comp_def]
  field_simp

/-- The unblocked finite factorial expression. -/
noncomputable def factorialCombination (N : ℕ) : ℝ :=
  Real.log (N.factorial : ℝ) - Real.log ((N / 2).factorial : ℝ) -
    Real.log ((N / 3).factorial : ℝ) - Real.log ((N / 5).factorial : ℝ) +
    Real.log ((N / 30).factorial : ℝ)

lemma log_factorial_gap {n N M : ℕ} (hnN : n ≤ N) (hNM : N ≤ M)
    (hM : 1 ≤ M) (hgap : N - n ≤ 30) :
    0 ≤ Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) ∧
      Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) ≤ 30 * Real.log M := by
  have hsum := Finset.sum_Ioc_consecutive (fun k : ℕ => Real.log (k : ℝ))
    (Nat.zero_le n) hnN
  have heq : Real.log (N.factorial : ℝ) - Real.log (n.factorial : ℝ) =
      ∑ k ∈ Ioc n N, Real.log (k : ℝ) := by
    rw [log_factorial_eq_sum_log, log_factorial_eq_sum_log]
    linarith
  rw [heq]
  constructor
  · apply Finset.sum_nonneg
    intro k hk
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ k by have := (Finset.mem_Ioc.mp hk).1; omega)
  · calc
      _ ≤ ∑ _k ∈ Ioc n N, Real.log (M : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Real.log_le_log
        · exact_mod_cast (show 0 < k by have := (Finset.mem_Ioc.mp hk).1; omega)
        · exact_mod_cast ((Finset.mem_Ioc.mp hk).2.trans hNM)
      _ = (N - n : ℕ) * Real.log M := by simp
      _ ≤ 30 * Real.log M := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hgap
        · exact Real.log_nonneg (by exact_mod_cast hM)

/-- Passing from a multiple of thirty to an arbitrary endpoint costs only
a logarithmic error. -/
lemma factorialCombination_sub_block_abs_le {N : ℕ} (hN : 1 ≤ N) :
    |factorialCombination N - factorialBlock (N / 30)| ≤ 120 * Real.log N := by
  have h0 := log_factorial_gap (n := 30 * (N / 30)) (N := N) (M := N)
    (by omega) le_rfl hN (by omega)
  have h2 := log_factorial_gap (n := 15 * (N / 30)) (N := N / 2) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have h3 := log_factorial_gap (n := 10 * (N / 30)) (N := N / 3) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have h5 := log_factorial_gap (n := 6 * (N / 30)) (N := N / 5) (M := N)
    (by omega) (Nat.div_le_self _ _) hN (by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  dsimp only [factorialCombination, factorialBlock]
  constructor <;> linarith [h0.1, h0.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2]

/-- The full, unblocked factorial combination has the same sharp coefficient. -/
theorem factorialCombination_div_tendsto :
    Tendsto (fun N : ℕ => factorialCombination N / N)
      atTop (nhds lowerConstant) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim : Tendsto (fun N : ℕ => 120 * (Real.log N / N)) atTop (nhds 0) := by
    simpa using hlog.const_mul 120
  have herror : Tendsto (fun N : ℕ =>
      (factorialCombination N - factorialBlock (N / 30)) / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun N => ?_) hlim
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hnormN : ‖(N : ℝ)‖ = (N : ℝ) :=
        Real.norm_of_nonneg (Nat.cast_nonneg N)
      rw [norm_div, hnormN, Real.norm_eq_abs]
      calc
        _ ≤ (120 * Real.log (N : ℝ)) / N :=
          div_le_div_of_nonneg_right (factorialCombination_sub_block_abs_le hN)
            (Nat.cast_nonneg N)
        _ = 120 * (Real.log (N : ℝ) / N) := by ring
  convert herror.add factorialBlock_div_tendsto using 1
  · funext N
    ring
  · simp

end Problem337.ChebyshevLowerSharp

namespace Problem337.DilationRecurrence

/-- An eventual dilation recurrence has a global affine barrier whenever its
linear drift fits the proposed slope. The finitely many initial values are
absorbed in one constant, without a positivity assumption on the sequence. -/
theorem exists_affine_upper_bound
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) (hb : 0 ≤ b)
    (hmargin : a + b / (d : ℝ) ≤ b)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, f n ≤ b * (n : ℝ) + B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrec.and hstep)
  let B : ℝ := ∑ k ∈ Finset.range (N + 1), |f k|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => abs_nonneg (f k))
  refine ⟨B, hB, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · have hf : f n ≤ B := (le_abs_self (f n)).trans
        (Finset.single_le_sum (fun k _ => abs_nonneg (f k))
          (Finset.mem_range.mpr (by omega : n < N + 1)))
      exact hf.trans (le_add_of_nonneg_left (mul_nonneg hb (Nat.cast_nonneg n)))
    · have hn0 : 0 < n := by omega
      have hsmall : n / d < n := Nat.div_lt_self hn0 (by omega)
      have hprev := ih (n / d) hsmall
      have hpair := hN n (by omega)
      have hquot : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hscaled := mul_le_mul_of_nonneg_left hquot hb
      have hdrift := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg n)
      calc
        f n ≤ g n + f (n / d) := hpair.1
        _ ≤ a * (n : ℝ) + (b * ((n / d : ℕ) : ℝ) + B) :=
          add_le_add hpair.2 hprev
        _ ≤ a * (n : ℝ) + (b * ((n : ℝ) / d) + B) := by linarith
        _ = (a + b / (d : ℝ)) * (n : ℝ) + B := by ring
        _ ≤ b * (n : ℝ) + B := by linarith

/-- Any strict enlargement of an affine barrier is eventually a linear bound. -/
theorem eventually_linear_of_affine
    (f : ℕ → ℝ) (b B c : ℝ) (hbc : b < c)
    (hbound : ∀ n : ℕ, f n ≤ b * (n : ℝ) + B) :
    ∀ᶠ n : ℕ in atTop, f n ≤ c * (n : ℝ) := by
  have hgrowth : ∀ᶠ n : ℕ in atTop, B / (c - b) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (B / (c - b)))
  filter_upwards [hgrowth] with n hn
  have hB : B ≤ (n : ℝ) * (c - b) := (div_le_iff₀ (sub_pos.mpr hbc)).mp hn
  have hf := hbound n
  nlinarith

/-- A fixed strict slack in the slope removes the initial-value constant. -/
theorem eventually_upper_bound
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (a b c : ℝ) (hb : 0 ≤ b)
    (hmargin : a + b / (d : ℝ) ≤ b) (hbc : b < c)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, f n ≤ c * (n : ℝ) := by
  obtain ⟨B, _, hB⟩ := exists_affine_upper_bound f g d hd a b hb hmargin hrec hstep
  exact eventually_linear_of_affine f b B c hbc hB

/-- The asymptotic slope of the forcing term gives the geometric-series slope
for the recursively bounded sequence. This needs a limit only for `g`, not
for `f`, and handles the natural-number rounding in `n / d` exactly. -/
theorem eventually_upper_of_ratio_limit
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hlim : Tendsto (fun n : ℕ => g n / (n : ℝ)) atTop (nhds c))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ (c / (1 - 1 / (d : ℝ)) + ε) * (n : ℝ) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := by linarith
  let ρ : ℝ := 1 - 1 / (d : ℝ)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact sub_pos.mpr ((div_lt_one hd0).mpr hdR)
  let b : ℝ := c / ρ + ε / 2
  let a : ℝ := b * ρ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hca : c < a := by
    dsimp [a, b]
    rw [add_mul, div_mul_cancel₀ c hρ.ne']
    linarith [mul_pos (show 0 < ε / 2 by positivity) hρ]
  have hmargin : a + b / (d : ℝ) ≤ b := by
    dsimp [a, ρ]
    exact le_of_eq (by ring)
  have hbc : b < c / (1 - 1 / (d : ℝ)) + ε := by
    dsimp [b, ρ]
    linarith
  have hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ) := by
    filter_upwards [hlim.eventually (gt_mem_nhds hca), eventually_ge_atTop (1 : ℕ)]
      with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    exact ((div_lt_iff₀ hn0).mp hn).le
  exact eventually_upper_bound f g d hd a b
    (c / (1 - 1 / (d : ℝ)) + ε) hb hmargin hbc hrec hstep

end Problem337.DilationRecurrence

namespace Problem337.ChebyshevUpperSharp

/-- The classical upper Chebyshev constant, approximately `1.10555`. -/
noncomputable def upperConstant : ℝ := 6 * ChebyshevLowerSharp.lowerConstant / 5

lemma upperConstant_pos : 0 < upperConstant := by
  have h := ChebyshevLowerSharp.lowerConstant_gt_921_div_1000
  dsimp [upperConstant]
  linarith

lemma upperConstant_lt_1106_div_1000 : upperConstant < (1106 / 1000 : ℝ) := by
  rw [upperConstant, ChebyshevLowerSharp.lowerConstant_eq]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

/-- The exact finite dilation recurrence and the factorial ratio limit give
the classical sharp elementary upper coefficient for `psi`. -/
theorem eventually_psi_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Chebyshev.psi N ≤ (upperConstant + ε) * (N : ℝ) := by
  have hc : 0 ≤ ChebyshevLowerSharp.lowerConstant := by
    linarith [ChebyshevLowerSharp.lowerConstant_gt_921_div_1000]
  have hrec : ∀ᶠ N : ℕ in atTop, Chebyshev.psi N ≤
      ChebyshevLowerSharp.factorialCombination N + Chebyshev.psi (N / 6 : ℕ) :=
    Eventually.of_forall chebyshev_psi_le_factorial_combination_add
  have h := DilationRecurrence.eventually_upper_of_ratio_limit
    (fun N => Chebyshev.psi N) ChebyshevLowerSharp.factorialCombination
    6 (by norm_num) ChebyshevLowerSharp.lowerConstant hc hrec
    ChebyshevLowerSharp.factorialCombination_div_tendsto ε hε
  have heq : ChebyshevLowerSharp.lowerConstant / (1 - 1 / (6 : ℝ)) =
      upperConstant := by dsimp [upperConstant]; ring
  simpa only [Nat.cast_ofNat, heq] using h

theorem eventually_theta_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Chebyshev.theta N ≤ (upperConstant + ε) * (N : ℝ) := by
  filter_upwards [eventually_psi_upper ε hε] with N hN
  exact (Chebyshev.theta_le_psi N).trans hN

/-- The classical partial-summation remainder is already lower order. Hence
an improved eventual coefficient for `theta` transfers without a fixed loss
to the actual prime counting function. -/
theorem eventually_primeCounting_upper_of_theta (c ε : ℝ) (hε : 0 < ε)
    (hθ : ∀ᶠ N : ℕ in atTop, Chebyshev.theta N ≤ c * (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤ (c + ε) * (N : ℝ) / Real.log (N : ℝ) := by
  have herr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.integral_theta_div_log_sq_isLittleO.bound hε)
  filter_upwards [hθ, herr, eventually_ge_atTop (2 : ℕ)] with N hN he hN2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hid := Chebyshev.primeCounting_eq_theta_div_log_add_integral
    (show (2 : ℝ) ≤ N by exact_mod_cast hN2)
  simp only [Nat.floor_natCast] at hid
  rw [Real.norm_of_nonneg (div_nonneg hN0 hlog.le)] at he
  have hi := (Real.le_norm_self
    (∫ t in (2 : ℝ)..(N : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2))).trans he
  calc
    (Nat.primeCounting N : ℝ) = Chebyshev.theta N / Real.log (N : ℝ) +
        ∫ t in (2 : ℝ)..(N : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2) := hid
    _ ≤ (c * (N : ℝ)) / Real.log (N : ℝ) +
        ε * ((N : ℝ) / Real.log (N : ℝ)) :=
      add_le_add (div_le_div_of_nonneg_right hN hlog.le) hi
    _ = _ := by ring

/-- The classical upper Chebyshev coefficient transfers to actual primes. -/
theorem eventually_primeCounting_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) ≤
        (upperConstant + ε) * (N : ℝ) / Real.log (N : ℝ) := by
  have hhalf : 0 < ε / 2 := by positivity
  have h := eventually_primeCounting_upper_of_theta (upperConstant + ε / 2)
    (ε / 2) hhalf (eventually_theta_upper (ε / 2) hhalf)
  have heq : upperConstant + ε / 2 + ε / 2 = upperConstant + ε := by ring
  simpa only [heq] using h

end Problem337.ChebyshevUpperSharp

end Zeta3_Chebyshev

section Zeta3_Basic

/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/

/-! # Apéry's irrationality proof for ζ(3)

Port of the Apache-2.0 source by Junqi Liu and Jujian Zhang.
-/

open scoped _root_.Nat
open _root_.BigOperators _root_.Polynomial OMAPort_Zeta3.Polynomial

/-- The logarithmic double integral weighted by two real shifted Legendre polynomials. -/
noncomputable abbrev JJ (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (-(x.1 * x.2).log / (1 - x.1 * x.2) * (aperyShiftedLegendre n).eval x.1 *
      (aperyShiftedLegendre n).eval x.2)

/-- The equivalent positive triple integral in the Apéry identity. -/
noncomputable abbrev JJ' (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)

/-- The nonnegative extended-real integral of the positive Apéry integrand. -/
noncomputable abbrev JJENN (n : ℕ) : ENNReal :=
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ENNReal.ofReal
    ((x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1))

/-- The Apéry double integral multiplied by the cube of the least common multiple. -/
noncomputable abbrev fun1 (n : ℕ) : ℝ := (d (Finset.Icc 1 n)) ^ 3 * JJ n

theorem linear_int (n : ℕ) : ∃ a b : ℕ → ℤ,
    fun1 n = a n + b n * (d (Finset.Icc 1 n) : ℤ) ^ 3  * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta fun1 JJ
  obtain ⟨c, hc⟩ := shiftedLegendre_eq_int_poly n
  simp_rw [hc, Polynomial.eval_finsetSum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  simp only [eval_mul, eval_intCast, eval_pow, eval_X]
  simp_rw [← mul_assoc, multi_integral_sum_comm, multi_integral_mul_const]
  simp only [Finset.mul_sum]
  obtain ⟨qq', ⟨pp', hqq'⟩⟩ := linear_int_aux
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    d (Finset.Icc 1 n) ^ 3 * c x * c i * qq' x i / d (Finset.Icc 1 (Nat.max x i)) ^ 3
  use fun n => ∑ x ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), c x * c i * pp' x i
  rw [← Nat.cast_pow, ← Int.cast_pow , ← Int.cast_mul, Finset.sum_mul]
  simp only [Nat.cast_pow, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  specialize hqq' x y
  rw [hqq', mul_add, mul_add, add_comm]
  congr 1
  · rw [Int.cast_div]
    · rw [mul_div_assoc', ← mul_div_assoc, div_eq_div_iff]
      · norm_cast
        rw [← mul_assoc, ← mul_assoc]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Nat.cast_eq_zero]
        apply d_ne_zero
        simp
      · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Nat.cast_eq_zero]
        apply d_ne_zero
        simp
    · rw [mul_assoc, mul_assoc]
      apply Dvd.dvd.mul_right
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsIntegrallyClosed.pow_dvd_pow_iff]
      norm_cast
      apply d_dvd_d_of_le
      simp_all only [Finset.mem_range]
      intro a b
      simp_all only [Finset.mem_Icc, true_and]
      simp only [le_max_iff] at b
      rcases b with ⟨_ ,(c | c)⟩
      <;>
      linarith
    · simp only [Int.cast_pow, Int.cast_natCast, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, Nat.cast_eq_zero]
      apply d_ne_zero
      simp
  · ring

lemma pos_aux (x : ℝ × ℝ × ℝ) (hx : (0 < x.1 ∧ x.1 < 1) ∧ (0 < x.2.1 ∧ x.2.1 < 1) ∧ 0 < x.2.2 ∧
  x.2.2 < 1) :
    0 < (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [sub_pos]
  suffices (1 - x.2.1 * x.2.2) * x.1 < x.1 by linarith
  rw [mul_lt_iff_lt_one_left]
  · simp only [sub_lt_self_iff]
    nlinarith
  · nlinarith

lemma JJENN_upper (n : ℕ) : JJENN n ≤
    ENNReal.ofReal (2 * (1 / 32) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
  calc
  _ ≤ ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal ((1 / 32) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [JJENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    apply MeasureTheory.lintegral_mono
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte]
      simp only [Set.mem_prod, Set.mem_Ioo] at h
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff_of_pos_right]
      · apply pow_le_pow_left₀
        · apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · linarith [pos_aux x h]
        · suffices x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
            (1 - (1 - x.2.1 * x.2.2) * x.1) < (1 / 32 : ℝ)by linarith
          apply bound_sharp <;> linarith
      · exact pos_aux x h
    · simp only [h, ↓reduceIte, le_refl]
  _ = ENNReal.ofReal ((1 / 32) ^ n) * ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ
    Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        rw [← ENNReal.ofReal_mul, ← mul_one_div]
        apply pow_nonneg (by norm_num)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.mul _ measurable_fst
      apply Measurable.const_sub
      apply Measurable.mul
      · exact measurable_fst.comp measurable_snd
      · exact measurable_snd.comp measurable_snd
  _ = ENNReal.ofReal (2 * (1 / 32) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr]
    simp only [one_div, inv_pow, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
      sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    nth_rw 2 [mul_comm]

lemma integrableOn_JJ' (n : ℕ) : MeasureTheory.Integrable (fun (x : ℝ × ℝ × ℝ) ↦
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) / (1 - (1 - x.2.1 * x.2.2) *
      x.1)) ^ n /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      ×ˢ Set.Ioo 0 1)) := by
  rw [MeasureTheory.Integrable]
  constructor
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    change k < ⊤
    have : k = JJENN n := by
      simp only [k, JJENN]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · rw [abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2,
              abs_eq_self.2] <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
        · positivity
        · apply div_nonneg
          · apply pow_nonneg
            apply div_nonneg
            · apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg _ (by linarith)
              apply mul_nonneg (by linarith) (by linarith)
            · linarith [pos_aux x hx]
          · linarith [pos_aux x hx]
      · simp only [hx, ↓reduceIte]
    rw [this]
    apply LE.le.trans_lt (JJENN_upper n)
    simp only [one_div, inv_pow, ENNReal.ofReal_lt_top]

lemma shiftedLegendre_bound (n : ℕ) (x : ℝ) (hx : 0 < x ∧ x < 1) :
  |eval x (aperyShiftedLegendre n)| ≤ ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n +
    x_1).choose n) := by
  simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one, eval_finsetSum,
    eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
  have := Finset.abs_sum_le_sum_abs (f := fun y => (-1) ^ y * ↑(n.choose y) * ↑((n + y).choose
    n) * x ^ y)
    (s := Finset.range (n + 1))
  refine this.trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast, one_mul]
  trans ↑(n.choose i) * ↑((n + i).choose n) * 1
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_one₀
    · simp
    · rw [abs_eq_self.2 (by linarith)]
      linarith
  · simp

lemma Measurable_one_div_aux :
    Measurable fun (x : ℝ × ℝ × ℝ) ↦ ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
  fun_prop

lemma integrableOn_JJ1 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦ eval x.1 (aperyShiftedLegendre n) * eval x.2
    (aperyShiftedLegendre n) * (1 / (1 - (1 - x.1 * x.2) * z)))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo 0
    1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ
      Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, pow_two]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · apply shiftedLegendre_bound _ _ hx.2.1
                · apply shiftedLegendre_bound _ _ hx.2.2
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · simp
    · positivity

lemma integrableOn_JJ2 (n : ℕ) : MeasureTheory.Integrable (Function.uncurry fun z x ↦
  eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
    x.2) * z) ^ (n + 1))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo 0
    1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (|C|) * ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ
      Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, pow_add, ← div_div, abs_div,mul_one_div,
            div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [← mul_div, mul_assoc, abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · suffices |C| = C by
                    rw [this]
                    apply shiftedLegendre_bound _ _ hx.2.1
                  rw [abs_eq_self]
                  positivity
                · rcases x with ⟨x, ⟨y, z⟩⟩
                  simp only at hx ⊢
                  rcases hx with ⟨⟨hx0, hx1⟩, ⟨hy0, _⟩, ⟨hz0, hz1⟩⟩
                  rw [← div_pow, ← mul_pow, abs_pow]
                  suffices ineq1 : |y * z * x * ((1 - z) / (1 - (1 - y * z) * x))| ≤ 1 from
                    pow_le_one₀ (abs_nonneg _) ineq1
                  rw [show (1 - (1 - y * z) * x) = 1 - x + y * z * x by ring]
                  by_cases ineq : 1 - x + y * z * x = 0
                  · rw [ineq]
                    simp only [div_zero, mul_zero, abs_zero, zero_le_one]
                  · rw [
                    show y * z * x * ((1 - z) / (1 - x + y * z * x)) = (1-z)/((1-x)/(y*z*x) + 1) by
                      rw [mul_div, div_eq_div_iff]
                      · rw [mul_comm _ (1 - z), mul_assoc _ (y * z * x), mul_add, mul_div_cancel₀]
                        · ring
                        · apply mul_ne_zero
                          · apply mul_ne_zero
                            · linarith
                            · linarith
                          · linarith
                      · exact ineq
                      · rw [div_add_one (by positivity)]
                        intro r
                        rw [_root_.div_eq_zero_iff] at r
                        exact ineq (r.resolve_right (by positivity)), abs_div]
                    trans |1 - z|
                    · apply div_le_self (abs_nonneg _)
                      rw [abs_of_nonneg, le_add_iff_nonneg_left]
                      · apply div_nonneg
                        · linarith
                        · apply mul_nonneg
                          · apply mul_nonneg <;> linarith
                          · linarith
                      · apply add_nonneg
                        · apply div_nonneg
                          · linarith
                          · apply mul_nonneg
                            · apply mul_nonneg <;> linarith
                            · linarith
                        · linarith
                    rw [abs_le]
                    exact ⟨by linarith, by linarith⟩
              · simp only [pow_one]
                exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · finiteness
    · positivity

lemma integrableOn_JJ3 (n : ℕ) : MeasureTheory.Integrable
  (Function.uncurry fun z x ↦ eval x.1 (aperyShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
    (1 - (1 - x.1 * x.2) * z))
  ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo 0
    1 ×ˢ Set.Ioo 0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Integrable]
  constructor
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    set C := ∑ x_1 ∈ Finset.range (n + 1), (n.choose x_1 : ℝ) * ((n + x_1).choose n)
    change k < ⊤
    have : k ≤ ENNReal.ofReal (|C|) * ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ
      Set.Ioo 0 1,
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
      simp only [k]
      rw [← MeasureTheory.lintegral_const_mul _ Measurable_one_div_aux]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      apply MeasureTheory.lintegral_mono
      intro x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, Real.norm_eq_abs]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [← ENNReal.ofReal_mul]
        · rw [ENNReal.ofReal_le_ofReal_iff]
          · rw [Function.uncurry_apply_pair, mul_one_div, abs_div, div_le_div_iff₀]
            · apply mul_le_mul _ _ (by linarith [pos_aux x hx]) (by positivity)
              · rw [abs_mul, ← mul_one (a := |C|)]
                apply mul_le_mul _ _ (by positivity) (by positivity)
                · rw [abs_mul, ← mul_one (a := |C|)]
                  apply mul_le_mul _ _ (by positivity) (by positivity)
                  · suffices |C| = C by
                      rw [this]
                      apply shiftedLegendre_bound _ _ hx.2.1
                    rw [abs_eq_self]
                    positivity
                  · simp only [abs_pow]
                    apply pow_le_one₀
                    · simp only [abs_nonneg]
                    · rw [abs_eq_self.2 (by linarith)]
                      linarith
                · simp only [abs_pow]
                  apply pow_le_one₀
                  · simp only [abs_nonneg]
                  · rw [abs_eq_self.2 (by linarith)]
                    linarith
              · exact le_abs_self (1 - (1 - x.2.1 * x.2.2) * x.1)
            · simp only [abs_pos]; linarith [pos_aux x hx]
            · exact pos_aux x hx
          · rw [mul_one_div]
            apply div_nonneg (by positivity)
            linarith [pos_aux x hx]
        · positivity
      · simp [hx]
    apply LE.le.trans_lt this
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr, ← ENNReal.ofReal_mul]
    · finiteness
    · positivity

lemma eq1_integrableOn_aux1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) : MeasureTheory.Integrable
    (fun x ↦ eval x.1 (aperyShiftedLegendre n) * eval x.2 (aperyShiftedLegendre n) * (1 / (1 -
      (1 - x.1 * x.2) * z)))
    ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo
      0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one,isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_snd
      · apply ContinuousOn.div continuousOn_const
        · apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul _ continuousOn_const
          apply ContinuousOn.sub continuousOn_const
          apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · intro x hx
          suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
          simp only [Set.mem_prod, Set.mem_Icc] at hx
          simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
          suffices (1 - x.1 * x.2) * z ≤ z by linarith
          apply mul_le_of_le_one_left (by linarith)
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
          nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma eq1_integrableOn_aux2 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) : MeasureTheory.Integrable
    (fun x ↦ eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1
      - x.1 * x.2) * z) ^ (n + 1))
    ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo
      0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one,isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
            apply continuousOn_finsetSum
            intro i _
            apply ContinuousOn.mul continuousOn_const
            apply ContinuousOn.pow continuousOn_fst
          · apply ContinuousOn.pow
            apply ContinuousOn.mul _ continuousOn_const
            apply ContinuousOn.mul continuousOn_fst continuousOn_snd
        · apply ContinuousOn.pow
          apply ContinuousOn.sub continuousOn_const continuousOn_snd
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by positivity
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq1 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) : ∫ (x : ℝ × ℝ) in Set.Ioo 0 1
  ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * eval x.2 (aperyShiftedLegendre n) * (1 / (1 - (1 - x.1
      * x.2) * z)) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
      x.2) * z) ^ (n + 1) := by
  calc
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (aperyShiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
     eval y (aperyShiftedLegendre n) * (1 / (1 - (1 - x * y) * z)) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
        norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
          norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [one_div, ← mul_assoc]
    · exact eq1_integrableOn_aux1 n z hz
  _ = ∫ (x : ℝ) in Set.Ioo 0 1, eval x (aperyShiftedLegendre n) * ∫ (y : ℝ) in Set.Ioo 0 1,
    (x * y * z) ^ n * (1 - y) ^ n / (1 - (1 - x * y) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
      norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
          norm_num)]
    rw [legendre_integral_special n hx hz]
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
      x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x _
      simp only
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
        norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
          norm_num),
        ← intervalIntegral.integral_const_mul]
      simp only [mul_div, ← mul_assoc]
    · exact eq1_integrableOn_aux2 n z hz

lemma ineq_aux (x : ℝ × ℝ) (z : ℝ) (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧
  z ≤ 1) :
    0 ≤ (1 - z) / (1 - (1 - x.1 * x.2) * z) ∧ (1 - z) / (1 - (1 - x.1 * x.2) * z) ≤ 1 := by
  constructor
  · apply div_nonneg (by linarith)
    simp only [sub_nonneg]
    refine (mul_le_of_le_one_left (by linarith) ?_).trans (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith
  · rw [div_le_iff₀]
    · simp only [one_mul, tsub_le_iff_right, sub_add, le_sub_self_iff, zero_add]
      by_cases h0 : z = 0
      · simp [h0]
      · suffices (1 - x.1 * x.2) * z < z by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]; nlinarith
        · by_contra!
          have : z = 0 := by linarith
          exact h0 this
    · simp only [sub_pos]
      rw [mul_comm]
      suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
      apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma ineq_aux1 (x : ℝ × ℝ) (z : ℝ) (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z
  ∧ z ≤ 1) :
    1 - (1 - x.1 * x.2) * z ≠ 0 := by
  suffices (1 - x.1 * x.2) * z < 1 by linarith
  rw [mul_comm]
  suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
  apply mul_le_of_le_one_left (by nlinarith) hz.2

lemma fun_eq_aux (x : ℝ × ℝ) (y : ℝ) (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hy : 0 ≤ y
  ∧ y ≤ 1) :
    deriv (fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)) y =
    (fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2) y := by
  rw [deriv_fun_div]
  · rw [deriv_const_sub, deriv_const_sub, deriv_const_mul _ differentiableAt_id]
    simp only [deriv_id'', neg_mul, one_mul, neg_sub, mul_one]
    congr
    ring
  · apply DifferentiableAt.const_sub differentiableAt_id _
  · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
  · exact ineq_aux1 x y hx hy

lemma double_integral_eq2 (n : ℕ) (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) : ∫ (z : ℝ)
  in Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
      x.2) * z) ^ (n + 1) =
    ∫ (z : ℝ) in Set.Ioo 0 1, eval x.1 (aperyShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n /
      (1 - (1 - x.1 * x.2) * z) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  simp only [← mul_div, mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  simp only [mul_div, ← mul_assoc]
  simp_rw [mul_comm (b := (1 - x.2) ^ n), ← mul_div]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  set g := fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)
  set g' := fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2
  have hg : ContinuousOn (deriv g) (Set.uIcc 0 1) := by
    rw [continuousOn_congr (f := g')]
    · simp only [g']
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le, Set.mem_Icc,
          ] at hx hy ⊢
        apply pow_ne_zero
        exact ineq_aux1 x y hx hy
    · intro y hy
      simp only [Set.mem_prod, Set.mem_Ioo, zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hx hy
      exact fun_eq_aux x y hx hy
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  symm
  calc
  _ = -∫ (y : ℝ) in (g 0)..g 1, (1 - y) ^ n / (1 - (1 - x.1 * x.2) * y) := by
    simp only [sub_zero, mul_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self,
      mul_one, sub_sub_cancel, zero_div, g]
    rw [intervalIntegral.integral_symm]
  _ = -∫ (y : ℝ) in (0)..1, (deriv g) y * (1 - g y) ^ n / (1 - (1 - x.1 * x.2) * g y) := by
    rw [neg_inj, ← intervalIntegral.integral_comp_mul_deriv' (f' := deriv g) (h' := hg)]
    · simp only [Function.comp_apply, div_mul_eq_mul_div, mul_comm]
    · intro y hy
      simp only [hasDerivAt_deriv_iff, g]
      apply DifferentiableAt.div (DifferentiableAt.const_sub differentiableAt_id _)
      · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
      · simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
    · have h1 : g '' Set.uIcc 0 1 = Set.Icc 0 1 := by
        simp only [zero_le_one, Set.uIcc_of_le, g]
        ext y
        constructor
        · intro hy
          simp only [Set.mem_image, Set.mem_Icc] at hy
          obtain ⟨z, hz, hz'⟩ := hy
          simp only [Set.mem_Icc]
          rw [← hz']
          exact ineq_aux x z hx hz
        · intro hy
          simp only [Set.mem_Icc] at hy
          simp only [Set.mem_image, Set.mem_Icc]
          use (1 - y) / (1 - (1 - x.1 * x.2) * y)
          constructor
          · exact ineq_aux x y hx hy
          · have eq1 : ((1 - (1 - x.1 * x.2) * y) - (1 - y)) / (1 - (1 - x.1 * x.2) * y) =
                1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
                rw [sub_div, div_self (ineq_aux1 x y hx hy)]
            have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
              (1 - (1 - x.1 * x.2) * y) = 1 - (1 - x.1 * x.2) * ((1 - y) / (1 - (1 - x.1 * x.2)
                * y)) := by
              rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
            rw [div_eq_iff]
            · rw [← eq1, ← eq2, mul_div, div_eq_div_iff (ineq_aux1 x y hx hy) (ineq_aux1 x y hx hy)]
              ring
            · rw [← eq2]
              apply div_ne_zero _ (ineq_aux1 x y hx hy)
              rw [mul_sub]
              simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
                not_or]
              constructor <;> linarith
      rw [h1]
      apply ContinuousOn.div
      · apply ContinuousOn.pow
        apply ContinuousOn.sub continuousOn_const continuousOn_id
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_const continuousOn_id
      · intro y hy
        simp only [Set.mem_Icc] at hy
        exact ineq_aux1 x y hx hy
  _ = ∫ (y : ℝ) in (0)..1, x.1 * x.2 / (1 - (1 - x.1 * x.2) * y) ^ 2 * (1 - g y) ^ n / (1 - (1
    - x.1 * x.2) * g y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    simp only [g]
    rw [fun_eq_aux x y hx hy]
    ring
  _ = ∫ (y : ℝ) in (0)..1, (x.1 * x.2 * y) ^ n / (1 - (1 - x.1 * x.2) * y) ^ (n + 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc] at hy ⊢
    have eq1 : ((1 - (1 - x.1 * x.2) * y) - (1 - y)) / (1 - (1 - x.1 * x.2) * y) =
        1 - (1 - y) / (1 - (1 - x.1 * x.2) * y) := by
        rw [sub_div, div_self (ineq_aux1 x y hx hy)]
    have eq2 : ((1 - (1 - x.1 * x.2) * y) - (1 - x.1 * x.2) * (1 - y)) /
      (1 - (1 - x.1 * x.2) * y) = 1 - (1 - x.1 * x.2) * ((1 - y) / (1 - (1 - x.1 * x.2) * y)) := by
      rw [sub_div, div_self (ineq_aux1 x y hx hy), mul_div]
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff]
    · simp only [← eq1, sub_sub_sub_cancel_left, div_pow, ← eq2, g]
      rw [mul_div, mul_comm, mul_div, mul_div, mul_div, div_eq_div_iff]
      · ring
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · exact ineq_aux1 x y hx hy
    · apply mul_ne_zero
      · apply pow_ne_zero
        exact ineq_aux1 x y hx hy
      · simp only [g, ← eq2]
        apply div_ne_zero _ (ineq_aux1 x y hx hy)
        rw [mul_sub]
        simp only [mul_one, sub_sub_sub_cancel_right, sub_sub_cancel, ne_eq, mul_eq_zero,
          not_or]
        constructor <;> linarith
    · apply pow_ne_zero
      exact ineq_aux1 x y hx hy

lemma eq3_integrableOn_aux (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) :
    MeasureTheory.Integrable (fun x ↦ eval x.1 (aperyShiftedLegendre n) * (1 - x.2) ^ n / (1 -
      (1 - x.1 * x.2) * z))
    ((MeasureTheory.volume.restrict (Set.Ioo 0 1)).prod (MeasureTheory.volume.restrict (Set.Ioo
      0 1))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  apply MeasureTheory.IntegrableOn.integrable
  apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  · apply ContinuousOn.integrableOn_compact
    · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one,isCompact_Icc]
    · simp only [shiftedLegendre_eq_sum, map_pow, map_neg, map_one]
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · simp only [eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, eval_X]
          apply continuousOn_finsetSum
          intro i _
          apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.pow continuousOn_fst
        · apply ContinuousOn.pow (ContinuousOn.sub continuousOn_const continuousOn_snd)
      · apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul _ continuousOn_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.mul continuousOn_fst continuousOn_snd
      · intro x hx
        suffices 1 - (1 - x.1 * x.2) * z > 0 by linarith
        simp only [Set.mem_prod, Set.mem_Icc] at hx
        simp only [Set.mem_Ioo, gt_iff_lt, sub_pos] at hz ⊢
        suffices (1 - x.1 * x.2) * z ≤ z by linarith
        apply mul_le_of_le_one_left (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        nlinarith
  · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

lemma double_integral_eq3 (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo 0 1) : ∫ (x : ℝ × ℝ) in Set.Ioo 0 1
  ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) =
    ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, eval x.1 (aperyShiftedLegendre n) * (1 - x.2)
      ^ n / (1 - (1 - x.1 * x.2) * z) := by
  symm
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod, MeasureTheory.integral_integral_swap]
  · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    simp only
    calc
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n * ∫ (x : ℝ) in Set.Ioo 0 1,
      eval x (aperyShiftedLegendre n) / (1 - (1 - x * y) * z) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only at hy ⊢
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
        norm_num),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
          norm_num),
        ← intervalIntegral.integral_const_mul]
      simp [mul_div, mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, (1 - y) ^ n * ∫ (x : ℝ) in (0)..1, (y * x * z) ^ n * (1 - x)
      ^ n / (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y hy
      simp only
      congr 1
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by
        norm_num)]
      have := legendre_integral_special n hy hz
      simp only [mul_one_div] at this
      simp only [← this]
      simp only [mul_comm]
    _ = ∫ (y : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ) in Set.Ioo 0 1, (1 - y) ^ n * (y * x * z) ^ n * (1
      - x) ^ n / (1 - (1 - y * x) * z) ^ (n + 1) := by
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      simp_rw [mul_div, ← mul_assoc]
    _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
      rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
        MeasureTheory.integral_prod]
      · simp [mul_pow, mul_comm]
      · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
        apply MeasureTheory.IntegrableOn.integrable
        apply MeasureTheory.IntegrableOn.mono_set (t := Set.Icc 0 1 ×ˢ Set.Icc 0 1)
        · apply ContinuousOn.integrableOn_compact
          · simp only [Set.Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one, isCompact_Icc]
          · apply ContinuousOn.div
            · apply ContinuousOn.pow
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_snd)
              apply ContinuousOn.mul _ (ContinuousOn.sub continuousOn_const continuousOn_fst)
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · apply ContinuousOn.pow
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul _ continuousOn_const
              apply ContinuousOn.sub continuousOn_const _
              apply ContinuousOn.mul continuousOn_fst continuousOn_snd
            · intro x hx
              simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ioo] at hx hz
              apply pow_ne_zero
              suffices (1 - x.1 * x.2) * z ≤ z by linarith
              apply mul_le_of_le_one_left (by linarith)
              simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
              nlinarith
        · apply Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  · exact eq3_integrableOn_aux n z hz
  · exact eq3_integrableOn_aux n z hz

theorem JJ_eq_form (n : ℕ) : JJ n = JJ' n := by
  simp only [JJ, JJ']
  calc
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (∫ (z : ℝ) in Set.Ioo 0 1, eval x.1 (aperyShiftedLegendre n) * eval x.2
      (aperyShiftedLegendre n) * (1 / (1 - (1 - x.1 * x.2) * z))) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only [Set.mem_prod, Set.mem_Ioo] at hx ⊢
    rw [mul_assoc, mul_comm, ← integral1, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul] <;>
        nlinarith
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * eval x.2 (aperyShiftedLegendre n) * (1 / (1 - (1 - x.1
      * x.2) * z)) := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ1 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
      x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    exact double_integral_eq1 n z hz
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (x.1 * x.2 * z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 *
      x.2) * z) ^ (n + 1) := by
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ2 n
  _ = ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫ (z : ℝ) in Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z)
      := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x hx
    simp only
    exact double_integral_eq2 n x hx
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    eval x.1 (aperyShiftedLegendre n) * (1 - z) ^ n * (1 - x.2) ^ n / (1 - (1 - x.1 * x.2) * z)
      := by
    symm
    rw [MeasureTheory.integral_integral_swap]
    exact integrableOn_JJ3 n
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, (1 - z) ^ n * ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1) := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [double_integral_eq3 n z hz, mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul]
    ring
  _ = ∫ (z : ℝ) in Set.Ioo 0 1, ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.1 * x.2 * z * (1 - x.1) * (1 - x.2) * (1 - z)) ^ n / (1 - (1 - x.1 * x.2) * z) ^ (n + 1)
      := by
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro z hz
    simp only
    rw [mul_comm, ← smul_eq_mul, ← integral_smul_const]
    apply MeasureTheory.setIntegral_congr_fun (by measurability)
    intro x _
    simp only
    rw [smul_eq_mul, mul_comm, mul_div, ← mul_pow]
    ring
  _ = ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) / (1 - (1 - x.2.1 * x.2.2) *
      x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
    symm
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.integral_prod]
    · apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro x hx
      simp only
      apply MeasureTheory.setIntegral_congr_fun (by measurability)
      intro y _
      simp only
      rw [pow_add, ← div_div, div_pow]
      ring
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact integrableOn_JJ' n

theorem JJ_pos (n : ℕ) : 0 < JJ n := by
  rw [JJ_eq_form, JJ']
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · set F := _;
    change 0 < MeasureTheory.volume.restrict _ (Function.support F)
    have subset : Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ⊆ Function.support F := by
      intro a ha
      change F a ≠ 0
      have hden := pos_aux a (by simpa only [Set.mem_prod, Set.mem_Ioo] using ha)
      simp only [Set.mem_prod, Set.mem_Ioo] at ha
      rcases ha with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩
      apply ne_of_gt
      dsimp only [F]
      positivity
    rw [MeasureTheory.Measure.restrict_apply']
    · rw [Set.inter_eq_right.2 subset]
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      simp only [Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, zero_lt_one]
    · measurability
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [Set.mem_prod, Set.mem_Ioo] at h
        apply div_nonneg
        · apply pow_nonneg
          apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
        · simp only [sub_nonneg]
          exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
      · rw [Set.mem_inter_iff] at hx
        tauto
  · exact integrableOn_JJ' n

lemma Summable_of_zeta_two' : Summable (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
  rw [Summable]
  use Real.pi ^ 2 / 6
  obtain h := hasSum_zeta_two
  let f := fun (n : ℕ) ↦ 1 / (n : ℝ) ^ 2
  let g := fun (n : ℕ) => n + 1
  have h1 : Function.Injective g := by
    intro m n h
    simp only [g] at h
    linarith
  have h2 : ∀ x ∉ Set.range g, f x = 0 := by
    intro x hx
    simp only [Set.mem_range, not_exists] at hx
    suffices x = 0 by simp only [one_div, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero, f, this]
    by_contra! h
    apply hx (x - 1)
    simp only [g]
    omega
  have h3 : f ∘ g = fun (n : ℕ) ↦ 1 / (n + 1 : ℝ) ^ 2 := by
    ext x
    simp [f, g]
  have := Function.Injective.hasSum_iff (f := f) (g := g) (a := (Real.pi ^ 2 / 6 : ℝ)) h1 h2
  rw [h3] at this
  rw [this]
  simp only [f]
  exact h

lemma zeta_3_pos : 0 < ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3 := by
  apply Summable.tsum_pos (ι := ℕ) (g := fun n => 1 / ((n : ℝ) + 1) ^ 3) (i := 1)
  · apply summable_of_sum_range_le (c := Real.pi ^ 2 / 6)
    · intro _
      positivity
    · intro n
      suffices ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 3 ≤
          ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 by
        have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
          suffices ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 by
            have h : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 = (riemannZeta 2).re := by
              rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
              simp_rw [← Complex.ofReal_natCast]
              norm_cast
            rw [h, riemannZeta_two] at this
            norm_cast at *
          apply Summable.sum_le_tsum (s := Finset.range n)
          · intro i _
            positivity
          · exact Summable_of_zeta_two'
        linarith
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_div_iff₀, one_mul, one_mul]
      · apply pow_le_pow_right₀ <;> linarith
      · positivity
      · positivity
  · intro m
    simp only [one_div, pow_succ]
    positivity
  · positivity

theorem JJ_upper (n : ℕ) : JJ n ≤ 2 * (1 / 32) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [JJ_eq_form, JJ', MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · trans (ENNReal.ofReal (2 * (1 / 32 : ℝ) ^ n * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)).toReal
    · apply ENNReal.toReal_mono
      · exact ENNReal.ofReal_ne_top
      · exact JJENN_upper n
    · rw [ENNReal.toReal_ofReal]
      apply mul_nonneg (by norm_num)
      linarith [zeta_3_pos]
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · rw [MeasureTheory.IntegrableOn]
      exact integrableOn_JJ' n
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro x hx
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [Set.mem_prod, Set.mem_Ioo] at h
        apply div_nonneg
        · apply pow_nonneg
          apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · simp only [sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
        · simp only [sub_nonneg]
          exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
      · rw [Set.mem_inter_iff] at hx
        tauto
  · apply Measurable.aestronglyMeasurable
    fun_prop

lemma zeta3_le_zeta2 : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 < ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 := by
  apply Summable.tsum_lt_tsum_of_nonneg (f := fun n => 1 / ((n : ℝ) + 1) ^ 3) 
    (g := fun n => 1 / ((n : ℝ) + 1) ^ 2) (i := 2)
  · intro n
    positivity
  · intro n
    rw [div_le_div_iff₀, one_mul, one_mul]
    · apply pow_le_pow_right₀ <;> linarith
    · positivity
    · positivity
  · norm_num
  · exact Summable_of_zeta_two'

/- Changed in this port: the original took this bound from the prime number theorem
(`π(n) ≤ (1 + ε) n / log n`); here Chebyshev's elementary constant `1.10555...` is used. -/
lemma ε_N_def_of_chebyshev : ∀ c > Problem337.ChebyshevUpperSharp.upperConstant, ∃ N : ℕ,
    ∀ n : ℕ, n ≥ N → n.primeCounting ≤ c * (n : ℝ) / (n : ℝ).log := by
  intro c hc
  have h := Problem337.ChebyshevUpperSharp.eventually_primeCounting_upper
    (c - Problem337.ChebyshevUpperSharp.upperConstant) (sub_pos.mpr hc)
  simp only [add_sub_cancel] at h
  exact Filter.eventually_atTop.mp h

/- Changed in this port: the constant `21` of the original is `30` here. -/
lemma eventuallyN_of_le : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ↑(d (Finset.Icc 1 n)) ^ 3 ≤ (30 : ℝ) ^ n := by
    have h : Real.log ((30 : ℝ) ^ (1 / 3 : ℝ)) > Problem337.ChebyshevUpperSharp.upperConstant := by
      have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
        rw [show (30 : ℝ) = (2 * 3) * 5 by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
          Real.log_mul (by norm_num) (by norm_num)]
      rw [Real.log_rpow (by norm_num), h30]
      linarith [Problem337.ChebyshevUpperSharp.upperConstant_lt_1106_div_1000,
        Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    obtain ⟨N, hN⟩ := ε_N_def_of_chebyshev (Real.log ((30 : ℝ) ^ (1 / 3 : ℝ))) h
    use N + 2
    intro n hn
    specialize hN n (by linarith [hn])
    rw [Real.log_rpow (by norm_num)] at hN
    calc
    _ ≤ ((n : ℝ) ^ (n.primeCounting)) ^ 3 := by
      norm_cast
      apply pow_le_pow_left₀ (by simp)
      exact d_le_pow_counting n
    _ ≤ (n ^ (1 / 3 * Real.log 30 * ↑n / Real.log ↑n)) ^ 3 := by
      apply pow_le_pow_left₀ (by simp)
      rw [← Real.rpow_natCast, Real.rpow_le_rpow_left_iff]
      · exact hN
      · simp only [Nat.one_lt_cast]
        omega
    _ ≤ (30 : ℝ) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by simp), mul_comm]
      nth_rewrite 1 [← Real.exp_log (x := n) (by simp only [Nat.cast_pos]; omega)]
      have h2 : Real.log ↑n * (↑3 * (1 / 3 * Real.log 30 * ↑n / Real.log ↑n)) = 
          Real.log 30 * ↑n := by
        rw [← mul_assoc, mul_div, ← mul_assoc, ← mul_assoc]
        simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.mul_inv_cancel_right]
        rw [mul_rotate, ← mul_div, div_self, mul_one]
        simp only [ne_eq, Real.log_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, not_or]
        norm_cast
        simp only [not_false_eq_true, and_true]
        constructor <;> omega
      rw [← Real.exp_one_rpow, ← Real.rpow_mul (by exact Real.exp_nonneg 1)]
      norm_cast
      rw [h2, Real.rpow_mul (by exact Real.exp_nonneg 1), Real.exp_one_rpow,
        Real.exp_log (by norm_num)]
      norm_cast

theorem fun1_tendsto_zero : Filter.Tendsto (fun n ↦ ENNReal.ofReal (fun1 n)) Filter.atTop (nhds
  0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  if h : ε = ⊤ then simp [h]
  else
    delta fun1
    rw [show ε = ENNReal.ofReal ε.toReal by simp [h]]
    obtain ⟨N, hN⟩ := eventuallyN_of_le
    obtain h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (ENNReal.ofReal (30 / 32 : ℝ)))
      (by simp only [ENNReal.ofReal_lt_one]; norm_num)
    rw [ENNReal.tendsto_atTop_zero] at h
    specialize h (ε / (ENNReal.ofReal (2 * (∑' n : ℕ , 1 / ((n : ℝ)+ 1) ^ 3))))
      (by simp only [one_div, gt_iff_lt, ENNReal.div_pos_iff, ne_eq, ENNReal.ofReal_ne_top,
        not_false_eq_true, and_true]; aesop)
    obtain ⟨N1, hN1⟩ := h
    use N.max N1
    intro n hn
    rw [ENNReal.ofReal_le_ofReal_iff (by simp)]
    suffices ↑(d (Finset.Icc 1 n)) ^ 3 * 2 * (1 / 32) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 ≤
      ε.toReal by
      trans ↑(d (Finset.Icc 1 n)) ^ 3 * 2 * (1 / 32) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3
      · rw [mul_assoc, mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by simp)
        linarith [JJ_upper n]
      · exact this
    calc
    _ ≤ 2 * (30 / 32 : ℝ) ^ n * (∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith[zeta_3_pos])
      nth_rewrite 2 [mul_comm, div_eq_mul_one_div]
      rw [mul_pow, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hN n (le_of_max_le_left hn)
    _ ≤ ε.toReal := by
      specialize hN1 n (le_of_max_le_right hn)
      rw [← ENNReal.ofReal_toReal_eq_iff.2 h, ← ENNReal.ofReal_div_of_pos (by linarith
        [zeta_3_pos]),
        ← ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_le_ofReal_iff] at hN1
      · rw [le_div_iff₀ (by linarith [zeta_3_pos])] at hN1
        linarith
      · suffices 0 <  ε.toReal / (2 * ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3)by linarith
        apply div_pos _ (by linarith [zeta_3_pos])
        apply ENNReal.toReal_pos (by aesop) (by aesop)

theorem zeta_3_irratoinal : ¬ ∃ r : ℚ , r = riemannZeta 3 := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
  simp_rw [← Complex.ofReal_natCast]
  norm_cast
  simp_rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  by_contra! r
  obtain ⟨r, hr⟩ := r
  let q := r.den
  let hq := Rat.den_nz r
  have prop1 := ENNReal.Tendsto.mul_const (b := (q : ENNReal)) (fun1_tendsto_zero) (by simp)
  rw [zero_mul] at prop1
  have prop2 : ∀ n : ℕ, fun1 n * q > 1/2 := by
    suffices ∀ n : ℕ, fun1 n * q ≥ 1 by intro n; linarith [this n]
    intro n
    obtain ⟨a, b, h⟩ := linear_int n
    have : fun1 n * q > 0 := by
      delta fun1
      rw [mul_comm, ← mul_assoc]
      refine mul_pos ?_ (JJ_pos n)
      norm_cast
      apply mul_pos (by omega)
      exact pow_pos (fin_d_neq_zero n) 3
    rw [h, add_mul, mul_assoc, ← hr] at this ⊢
    simp only [ge_iff_le, q] at this ⊢
    norm_cast at this ⊢
    rw [Rat.mul_den_eq_num] at this ⊢
    norm_cast at this ⊢
  rw [ENNReal.tendsto_atTop_zero] at prop1
  specialize prop1 (1/2) (by simp)
  simp only [one_div] at prop1
  rw [← one_div] at prop1
  simp only [ge_iff_le] at prop1
  obtain ⟨a, ha⟩ := prop1
  specialize prop2 (a + 1)
  specialize ha (a + 1) (by simp)
  rw [gt_iff_lt, ← ENNReal.ofReal_lt_ofReal_iff, ENNReal.ofReal_mul' (by simp)] at prop2
  · have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp
    rw [ENNReal.ofReal_natCast, hhalf] at prop2
    exact not_lt_of_ge ha prop2
  · apply mul_pos _ (by simp; omega)
    apply mul_pos _ (JJ_pos (a + 1))
    apply pow_pos
    simp only [Nat.cast_pos]
    exact fin_d_neq_zero (a + 1)

end Zeta3_Basic

end OMAPort_Zeta3

theorem OMA.solution : type_of% @RiemannZetaValues.irrational_three := by
  have hz : riemannZeta 3 = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num), Complex.ofReal_tsum]
    simp_rw [← Complex.ofReal_natCast]
    norm_cast
  refine ⟨_, ?_, hz⟩
  rintro ⟨r, hr⟩
  exact OMAPort_Zeta3.zeta_3_irratoinal ⟨r, by rw [hz, ← hr]; norm_cast⟩
