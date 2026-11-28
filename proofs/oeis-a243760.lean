import OMAStatements.S_oeis_a243760
import Mathlib

namespace OMA.P243760

open PowerSeries

lemma dOfNat (m : ℕ) [m.AtLeastTwo] : derivative ℚ (ofNat(m) : PowerSeries ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℚ)]
  exact Derivation.map_natCast _ _

lemma half (a : PowerSeries ℚ) (h : 2 * a = 0) : a = 0 := by
  have h2 : (2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp only [map_ofNat, map_zero] at h'
    norm_num at h'
  exact (mul_eq_zero.mp h).resolve_left h2

/-- Differentiating a relation in a two-dimensional module closed under the derivative. -/
lemma mod_d (W U H K K' p q r s a b a' b' : PowerSeries ℚ) (hK : derivative ℚ K = K')
    (ha : derivative ℚ a = a') (hb : derivative ℚ b = b')
    (hW : K * derivative ℚ W = p * W + q * U) (hU : K * derivative ℚ U = r * W + s * U)
    (e1 : K * derivative ℚ H = a * W + b * U) :
    K * (K' * derivative ℚ H + K * derivative ℚ (derivative ℚ H))
      = (a' * K + a * p + b * r) * W + (b' * K + a * q + b * s) * U := by
  have h := congrArg (derivative ℚ) e1
  simp only [map_add, Derivation.leibniz, smul_eq_mul] at h
  rw [hK, ha, hb] at h
  linear_combination K * h + a * hW + b * hU

/-- Differentiating a second-order relation with one extra generator. -/
lemma ord2_d (G T y2 y2' y1 y1' y0 y0' r0 r0' r1 r1' : PowerSeries ℚ) (h2 : derivative ℚ y2 = y2')
    (h1 : derivative ℚ y1 = y1') (h0 : derivative ℚ y0 = y0') (hr0 : derivative ℚ r0 = r0')
    (hr1 : derivative ℚ r1 = r1')
    (h : y2 * derivative ℚ (derivative ℚ G) + y1 * derivative ℚ G + y0 * G = r0 + r1 * T) :
    y2 * derivative ℚ (derivative ℚ (derivative ℚ G)) + (y2' + y1) * derivative ℚ (derivative ℚ G)
      + (y1' + y0) * derivative ℚ G + y0' * G = r0' + r1' * T + r1 * derivative ℚ T := by
  have h' := congrArg (derivative ℚ) h
  simp only [map_add, Derivation.leibniz, smul_eq_mul] at h'
  rw [h2, h1, h0, hr0, hr1] at h'
  linear_combination h'

lemma coeff_theta (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * derivative ℚ F) = (k : ℚ) * coeff k F := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma theta2 (G : PowerSeries ℚ) : X * derivative ℚ (X * derivative ℚ G)
    = X * derivative ℚ G + X ^ 2 * derivative ℚ (derivative ℚ G) := by
  rw [Derivation.leibniz, derivative_X]
  simp only [smul_eq_mul]
  ring

lemma theta3 (G : PowerSeries ℚ) : X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G))
    = X * derivative ℚ G + 3 * X ^ 2 * derivative ℚ (derivative ℚ G)
      + X ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
  rw [theta2]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul, nsmul_eq_mul,
    Derivation.map_one_eq_zero, mul_zero, add_zero]
  push_cast
  ring

lemma dD1 : derivative ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dK : derivative ℚ (-7 + 44 * X - 256 * X ^ 3 : PowerSeries ℚ) = 44 - 768 * X ^ 2 := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma da1 : derivative ℚ (-64 * X + 256 * X ^ 2 : PowerSeries ℚ) = -64 + 512 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma db1 : derivative ℚ (-14 - 16 * X + 256 * X ^ 2 : PowerSeries ℚ) = -16 + 512 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dy2 : derivative ℚ (49 * X - 476 * X ^ 2 + 1056 * X ^ 3 + 1792 * X ^ 4 - 6144 * X ^ 5 : PowerSeries ℚ) = 49 - 952 * X + 3168 * X ^ 2 + 7168 * X ^ 3 - 30720 * X ^ 4 := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dy1 : derivative ℚ (98 - 938 * X + 1584 * X ^ 2 + 6272 * X ^ 3 - 15360 * X ^ 4 : PowerSeries ℚ) = -938 + 3168 * X + 18816 * X ^ 2 - 61440 * X ^ 3 := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dy0 : derivative ℚ (14 - 24 * X - 192 * X ^ 2 : PowerSeries ℚ) = -24 - 384 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma drho0 : derivative ℚ (63 - 360 * X + 384 * X ^ 2 : PowerSeries ℚ) = -360 + 768 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma drho1 : derivative ℚ (35 - 200 * X + 384 * X ^ 2 : PowerSeries ℚ) = -200 + 768 * X := by
  simp only [map_add, map_sub, map_neg, map_zero, map_mul, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma nz_c : (14 - 88 * X + 512 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

lemma nz_y : (8 - 64 * X + 128 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

lemma nz_g : (-7 + 24 * X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

/-- (1 - 4X) T' = -2 T. -/
lemma hT1 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (1 - 4 * X) * derivative ℚ T = -2 * T := by
  have hT' : T * T = 1 - 4 * X := by rw [← pow_two]; exact hT
  have h := congrArg (derivative ℚ) hT'
  rw [Derivation.leibniz, dD1] at h
  simp only [smul_eq_mul] at h
  have h2 : 2 * ((1 - 4 * X) * derivative ℚ T - -2 * T) = 0 := by
    linear_combination T * h - 2 * derivative ℚ T * hT
  have := half _ h2
  linear_combination this

lemma hT2 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (1 - 4 * X) * derivative ℚ (derivative ℚ T) = 2 * derivative ℚ T := by
  have h := congrArg (derivative ℚ) (hT1 T W G hT hW hG)
  rw [Derivation.leibniz, Derivation.leibniz, dD1] at h
  simp only [smul_eq_mul, map_neg, dOfNat] at h
  linear_combination h

/-- The derivative of W in the module spanned by W and T W. -/
lemma hW1 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (-7 + 44 * X - 256 * X ^ 3) * derivative ℚ W = (4 + 16 * X - 128 * X ^ 2) * W + (-4 + 32 * X) * (T * W) := by
  have hW' : W * W = 8 * X + 4 * T - 3 := by rw [← pow_two]; exact hW
  have h := congrArg (derivative ℚ) hW'
  have e : derivative ℚ (8 * X + 4 * T - 3 : PowerSeries ℚ) = 8 + 4 * derivative ℚ T := by
    simp only [map_add, map_sub, Derivation.leibniz, derivative_X, dOfNat, smul_eq_mul]
    ring
  rw [Derivation.leibniz, e] at h
  simp only [smul_eq_mul] at h
  have h1 := hT1 T W G hT hW hG
  have h2 : 2 * ((-7 + 44 * X - 256 * X ^ 3) * derivative ℚ W - ((4 + 16 * X - 128 * X ^ 2) * W + (-4 + 32 * X) * (T * W))) = 0 := by
    linear_combination (32 * (1 - 4 * X) * derivative ℚ W + 32 * W) * hT
      - 2 * (8 * X - 3 - 4 * T) * (1 - 4 * X) * derivative ℚ W * hW
      + W * (8 * X - 3 - 4 * T) * (1 - 4 * X) * h + 4 * W * (8 * X - 3 - 4 * T) * h1
  have := half _ h2
  linear_combination this

lemma hU1 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (-7 + 44 * X - 256 * X ^ 3) * derivative ℚ (T * W) = (-4 + 48 * X - 128 * X ^ 2) * W + (18 - 16 * X - 256 * X ^ 2) * (T * W) := by
  have e : derivative ℚ (T * W) = T * derivative ℚ W + W * derivative ℚ T := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
  rw [e]
  linear_combination T * hW1 T W G hT hW hG + (-7 + 16 * X + 64 * X ^ 2) * W * hT1 T W G hT hW hG + (-4 + 32 * X) * W * hT

/-- H = 8 X G - 1 - T lies in the module: H = -W - T W. -/
lemma e0 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (8 * X * G - 1 - T) + W + T * W = 0 := by
  have h2 : 2 * ((8 * X * G - 1 - T) + W + T * W) = 0 := by
    linear_combination (-(2 * T + 2)) * hG + 4 * G * hT
  exact half _ h2

lemma e1 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (-7 + 44 * X - 256 * X ^ 3) * derivative ℚ (8 * X * G - 1 - T) = (-64 * X + 256 * X ^ 2) * W + (-14 - 16 * X + 256 * X ^ 2) * (T * W) := by
  have h := congrArg (derivative ℚ) (e0 T W G hT hW hG)
  simp only [map_add, map_zero] at h
  linear_combination (-7 + 44 * X - 256 * X ^ 3) * h - hW1 T W G hT hW hG - hU1 T W G hT hW hG

lemma e2 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (-7 + 44 * X - 256 * X ^ 3) * ((44 - 768 * X ^ 2) * derivative ℚ (8 * X * G - 1 - T) + (-7 + 44 * X - 256 * X ^ 3) * derivative ℚ (derivative ℚ (8 * X * G - 1 - T)))
    = (504 - 7264 * X + 22528 * X ^ 2 + 43008 * X ^ 3 - 196608 * X ^ 4) * W + (-140 - 4096 * X + 27904 * X ^ 2 + 12288 * X ^ 3 - 196608 * X ^ 4) * (T * W) := by
  have h := mod_d W (T * W) (8 * X * G - 1 - T) (-7 + 44 * X - 256 * X ^ 3) (44 - 768 * X ^ 2) (4 + 16 * X - 128 * X ^ 2) (-4 + 32 * X) (-4 + 48 * X - 128 * X ^ 2) (18 - 16 * X - 256 * X ^ 2)
    (-64 * X + 256 * X ^ 2) (-14 - 16 * X + 256 * X ^ 2) (-64 + 512 * X) (-16 + 512 * X) dK da1 db1 (hW1 T W G hT hW hG) (hU1 T W G hT hW hG) (e1 T W G hT hW hG)
  linear_combination h

/-- The second-order equation of H. -/
lemma ode2 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (49 - 476 * X + 1056 * X ^ 2 + 1792 * X ^ 3 - 6144 * X ^ 4) * derivative ℚ (derivative ℚ (8 * X * G - 1 - T)) + (14 - 528 * X + 2688 * X ^ 2 - 3072 * X ^ 3) * derivative ℚ (8 * X * G - 1 - T)
    + (504 - 2880 * X + 3072 * X ^ 2) * (8 * X * G - 1 - T) = 0 := by
  have hm : (14 - 88 * X + 512 * X ^ 3) * ((49 - 476 * X + 1056 * X ^ 2 + 1792 * X ^ 3 - 6144 * X ^ 4) * derivative ℚ (derivative ℚ (8 * X * G - 1 - T)) + (14 - 528 * X + 2688 * X ^ 2 - 3072 * X ^ 3) * derivative ℚ (8 * X * G - 1 - T)
      + (504 - 2880 * X + 3072 * X ^ 2) * (8 * X * G - 1 - T)) = 0 := by
    linear_combination (7056 - 84672 * X + 296448 * X ^ 2 - 12288 * X ^ 3 - 1474560 * X ^ 4 + 1572864 * X ^ 5) * e0 T W G hT hW hG + (-644 + 3168 * X + 5376 * X ^ 2 - 30720 * X ^ 3) * e1 T W G hT hW hG + (14 - 48 * X) * e2 T W G hT hW hG
  exact (mul_eq_zero.mp hm).resolve_left nz_c

lemma dH_eq (T G : PowerSeries ℚ) : derivative ℚ (8 * X * G - 1 - T) = 8 * G + 8 * X * derivative ℚ G - derivative ℚ T := by
  simp only [map_sub, Derivation.leibniz, derivative_X, dOfNat, smul_eq_mul, Derivation.map_one_eq_zero]
  ring

lemma ddH_eq (T G : PowerSeries ℚ) : derivative ℚ (derivative ℚ (8 * X * G - 1 - T))
    = 16 * derivative ℚ G + 8 * X * derivative ℚ (derivative ℚ G) - derivative ℚ (derivative ℚ T) := by
  rw [dH_eq]
  simp only [map_sub, map_add, Derivation.leibniz, derivative_X, dOfNat, smul_eq_mul]
  ring

/-- Second-order equation for G with the generator T on the right. -/
lemma hY (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (49 * X - 476 * X ^ 2 + 1056 * X ^ 3 + 1792 * X ^ 4 - 6144 * X ^ 5) * derivative ℚ (derivative ℚ G) + (98 - 938 * X + 1584 * X ^ 2 + 6272 * X ^ 3 - 15360 * X ^ 4) * derivative ℚ G + (14 - 24 * X - 192 * X ^ 2) * G
    = (63 - 360 * X + 384 * X ^ 2) + (35 - 200 * X + 384 * X ^ 2) * T := by
  have h := ode2 T W G hT hW hG
  rw [ddH_eq, dH_eq] at h
  have hm : (8 - 64 * X + 128 * X ^ 2) * ((49 * X - 476 * X ^ 2 + 1056 * X ^ 3 + 1792 * X ^ 4 - 6144 * X ^ 5) * derivative ℚ (derivative ℚ G) + (98 - 938 * X + 1584 * X ^ 2 + 6272 * X ^ 3 - 15360 * X ^ 4) * derivative ℚ G + (14 - 24 * X - 192 * X ^ 2) * G
      - ((63 - 360 * X + 384 * X ^ 2) + (35 - 200 * X + 384 * X ^ 2) * T)) = 0 := by
    linear_combination (1 - 8 * X + 16 * X ^ 2) * h + (49 - 672 * X + 2960 * X ^ 2 - 2432 * X ^ 3 - 13312 * X ^ 4 + 24576 * X ^ 5) * hT2 T W G hT hW hG + (112 - 1536 * X + 6912 * X ^ 2 - 10240 * X ^ 3) * hT1 T W G hT hW hG
  have := (mul_eq_zero.mp hm).resolve_left nz_y
  linear_combination this

/-- The third-order equation in the form of the stated recurrence. -/
lemma hT3 (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : (420 * X ^ 2 - 4176 * X ^ 3 + 7296 * X ^ 4 + 6144 * X ^ 5) * G + (-840 * X ^ 2 - 6012 * X ^ 3 + 142080 * X ^ 4 - 708096 * X ^ 5 + 1529856 * X ^ 6 - 1474560 * X ^ 7) * derivative ℚ G + (735 * X ^ 2 - 12180 * X ^ 3 + 66528 * X ^ 4 - 86016 * X ^ 5 - 448512 * X ^ 6 + 1769472 * X ^ 7 - 1966080 * X ^ 8) * derivative ℚ (derivative ℚ G) + (245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) - (630 * X ^ 2 - 8112 * X ^ 3 + 24576 * X ^ 4 - 12288 * X ^ 5) = 0 := by
  have h := hY T W G hT hW hG
  have h' := ord2_d G T (49 * X - 476 * X ^ 2 + 1056 * X ^ 3 + 1792 * X ^ 4 - 6144 * X ^ 5) (49 - 952 * X + 3168 * X ^ 2 + 7168 * X ^ 3 - 30720 * X ^ 4) (98 - 938 * X + 1584 * X ^ 2 + 6272 * X ^ 3 - 15360 * X ^ 4) (-938 + 3168 * X + 18816 * X ^ 2 - 61440 * X ^ 3) (14 - 24 * X - 192 * X ^ 2) (-24 - 384 * X)
    (63 - 360 * X + 384 * X ^ 2) (-360 + 768 * X) (35 - 200 * X + 384 * X ^ 2) (-200 + 768 * X) dy2 dy1 dy0 drho0 drho1 h
  have hm : (-7 + 24 * X) * ((420 * X ^ 2 - 4176 * X ^ 3 + 7296 * X ^ 4 + 6144 * X ^ 5) * G + (-840 * X ^ 2 - 6012 * X ^ 3 + 142080 * X ^ 4 - 708096 * X ^ 5 + 1529856 * X ^ 6 - 1474560 * X ^ 7) * derivative ℚ G + (735 * X ^ 2 - 12180 * X ^ 3 + 66528 * X ^ 4 - 86016 * X ^ 5 - 448512 * X ^ 6 + 1769472 * X ^ 7 - 1966080 * X ^ 8) * derivative ℚ (derivative ℚ G) + (245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) - (630 * X ^ 2 - 8112 * X ^ 3 + 24576 * X ^ 4 - 12288 * X ^ 5)) = 0 := by
    linear_combination ((-X ^ 2) * (35 - 340 * X + 1184 * X ^ 2 - 1536 * X ^ 3)) * h' + ((-X ^ 2) * (270 - 1968 * X + 3840 * X ^ 2)) * h
      + ((-X ^ 2) * (1225 - 14000 * X + 66880 * X ^ 2 - 153600 * X ^ 3 + 147456 * X ^ 4)) * hT1 T W G hT hW hG
  exact (mul_eq_zero.mp hm).resolve_left nz_g

lemma hTC (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) : C (420 : ℚ) * (X ^ 2 * (G)) + C (-4176 : ℚ) * (X ^ 3 * (G)) + C (7296 : ℚ) * (X ^ 4 * (G)) + C (6144 : ℚ) * (X ^ 5 * (G)) + C (-245 : ℚ) * (X ^ 0 * (X * derivative ℚ G)) + C (3500 : ℚ) * (X ^ 1 * (X * derivative ℚ G)) + C (-26044 : ℚ) * (X ^ 2 * (X * derivative ℚ G)) + C (120320 : ℚ) * (X ^ 3 * (X * derivative ℚ G)) + C (-298496 : ℚ) * (X ^ 4 * (X * derivative ℚ G)) + C (366592 : ℚ) * (X ^ 5 * (X * derivative ℚ G)) + C (-294912 : ℚ) * (X ^ 6 * (X * derivative ℚ G)) + C (-420 : ℚ) * (X ^ 1 * (X * derivative ℚ (X * derivative ℚ G))) + C (-3216 : ℚ) * (X ^ 2 * (X * derivative ℚ (X * derivative ℚ G))) + C (75648 : ℚ) * (X ^ 3 * (X * derivative ℚ (X * derivative ℚ G))) + C (-390144 : ℚ) * (X ^ 4 * (X * derivative ℚ (X * derivative ℚ G))) + C (860160 : ℚ) * (X ^ 5 * (X * derivative ℚ (X * derivative ℚ G))) + C (-786432 : ℚ) * (X ^ 6 * (X * derivative ℚ (X * derivative ℚ G))) + C (245 : ℚ) * (X ^ 0 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (-3920 : ℚ) * (X ^ 1 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (23248 : ℚ) * (X ^ 2 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (-53888 : ℚ) * (X ^ 3 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (-19456 : ℚ) * (X ^ 4 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (303104 : ℚ) * (X ^ 5 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) + C (-393216 : ℚ) * (X ^ 6 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) - (C (630 : ℚ) * X ^ 2 + C (-8112 : ℚ) * X ^ 3 + C (24576 : ℚ) * X ^ 4 + C (-12288 : ℚ) * X ^ 5) = 0 := by
  have h := hT3 T W G hT hW hG
  simp only [map_ofNat, map_neg, map_one, map_zero]
  linear_combination h + (-420 * X - 3216 * X ^ 2 + 75648 * X ^ 3 - 390144 * X ^ 4 + 860160 * X ^ 5 - 786432 * X ^ 6) * theta2 G + (245 - 3920 * X + 23248 * X ^ 2 - 53888 * X ^ 3 - 19456 * X ^ 4 + 303104 * X ^ 5 - 393216 * X ^ 6) * theta3 G

lemma hrec (T W G : PowerSeries ℚ) (hT : T ^ 2 = 1 - 4 * X) (hW : W ^ 2 = 8 * X + 4 * T - 3) (hG : G * (2 * T - 2) = W - 1) (N : ℕ) : ((-245) * ((N : ℚ) + 6) ^ 1 + (245) * ((N : ℚ) + 6) ^ 3) * coeff (N + 6) G + ((-7420) * ((N : ℚ) + 6) ^ 1 + (11340) * ((N : ℚ) + 6) ^ 2 + (-3920) * ((N : ℚ) + 6) ^ 3) * coeff (N + 5) G + ((-146340) * ((N : ℚ) + 6) ^ 0 + (265796) * ((N : ℚ) + 6) ^ 1 + (-142704) * ((N : ℚ) + 6) ^ 2 + (23248) * ((N : ℚ) + 6) ^ 3) * coeff (N + 4) G + ((1770672) * ((N : ℚ) + 6) ^ 0 + (-1788544) * ((N : ℚ) + 6) ^ 1 + (560640) * ((N : ℚ) + 6) ^ 2 + (-53888) * ((N : ℚ) + 6) ^ 3) * coeff (N + 3) G + ((-3795840) * ((N : ℚ) + 6) ^ 0 + (1888768) * ((N : ℚ) + 6) ^ 1 + (-156672) * ((N : ℚ) + 6) ^ 2 + (-19456) * ((N : ℚ) + 6) ^ 3) * coeff (N + 2) G + ((-18210816) * ((N : ℚ) + 6) ^ 0 + (14497792) * ((N : ℚ) + 6) ^ 1 + (-3686400) * ((N : ℚ) + 6) ^ 2 + (303104) * ((N : ℚ) + 6) ^ 3) * coeff (N + 1) G + ((58392576) * ((N : ℚ) + 6) ^ 0 + (-33325056) * ((N : ℚ) + 6) ^ 1 + (6291456) * ((N : ℚ) + 6) ^ 2 + (-393216) * ((N : ℚ) + 6) ^ 3) * coeff (N + 0) G = 0 := by
  have h := congrArg (coeff (N + 6)) (hTC T W G hT hW hG)
  have e2_0 : coeff (N + 6) (X ^ 2 * (G)) = ((N : ℚ) + 4) ^ 0 * coeff (N + 4) G := by
    rw [show N + 6 = N + 4 + 2 from rfl, coeff_X_pow_mul]
    push_cast
    ring
  have e3_0 : coeff (N + 6) (X ^ 3 * (G)) = ((N : ℚ) + 3) ^ 0 * coeff (N + 3) G := by
    rw [show N + 6 = N + 3 + 3 from rfl, coeff_X_pow_mul]
    push_cast
    ring
  have e4_0 : coeff (N + 6) (X ^ 4 * (G)) = ((N : ℚ) + 2) ^ 0 * coeff (N + 2) G := by
    rw [show N + 6 = N + 2 + 4 from rfl, coeff_X_pow_mul]
    push_cast
    ring
  have e5_0 : coeff (N + 6) (X ^ 5 * (G)) = ((N : ℚ) + 1) ^ 0 * coeff (N + 1) G := by
    rw [show N + 6 = N + 1 + 5 from rfl, coeff_X_pow_mul]
    push_cast
    ring
  have e0_1 : coeff (N + 6) (X ^ 0 * (X * derivative ℚ G)) = ((N : ℚ) + 6) ^ 1 * coeff (N + 6) G := by
    rw [show N + 6 = N + 6 + 0 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e1_1 : coeff (N + 6) (X ^ 1 * (X * derivative ℚ G)) = ((N : ℚ) + 5) ^ 1 * coeff (N + 5) G := by
    rw [show N + 6 = N + 5 + 1 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e2_1 : coeff (N + 6) (X ^ 2 * (X * derivative ℚ G)) = ((N : ℚ) + 4) ^ 1 * coeff (N + 4) G := by
    rw [show N + 6 = N + 4 + 2 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e3_1 : coeff (N + 6) (X ^ 3 * (X * derivative ℚ G)) = ((N : ℚ) + 3) ^ 1 * coeff (N + 3) G := by
    rw [show N + 6 = N + 3 + 3 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e4_1 : coeff (N + 6) (X ^ 4 * (X * derivative ℚ G)) = ((N : ℚ) + 2) ^ 1 * coeff (N + 2) G := by
    rw [show N + 6 = N + 2 + 4 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e5_1 : coeff (N + 6) (X ^ 5 * (X * derivative ℚ G)) = ((N : ℚ) + 1) ^ 1 * coeff (N + 1) G := by
    rw [show N + 6 = N + 1 + 5 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e6_1 : coeff (N + 6) (X ^ 6 * (X * derivative ℚ G)) = ((N : ℚ) + 0) ^ 1 * coeff (N + 0) G := by
    rw [show N + 6 = N + 0 + 6 from rfl, coeff_X_pow_mul, coeff_theta]
    push_cast
    ring
  have e1_2 : coeff (N + 6) (X ^ 1 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 5) ^ 2 * coeff (N + 5) G := by
    rw [show N + 6 = N + 5 + 1 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e2_2 : coeff (N + 6) (X ^ 2 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 4) ^ 2 * coeff (N + 4) G := by
    rw [show N + 6 = N + 4 + 2 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e3_2 : coeff (N + 6) (X ^ 3 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 3) ^ 2 * coeff (N + 3) G := by
    rw [show N + 6 = N + 3 + 3 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e4_2 : coeff (N + 6) (X ^ 4 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 2) ^ 2 * coeff (N + 2) G := by
    rw [show N + 6 = N + 2 + 4 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e5_2 : coeff (N + 6) (X ^ 5 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 1) ^ 2 * coeff (N + 1) G := by
    rw [show N + 6 = N + 1 + 5 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e6_2 : coeff (N + 6) (X ^ 6 * (X * derivative ℚ (X * derivative ℚ G))) = ((N : ℚ) + 0) ^ 2 * coeff (N + 0) G := by
    rw [show N + 6 = N + 0 + 6 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta]
    push_cast
    ring
  have e0_3 : coeff (N + 6) (X ^ 0 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 6) ^ 3 * coeff (N + 6) G := by
    rw [show N + 6 = N + 6 + 0 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e1_3 : coeff (N + 6) (X ^ 1 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 5) ^ 3 * coeff (N + 5) G := by
    rw [show N + 6 = N + 5 + 1 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e2_3 : coeff (N + 6) (X ^ 2 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 4) ^ 3 * coeff (N + 4) G := by
    rw [show N + 6 = N + 4 + 2 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e3_3 : coeff (N + 6) (X ^ 3 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 3) ^ 3 * coeff (N + 3) G := by
    rw [show N + 6 = N + 3 + 3 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e4_3 : coeff (N + 6) (X ^ 4 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 2) ^ 3 * coeff (N + 2) G := by
    rw [show N + 6 = N + 2 + 4 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e5_3 : coeff (N + 6) (X ^ 5 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 1) ^ 3 * coeff (N + 1) G := by
    rw [show N + 6 = N + 1 + 5 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have e6_3 : coeff (N + 6) (X ^ 6 * (X * derivative ℚ (X * derivative ℚ (X * derivative ℚ G)))) = ((N : ℚ) + 0) ^ 3 * coeff (N + 0) G := by
    rw [show N + 6 = N + 0 + 6 from rfl, coeff_X_pow_mul, coeff_theta, coeff_theta, coeff_theta]
    push_cast
    ring
  have s2 : coeff (N + 6) (X ^ 2 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s3 : coeff (N + 6) (X ^ 3 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s4 : coeff (N + 6) (X ^ 4 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s5 : coeff (N + 6) (X ^ 5 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  simp only [map_add, map_sub, coeff_C_mul, e2_0, e3_0, e4_0, e5_0, e0_1, e1_1, e2_1, e3_1, e4_1, e5_1, e6_1, e1_2, e2_2, e3_2, e4_2, e5_2, e6_2, e0_3, e1_3, e2_3, e3_3, e4_3, e5_3, e6_3, s2, s3, s4, s5, map_zero, mul_zero, sub_zero, add_zero] at h
  linear_combination h

end OMA.P243760

theorem OMA.solution : type_of% @OMA.S_oeis_a243760.main := by
  intro T W G hT _ hW _ hG _ n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 6 := ⟨n - 6, by omega⟩
  have h := OMA.P243760.hrec T W G hT hW hG N
  have t1 : N + 6 - 1 = N + 5 := by omega
  have t2 : N + 6 - 2 = N + 4 := by omega
  have t3 : N + 6 - 3 = N + 3 := by omega
  have t4 : N + 6 - 4 = N + 2 := by omega
  have t5 : N + 6 - 5 = N + 1 := by omega
  have t6 : N + 6 - 6 = N + 0 := by omega
  simp only [t1, t2, t3, t4, t5, t6]
  push_cast
  linear_combination h
