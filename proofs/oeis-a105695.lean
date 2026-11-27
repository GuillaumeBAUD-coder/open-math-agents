import OMAStatements.S_oeis_a105695
import Mathlib

open PowerSeries
open scoped PowerSeries

noncomputable abbrev Fps := FractionRing ℚ⟦X⟧

noncomputable instance : CharZero Fps := by
  let f : ℚ →+* Fps := (algebraMap ℚ⟦X⟧ Fps).comp C
  have hf : Function.Injective f := by
    exact (IsFractionRing.injective ℚ⟦X⟧ Fps).comp PowerSeries.C_injective
  exact charZero_of_injective_ringHom hf

lemma ode_elim {K : Type*} [Field K] [CharZero K] (x t g tp gp : K)
    (hT : t ^ 2 * (1 + x) = 1 - 3 * x)
    (hT' : t^2 + 2 * t * tp * (1 + x) = -3)
    (hkey : t*g + 2*x + g - 2 = 0)
    (hG' : 2 * g + 2 * x * gp = -2 * x * (1 - t) - (1 - x) * (1 + x) * tp) :
    x * (1 - x^2) * (1 - 3 * x) * gp +
      (1 - x - x^2 - 3 * x^3) * g - (1 - x) * (1 - x^2) = 0 := by
  grobner


lemma coeff_Xpow (H : ℚ⟦X⟧) (k n : ℕ) (hkn : k ≤ n) :
    coeff n (X^k * H) = coeff (n - k) H := by
  rw [coeff_X_pow_mul' H k n, if_pos hkn]

lemma coeff_Xpow_three (H : ℚ⟦X⟧) (k n : ℕ) (hkn : k ≤ n) :
    coeff n (X^k * H * 3) = 3 * coeff (n - k) H := by
  change coeff n ((X^k * H) * C (3 : ℚ)) = 3 * coeff (n - k) H
  rw [coeff_mul_C, coeff_Xpow H k n hkn]
  ring


theorem OMA.solution : type_of% @OMA.S_oeis_a105695.main := by
  intro T G hT _hT0 hG n hn
  have h2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
    change d⁄dX ℚ ((2 : ℕ) : ℚ⟦X⟧) = 0
    exact Derivation.map_natCast _ _
  have h3 : d⁄dX ℚ (3 : ℚ⟦X⟧) = 0 := by
    change d⁄dX ℚ ((3 : ℕ) : ℚ⟦X⟧) = 0
    exact Derivation.map_natCast _ _
  have hT' : T^2 + 2 * T * (d⁄dX ℚ T) * (1 + X) = -3 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hT
    rw [(PowerSeries.derivative ℚ).leibniz, PowerSeries.derivative_pow] at h
    simp [smul_eq_mul, h3] at h
    linear_combination h
  have hG' : 2 * G + 2 * X * (d⁄dX ℚ G) =
      -2 * X * (1 - T) - (1 - X) * (1 + X) * (d⁄dX ℚ T) := by
    have h := congrArg (fun f : ℚ⟦X⟧ => d⁄dX ℚ f) hG
    repeat rw [(PowerSeries.derivative ℚ).leibniz] at h
    simp [smul_eq_mul, h2] at h
    linear_combination h
  have hXkey2 : 2 * (X * (T * G + 2 * X + G - 2)) = 0 := by
    linear_combination (X - 1) * hT + (T + 1) * hG
  have hXkey : X * (T * G + 2 * X + G - 2) = 0 := by
    have htwo : (2 : ℚ⟦X⟧) ≠ 0 := by
      intro hh
      have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) hh
      change (2 : ℚ) = 0 at hc
      norm_num at hc
    exact mul_left_cancel₀ htwo (by simpa using hXkey2)
  have hkey : T * G + 2 * X + G - 2 = 0 := by
    have hk1 : X ^ 1 * (T * G + 2 * X + G - 2) = X ^ 1 * (0 : ℚ⟦X⟧) := by
      simpa using hXkey
    exact PowerSeries.X_pow_mul_cancel hk1
  let A := algebraMap ℚ⟦X⟧ Fps
  have mT : (A T) ^ 2 * (1 + A X) = 1 - 3 * A X := by
    have h := congrArg A hT
    simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat] at h
    exact h
  have mT' : (A T)^2 + 2 * (A T) * A (d⁄dX ℚ T) * (1 + A X) = -3 := by
    have h := congrArg A hT'
    simp only [map_add, map_mul, map_pow, map_one, map_ofNat, map_neg] at h
    exact h
  have mkey : (A T)*(A G) + 2*(A X) + (A G) - 2 = 0 := by
    have h := congrArg A hkey
    simp only [map_add, map_mul, map_sub, map_ofNat, map_zero] at h
    exact h
  have mG' : 2 * A G + 2 * A X * A (d⁄dX ℚ G) =
      -2 * A X * (1 - A T) - (1 - A X) * (1 + A X) * A (d⁄dX ℚ T) := by
    have h := congrArg A hG'
    simp only [map_add, map_mul, map_neg, map_sub, map_one, map_ofNat] at h
    exact h
  have hF := ode_elim (K := Fps) (A X) (A T) (A G) (A (d⁄dX ℚ T)) (A (d⁄dX ℚ G))
    mT mT' mkey mG'
  have hinj : Function.Injective A := IsFractionRing.injective ℚ⟦X⟧ Fps
  have hODE : X * (1 - X^2) * (1 - 3 * X) * (d⁄dX ℚ G) +
      (1 - X - X^2 - 3 * X^3) * G - (1 - X) * (1 - X^2) = 0 := by
    apply hinj
    simpa [map_ofNat] using hF
  have hE : X * (d⁄dX ℚ G) - 3 * X^2 * (d⁄dX ℚ G) - X^3 * (d⁄dX ℚ G) +
      3 * X^4 * (d⁄dX ℚ G) + G - X * G - X^2 * G - 3 * X^3 * G -
      (1 - X - X^2 + X^3) = 0 := by
    linear_combination hODE
  have hC : X * (d⁄dX ℚ G) - X^2 * (d⁄dX ℚ G) * 3 - X^3 * (d⁄dX ℚ G) +
      X^4 * (d⁄dX ℚ G) * 3 + G - X * G - X^2 * G - X^3 * G * 3 -
      (1 - X - X^2 + X^3) = 0 := by
    linear_combination hE
  have hc := congrArg (fun f : ℚ⟦X⟧ => coeff n f) hC
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hn3 : n ≠ 3 := by omega
  simp only [map_sub, map_add] at hc
  rw [show X * (d⁄dX ℚ G) = X^1 * (d⁄dX ℚ G) by simp,
    show X * G = X^1 * G by simp] at hc
  rw [coeff_Xpow _ 1 n h1, coeff_Xpow_three _ 2 n h2, coeff_Xpow _ 3 n h3,
    coeff_Xpow_three _ 4 n h4, coeff_Xpow _ 1 n h1, coeff_Xpow _ 2 n h2,
    coeff_Xpow_three _ 3 n h3] at hc
  simp [coeff_derivative, coeff_X, hn0, hn1, hn2, hn3] at hc
  have e1 : n - 1 + 1 = n := by omega
  have e2 : n - 2 + 1 = n - 1 := by omega
  have e3 : n - 3 + 1 = n - 2 := by omega
  have e4 : n - 4 + 1 = n - 3 := by omega
  rw [e1, e2, e3, e4] at hc
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4] at hc
  ring_nf at hc ⊢
  linear_combination hc
