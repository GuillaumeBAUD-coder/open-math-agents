import OMAStatements.S_oeis_a228770
import Mathlib

namespace OMA.P228770

open PowerSeries OMA.S_oeis_a228770

lemma hR0 : constantCoeff (R - 1) = 0 := by
  simp [R]

lemma hsub : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' hR0

lemma hone : (1 : PowerSeries ℚ).subst (R - 1) = 1 := by
  rw [← coe_substAlgHom hsub]
  exact map_one _

lemma hS : S ^ 2 = R := by
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [pow_two, ← PowerSeries.binomialSeries_add]
    have h := PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1
    norm_num at h ⊢
    exact h
  unfold S
  rw [← subst_pow hsub, h2, subst_add hsub, subst_X hsub, hone]
  ring

lemma hS0 : constantCoeff S = 1 := by
  have e : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = 1 + (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) := by ring
  have hz : constantCoeff ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1)) = 0 :=
    constantCoeff_subst_eq_zero hR0 _ (by simp)
  unfold S
  rw [e, subst_add hsub, hone, map_add, hz]
  simp

/-- The first-order differential equation satisfied by a series of the form (P + Q sqrt(Δ)) / D. -/
lemma ode (S Δ D P Q G : PowerSeries ℚ) (hS : S ^ 2 = Δ) (hG : D * G = P + Q * S) :
    2 * Δ * Q * D * derivative ℚ G
      + (2 * Δ * Q * derivative ℚ D - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * D) * G
    = 2 * Δ * Q * derivative ℚ P - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * P := by
  have hS' := congrArg (derivative ℚ) hS
  have hG' := congrArg (derivative ℚ) hG
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hS' hG'
  push_cast at hS' hG'
  linear_combination (2 * Δ * Q) * hG' - (2 * Δ * derivative ℚ Q + Q * derivative ℚ Δ) * hG
    + (Q ^ 2 * S) * hS' - (2 * Q ^ 2 * derivative ℚ S) * hS

lemma dOfNat (m : ℕ) [m.AtLeastTwo] : derivative ℚ (ofNat(m) : PowerSeries ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := PowerSeries ℚ)]
  exact Derivation.map_natCast _ _

noncomputable def G : PowerSeries ℚ := PowerSeries.mk a

/-- The series whose coefficients define the sequence. -/
noncomputable def F : PowerSeries ℚ := ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S) * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹

lemma hD0 : constantCoeff (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X, hS0]
  norm_num

lemma hF : (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3) * F = (-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S := by
  unfold F
  rw [mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ hD0, mul_one]

lemma a_eq (j : ℕ) : a j = coeff (j + 1) F := by
  unfold a F
  congr 1
  try ring


lemma hconj : constantCoeff ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) - (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S : PowerSeries ℚ) ≠ 0 := by
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X, hS0]
  norm_num

lemma hFX : F = X ^ 1 * ((-4 * X + 52 * X ^ 2 - 260 * X ^ 3 + 632 * X ^ 4 - 800 * X ^ 5 + 572 * X ^ 6 - 240 * X ^ 7 + 64 * X ^ 8) * ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) - (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S : PowerSeries ℚ)⁻¹ * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹) := by
  have h1 := PowerSeries.mul_inv_cancel _ hconj
  have h2 := hS
  unfold F
  unfold R at h2
  have key : ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S) = X ^ 1 * ((-4 * X + 52 * X ^ 2 - 260 * X ^ 3 + 632 * X ^ 4 - 800 * X ^ 5 + 572 * X ^ 6 - 240 * X ^ 7 + 64 * X ^ 8) * ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) - (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S : PowerSeries ℚ)⁻¹) := by
    linear_combination (-((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S)) * h1
      + (-((1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) ^ 2) * ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) - (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S : PowerSeries ℚ)⁻¹) * h2
  rw [key]
  ring

lemma hGF : X ^ 1 * G = F := by
  ext j
  rw [hFX, coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hj : 1 ≤ j
  · rw [if_pos hj, if_pos hj, G, coeff_mk, a_eq, hFX]
    have e : j - 1 + 1 = j := by omega
    rw [e, coeff_X_pow_mul', if_pos hj]
  · rw [if_neg hj, if_neg hj]

lemma hG : X ^ 1 * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3) * G = (-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S := by
  have e : X ^ 1 * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3) * G = (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3) * (X ^ 1 * G) := by ring
  rw [e, hGF]
  exact hF

lemma dP : derivative ℚ (-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3 : PowerSeries ℚ) = 8 - 36 * X + 27 * X ^ 2 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dQ : derivative ℚ (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ) = -6 + 20 * X - 21 * X ^ 2 + 16 * X ^ 3 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dDl : derivative ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring

lemma dD : derivative ℚ (X ^ 1 * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3) : PowerSeries ℚ) = 2 - 24 * X + 54 * X ^ 2 - 32 * X ^ 3 := by
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero]
  try push_cast
  try ring


lemma hE0 : (4 * X - 64 * X ^ 2 + 412 * X ^ 3 - 1380 * X ^ 4 + 2640 * X ^ 5 - 3068 * X ^ 6 + 2288 * X ^ 7 - 1088 * X ^ 8 + 256 * X ^ 9) * derivative ℚ G + (4 - 56 * X + 308 * X ^ 2 - 848 * X ^ 3 + 1192 * X ^ 4 - 576 * X ^ 5 - 536 * X ^ 6 + 640 * X ^ 7 - 128 * X ^ 8) * G = 8 * X - 108 * X ^ 2 + 584 * X ^ 3 - 1600 * X ^ 4 + 2336 * X ^ 5 - 1764 * X ^ 6 + 432 * X ^ 7 := by
  have h := ode S R (X ^ 1 * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3)) (-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3) (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) G hS hG
  rw [dP, dQ, dD] at h
  unfold R at h
  rw [dDl] at h
  linear_combination h

lemma hE1 : (4 * X - 64 * X ^ 2 + 412 * X ^ 3 - 1380 * X ^ 4 + 2640 * X ^ 5 - 3068 * X ^ 6 + 2288 * X ^ 7 - 1088 * X ^ 8 + 256 * X ^ 9) * derivative ℚ (derivative ℚ G) + (8 - 184 * X + 1544 * X ^ 2 - 6368 * X ^ 3 + 14392 * X ^ 4 - 18984 * X ^ 5 + 15480 * X ^ 6 - 8064 * X ^ 7 + 2176 * X ^ 8) * derivative ℚ G + (-56 + 616 * X - 2544 * X ^ 2 + 4768 * X ^ 3 - 2880 * X ^ 4 - 3216 * X ^ 5 + 4480 * X ^ 6 - 1024 * X ^ 7) * G
    = 8 - 216 * X + 1752 * X ^ 2 - 6400 * X ^ 3 + 11680 * X ^ 4 - 10584 * X ^ 5 + 3024 * X ^ 6 := by
  have h := congrArg (derivative ℚ) hE0
  simp only [map_add, map_sub, map_neg, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, smul_eq_mul, nsmul_eq_mul, dOfNat, Derivation.map_one_eq_zero] at h
  push_cast at h
  linear_combination h


lemma hu : (4 - 64 * X + 412 * X ^ 2 - 1380 * X ^ 3 + 2640 * X ^ 4 - 3068 * X ^ 5 + 2288 * X ^ 6 - 1088 * X ^ 7 + 256 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h' := congrArg constantCoeff h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero,
    constantCoeff_X] at h'
  norm_num at h'

lemma hT : (-39961 * X ^ 2 - 39961 * X ^ 3 + 4382433 * X ^ 4 - 25961763 * X ^ 5 + 60022852 * X ^ 6 - 59250576 * X ^ 7 + 20886976 * X ^ 8) * derivative ℚ (derivative ℚ G) + (2394676 * X - 26095084 * X ^ 2 + 104199480 * X ^ 3 - 195982428 * X ^ 4 + 210280636 * X ^ 5 - 163037088 * X ^ 6 + 68239808 * X ^ 7) * derivative ℚ G + (2474598 - 21065966 * X + 58171956 * X ^ 2 - 53323956 * X ^ 3 - 26955412 * X ^ 4 + 84463212 * X ^ 5 - 28898160 * X ^ 6) * G - (4869274 * X - 39977022 * X ^ 2 + 117291960 * X ^ 3 - 133858314 * X ^ 4 + 62284518 * X ^ 5) = 0 := by
  have hc : (X ^ 1 * (4 - 64 * X + 412 * X ^ 2 - 1380 * X ^ 3 + 2640 * X ^ 4 - 3068 * X ^ 5 + 2288 * X ^ 6 - 1088 * X ^ 7 + 256 * X ^ 8) : PowerSeries ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hu
  have hm : (X ^ 1 * (4 - 64 * X + 412 * X ^ 2 - 1380 * X ^ 3 + 2640 * X ^ 4 - 3068 * X ^ 5 + 2288 * X ^ 6 - 1088 * X ^ 7 + 256 * X ^ 8)) ^ 2 * ((-39961 * X ^ 2 - 39961 * X ^ 3 + 4382433 * X ^ 4 - 25961763 * X ^ 5 + 60022852 * X ^ 6 - 59250576 * X ^ 7 + 20886976 * X ^ 8) * derivative ℚ (derivative ℚ G) + (2394676 * X - 26095084 * X ^ 2 + 104199480 * X ^ 3 - 195982428 * X ^ 4 + 210280636 * X ^ 5 - 163037088 * X ^ 6 + 68239808 * X ^ 7) * derivative ℚ G + (2474598 - 21065966 * X + 58171956 * X ^ 2 - 53323956 * X ^ 3 - 26955412 * X ^ 4 + 84463212 * X ^ 5 - 28898160 * X ^ 6) * G - (4869274 * X - 39977022 * X ^ 2 + 117291960 * X ^ 3 - 133858314 * X ^ 4 + 62284518 * X ^ 5)) = 0 := by
    linear_combination (9898392 * X ^ 2 - 264672736 * X ^ 3 + 3092777304 * X ^ 4 - 20687234008 * X ^ 5 + 86944367560 * X ^ 6 - 235561035640 * X ^ 7 + 396143077992 * X ^ 8 - 326428713480 * X ^ 9 - 157405657728 * X ^ 10 + 824344351800 * X ^ 11 - 1172086950560 * X ^ 12 + 992888921856 * X ^ 13 - 544387884032 * X ^ 14 + 181379422208 * X ^ 15 - 27980668928 * X ^ 16) * hE0 + (-159844 * X ^ 3 + 2397660 * X ^ 4 + 3623304 * X ^ 5 - 345640516 * X ^ 6 + 3656855776 * X ^ 7 - 20805365420 * X ^ 8 + 76033025432 * X ^ 9 - 190611851500 * X ^ 10 + 338542501412 * X ^ 11 - 433574488320 * X ^ 12 + 403622970176 * X ^ 13 - 271597634560 * X ^ 14 + 127619877888 * X ^ 15 - 37893177344 * X ^ 16 + 5347065856 * X ^ 17) * hE1
  exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hc)

/-- Iterated derivative. -/
noncomputable def dn : ℕ → PowerSeries ℚ → PowerSeries ℚ
  | 0, f => f
  | (j + 1), f => dn j (derivative ℚ f)

lemma coeff_dn (j : ℕ) : ∀ (m : ℕ) (f : PowerSeries ℚ),
    coeff m (dn j f) = coeff (m + j) f * ((m + j).descFactorial j : ℚ) := by
  induction j with
  | zero =>
    intro m f
    simp [dn]
  | succ j ih =>
    intro m f
    rw [dn, ih, coeff_derivative, show m + (j + 1) = m + j + 1 from rfl, Nat.succ_descFactorial_succ]
    push_cast
    ring

lemma coeff_term (b : ℕ → ℚ) (i j e t : ℕ) (he : e = i + j) (hi : i ≤ t) :
    coeff t (X ^ e * dn j (PowerSeries.mk b)) = b (t - i) * ((t - i).descFactorial j : ℚ) := by
  subst he
  rw [coeff_X_pow_mul']
  by_cases h : i + j ≤ t
  · rw [if_pos h, coeff_dn, coeff_mk]
    have e1 : t - (i + j) + j = t - i := by omega
    rw [e1]
  · rw [if_neg h]
    have hz : (t - i).descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz]
    simp

lemma df1 (t : ℕ) : (t.descFactorial 1 : ℚ) = t := by
  simp

lemma df2 (t : ℕ) : (t.descFactorial 2 : ℚ) = t * ((t : ℚ) - 1) := by
  rcases t with _ | t
  · simp
  · rw [Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    push_cast
    ring

lemma df3 (t : ℕ) : (t.descFactorial 3 : ℚ) = t * ((t : ℚ) - 1) * ((t : ℚ) - 2) := by
  rcases t with _ | _ | t
  · simp
  · simp [Nat.descFactorial]
  · rw [Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ, Nat.descFactorial_one]
    push_cast
    ring

lemma dn0 : dn 0 (PowerSeries.mk a) = G := rfl

lemma dn1 : dn 1 (PowerSeries.mk a) = derivative ℚ G := rfl

lemma dn2 : dn 2 (PowerSeries.mk a) = derivative ℚ (derivative ℚ G) := rfl

lemma dn3 : dn 3 (PowerSeries.mk a) = derivative ℚ (derivative ℚ (derivative ℚ G)) := rfl


lemma hTC : C (-39961 : ℚ) * (X ^ 2 * dn 2 (PowerSeries.mk a))
      + C (-39961 : ℚ) * (X ^ 3 * dn 2 (PowerSeries.mk a))
      + C (4382433 : ℚ) * (X ^ 4 * dn 2 (PowerSeries.mk a))
      + C (-25961763 : ℚ) * (X ^ 5 * dn 2 (PowerSeries.mk a))
      + C (60022852 : ℚ) * (X ^ 6 * dn 2 (PowerSeries.mk a))
      + C (-59250576 : ℚ) * (X ^ 7 * dn 2 (PowerSeries.mk a))
      + C (20886976 : ℚ) * (X ^ 8 * dn 2 (PowerSeries.mk a))
      + C (2394676 : ℚ) * (X ^ 1 * dn 1 (PowerSeries.mk a))
      + C (-26095084 : ℚ) * (X ^ 2 * dn 1 (PowerSeries.mk a))
      + C (104199480 : ℚ) * (X ^ 3 * dn 1 (PowerSeries.mk a))
      + C (-195982428 : ℚ) * (X ^ 4 * dn 1 (PowerSeries.mk a))
      + C (210280636 : ℚ) * (X ^ 5 * dn 1 (PowerSeries.mk a))
      + C (-163037088 : ℚ) * (X ^ 6 * dn 1 (PowerSeries.mk a))
      + C (68239808 : ℚ) * (X ^ 7 * dn 1 (PowerSeries.mk a))
      + C (2474598 : ℚ) * (X ^ 0 * dn 0 (PowerSeries.mk a))
      + C (-21065966 : ℚ) * (X ^ 1 * dn 0 (PowerSeries.mk a))
      + C (58171956 : ℚ) * (X ^ 2 * dn 0 (PowerSeries.mk a))
      + C (-53323956 : ℚ) * (X ^ 3 * dn 0 (PowerSeries.mk a))
      + C (-26955412 : ℚ) * (X ^ 4 * dn 0 (PowerSeries.mk a))
      + C (84463212 : ℚ) * (X ^ 5 * dn 0 (PowerSeries.mk a))
      + C (-28898160 : ℚ) * (X ^ 6 * dn 0 (PowerSeries.mk a))
      - (C (4869274 : ℚ) * X ^ 1 + C (-39977022 : ℚ) * X ^ 2 + C (117291960 : ℚ) * X ^ 3
        + C (-133858314 : ℚ) * X ^ 4 + C (62284518 : ℚ) * X ^ 5) = 0 := by
  have h := hT
  simp only [dn0, dn1, dn2, dn3]
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h


lemma hrec (N : ℕ) :
    (-39961 * ((N : ℚ) + 7) ^ 2 + 2434637 * ((N : ℚ) + 7) + 2474598) * a (N + 7)
      + (-39961 * ((N : ℚ) + 7) ^ 2 - 25975201 * ((N : ℚ) + 7) + 4949196) * a (N + 6)
      + (4382433 * ((N : ℚ) + 7) ^ 2 + 82287315 * ((N : ℚ) + 7) - 123932406) * a (N + 5)
      + (-25961763 * ((N : ℚ) + 7) ^ 2 - 14250087 * ((N : ℚ) + 7) + 223082172) * a (N + 4)
      + (60022852 * ((N : ℚ) + 7) ^ 2 - 329925032 * ((N : ℚ) + 7) + 332379084) * a (N + 3)
      + (-59250576 * ((N : ℚ) + 7) ^ 2 + 488719248 * ((N : ℚ) + 7) - 877868628) * a (N + 2)
      + (20886976 * ((N : ℚ) + 7) ^ 2 - 203290880 * ((N : ℚ) + 7) + 438915984) * a (N + 1) = 0 := by
  have h := congrArg (coeff (N + 7)) hTC
  have e0_2 := coeff_term a 0 2 2 (N + 7) rfl (by omega)
  have e1_2 := coeff_term a 1 2 3 (N + 7) rfl (by omega)
  have e2_2 := coeff_term a 2 2 4 (N + 7) rfl (by omega)
  have e3_2 := coeff_term a 3 2 5 (N + 7) rfl (by omega)
  have e4_2 := coeff_term a 4 2 6 (N + 7) rfl (by omega)
  have e5_2 := coeff_term a 5 2 7 (N + 7) rfl (by omega)
  have e6_2 := coeff_term a 6 2 8 (N + 7) rfl (by omega)
  have e0_1 := coeff_term a 0 1 1 (N + 7) rfl (by omega)
  have e1_1 := coeff_term a 1 1 2 (N + 7) rfl (by omega)
  have e2_1 := coeff_term a 2 1 3 (N + 7) rfl (by omega)
  have e3_1 := coeff_term a 3 1 4 (N + 7) rfl (by omega)
  have e4_1 := coeff_term a 4 1 5 (N + 7) rfl (by omega)
  have e5_1 := coeff_term a 5 1 6 (N + 7) rfl (by omega)
  have e6_1 := coeff_term a 6 1 7 (N + 7) rfl (by omega)
  have e0_0 := coeff_term a 0 0 0 (N + 7) rfl (by omega)
  have e1_0 := coeff_term a 1 0 1 (N + 7) rfl (by omega)
  have e2_0 := coeff_term a 2 0 2 (N + 7) rfl (by omega)
  have e3_0 := coeff_term a 3 0 3 (N + 7) rfl (by omega)
  have e4_0 := coeff_term a 4 0 4 (N + 7) rfl (by omega)
  have e5_0 := coeff_term a 5 0 5 (N + 7) rfl (by omega)
  have e6_0 := coeff_term a 6 0 6 (N + 7) rfl (by omega)
  have s1 : coeff (N + 7) (X ^ 1 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s2 : coeff (N + 7) (X ^ 2 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s3 : coeff (N + 7) (X ^ 3 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s4 : coeff (N + 7) (X ^ 4 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have s5 : coeff (N + 7) (X ^ 5 : PowerSeries ℚ) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have t1 : N + 7 - 1 = N + 6 := by omega
  have t2 : N + 7 - 2 = N + 5 := by omega
  have t3 : N + 7 - 3 = N + 4 := by omega
  have t4 : N + 7 - 4 = N + 3 := by omega
  have t5 : N + 7 - 5 = N + 2 := by omega
  have t6 : N + 7 - 6 = N + 1 := by omega
  simp only [LinearMap.map_add, LinearMap.map_sub, coeff_C_mul, e0_2, e1_2, e2_2, e3_2, e4_2, e5_2, e6_2, e0_1, e1_1, e2_1, e3_1, e4_1, e5_1, e6_1, e0_0, e1_0, e2_0, e3_0, e4_0, e5_0, e6_0, s1, s2, s3, s4, s5, LinearMap.map_zero,
    mul_zero, sub_zero, add_zero] at h
  simp only [t1, t2, t3, t4, t5, t6, Nat.sub_zero, df1, df2, df3, Nat.descFactorial_zero, Nat.cast_one,
    mul_one] at h
  push_cast at h
  linear_combination h

end OMA.P228770

theorem OMA.solution : type_of% @OMA.S_oeis_a228770.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 7 := ⟨n - 7, by omega⟩
  have h := OMA.P228770.hrec N
  have t1 : N + 7 - 1 = N + 6 := by omega
  have t2 : N + 7 - 2 = N + 5 := by omega
  have t3 : N + 7 - 3 = N + 4 := by omega
  have t4 : N + 7 - 4 = N + 3 := by omega
  have t5 : N + 7 - 5 = N + 2 := by omega
  have t6 : N + 7 - 6 = N + 1 := by omega
  simp only [t1, t2, t3, t4, t5, t6]
  push_cast
  linear_combination h
