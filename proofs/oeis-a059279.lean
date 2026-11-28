import OMAStatements.S_oeis_a059279
import Mathlib

namespace OMA.S_oeis_a059279

open PowerSeries

lemma sqrt_ode (S R : PowerSeries ℚ) (h : S * S = R) :
    2 * R * derivative ℚ S = derivative ℚ R * S := by
  rw [← h, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

lemma ne_zero_of (F F0 : PowerSeries ℚ) (e : ℕ) (h : F = X ^ e * F0) (h0 : constantCoeff F0 ≠ 0) : F ≠ 0 := by
  intro hF
  rw [h] at hF
  rcases mul_eq_zero.1 hF with h1 | h1
  · exact pow_ne_zero _ PowerSeries.X_ne_zero h1
  · exact h0 (by simp [h1])

@[simp] lemma dn2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2
@[simp] lemma cc2 : constantCoeff (2 : PowerSeries ℚ) = 2 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2
lemma cm2 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2 : PowerSeries ℚ) * F) = 2 * coeff m F := by
  have e : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3
@[simp] lemma cc3 : constantCoeff (3 : PowerSeries ℚ) = 3 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3
lemma cm3 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3 : PowerSeries ℚ) * F) = 3 * coeff m F := by
  have e : (3 : PowerSeries ℚ) = C (3 : ℚ) := (map_ofNat C 3).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4 : derivative ℚ (4 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4
@[simp] lemma cc4 : constantCoeff (4 : PowerSeries ℚ) = 4 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4
lemma cm4 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4 : PowerSeries ℚ) * F) = 4 * coeff m F := by
  have e : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_ofNat C 4).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5 : derivative ℚ (5 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5
@[simp] lemma cc5 : constantCoeff (5 : PowerSeries ℚ) = 5 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5
lemma cm5 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5 : PowerSeries ℚ) * F) = 5 * coeff m F := by
  have e : (5 : PowerSeries ℚ) = C (5 : ℚ) := (map_ofNat C 5).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6 : derivative ℚ (6 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6
@[simp] lemma cc6 : constantCoeff (6 : PowerSeries ℚ) = 6 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6
lemma cm6 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6 : PowerSeries ℚ) * F) = 6 * coeff m F := by
  have e : (6 : PowerSeries ℚ) = C (6 : ℚ) := (map_ofNat C 6).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7 : derivative ℚ (7 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7
@[simp] lemma cc7 : constantCoeff (7 : PowerSeries ℚ) = 7 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7
lemma cm7 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7 : PowerSeries ℚ) * F) = 7 * coeff m F := by
  have e : (7 : PowerSeries ℚ) = C (7 : ℚ) := (map_ofNat C 7).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8 : derivative ℚ (8 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8
@[simp] lemma cc8 : constantCoeff (8 : PowerSeries ℚ) = 8 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8
lemma cm8 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8 : PowerSeries ℚ) * F) = 8 * coeff m F := by
  have e : (8 : PowerSeries ℚ) = C (8 : ℚ) := (map_ofNat C 8).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9 : derivative ℚ (9 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9
@[simp] lemma cc9 : constantCoeff (9 : PowerSeries ℚ) = 9 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9
lemma cm9 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9 : PowerSeries ℚ) * F) = 9 * coeff m F := by
  have e : (9 : PowerSeries ℚ) = C (9 : ℚ) := (map_ofNat C 9).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10 : derivative ℚ (10 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10
@[simp] lemma cc10 : constantCoeff (10 : PowerSeries ℚ) = 10 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10
lemma cm10 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10 : PowerSeries ℚ) * F) = 10 * coeff m F := by
  have e : (10 : PowerSeries ℚ) = C (10 : ℚ) := (map_ofNat C 10).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11 : derivative ℚ (11 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11
@[simp] lemma cc11 : constantCoeff (11 : PowerSeries ℚ) = 11 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11
lemma cm11 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11 : PowerSeries ℚ) * F) = 11 * coeff m F := by
  have e : (11 : PowerSeries ℚ) = C (11 : ℚ) := (map_ofNat C 11).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12 : derivative ℚ (12 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12
@[simp] lemma cc12 : constantCoeff (12 : PowerSeries ℚ) = 12 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12
lemma cm12 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12 : PowerSeries ℚ) * F) = 12 * coeff m F := by
  have e : (12 : PowerSeries ℚ) = C (12 : ℚ) := (map_ofNat C 12).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16 : derivative ℚ (16 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16
@[simp] lemma cc16 : constantCoeff (16 : PowerSeries ℚ) = 16 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16
lemma cm16 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16 : PowerSeries ℚ) * F) = 16 * coeff m F := by
  have e : (16 : PowerSeries ℚ) = C (16 : ℚ) := (map_ofNat C 16).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20 : derivative ℚ (20 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20
@[simp] lemma cc20 : constantCoeff (20 : PowerSeries ℚ) = 20 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20
lemma cm20 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20 : PowerSeries ℚ) * F) = 20 * coeff m F := by
  have e : (20 : PowerSeries ℚ) = C (20 : ℚ) := (map_ofNat C 20).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22 : derivative ℚ (22 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22
@[simp] lemma cc22 : constantCoeff (22 : PowerSeries ℚ) = 22 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22
lemma cm22 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22 : PowerSeries ℚ) * F) = 22 * coeff m F := by
  have e : (22 : PowerSeries ℚ) = C (22 : ℚ) := (map_ofNat C 22).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32 : derivative ℚ (32 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32
@[simp] lemma cc32 : constantCoeff (32 : PowerSeries ℚ) = 32 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32
lemma cm32 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32 : PowerSeries ℚ) * F) = 32 * coeff m F := by
  have e : (32 : PowerSeries ℚ) = C (32 : ℚ) := (map_ofNat C 32).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn36 : derivative ℚ (36 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36
@[simp] lemma cc36 : constantCoeff (36 : PowerSeries ℚ) = 36 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36
lemma cm36 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36 : PowerSeries ℚ) * F) = 36 * coeff m F := by
  have e : (36 : PowerSeries ℚ) = C (36 : ℚ) := (map_ofNat C 36).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn48 : derivative ℚ (48 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 48
@[simp] lemma cc48 : constantCoeff (48 : PowerSeries ℚ) = 48 := by simpa using map_natCast (constantCoeff (R := ℚ)) 48
lemma cm48 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((48 : PowerSeries ℚ) * F) = 48 * coeff m F := by
  have e : (48 : PowerSeries ℚ) = C (48 : ℚ) := (map_ofNat C 48).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn60 : derivative ℚ (60 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 60
@[simp] lemma cc60 : constantCoeff (60 : PowerSeries ℚ) = 60 := by simpa using map_natCast (constantCoeff (R := ℚ)) 60
lemma cm60 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((60 : PowerSeries ℚ) * F) = 60 * coeff m F := by
  have e : (60 : PowerSeries ℚ) = C (60 : ℚ) := (map_ofNat C 60).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn96 : derivative ℚ (96 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 96
@[simp] lemma cc96 : constantCoeff (96 : PowerSeries ℚ) = 96 := by simpa using map_natCast (constantCoeff (R := ℚ)) 96
lemma cm96 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((96 : PowerSeries ℚ) * F) = 96 * coeff m F := by
  have e : (96 : PowerSeries ℚ) = C (96 : ℚ) := (map_ofNat C 96).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn240 : derivative ℚ (240 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 240
@[simp] lemma cc240 : constantCoeff (240 : PowerSeries ℚ) = 240 := by simpa using map_natCast (constantCoeff (R := ℚ)) 240
lemma cm240 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((240 : PowerSeries ℚ) * F) = 240 * coeff m F := by
  have e : (240 : PowerSeries ℚ) = C (240 : ℚ) := (map_ofNat C 240).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn512 : derivative ℚ (512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 512
@[simp] lemma cc512 : constantCoeff (512 : PowerSeries ℚ) = 512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 512
lemma cm512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((512 : PowerSeries ℚ) * F) = 512 * coeff m F := by
  have e : (512 : PowerSeries ℚ) = C (512 : ℚ) := (map_ofNat C 512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1304 : derivative ℚ (1304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1304
@[simp] lemma cc1304 : constantCoeff (1304 : PowerSeries ℚ) = 1304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1304
lemma cm1304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1304 : PowerSeries ℚ) * F) = 1304 * coeff m F := by
  have e : (1304 : PowerSeries ℚ) = C (1304 : ℚ) := (map_ofNat C 1304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3072 : derivative ℚ (3072 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3072
@[simp] lemma cc3072 : constantCoeff (3072 : PowerSeries ℚ) = 3072 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3072
lemma cm3072 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3072 : PowerSeries ℚ) * F) = 3072 * coeff m F := by
  have e : (3072 : PowerSeries ℚ) = C (3072 : ℚ) := (map_ofNat C 3072).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4224 : derivative ℚ (4224 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4224
@[simp] lemma cc4224 : constantCoeff (4224 : PowerSeries ℚ) = 4224 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4224
lemma cm4224 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4224 : PowerSeries ℚ) * F) = 4224 * coeff m F := by
  have e : (4224 : PowerSeries ℚ) = C (4224 : ℚ) := (map_ofNat C 4224).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7680 : derivative ℚ (7680 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7680
@[simp] lemma cc7680 : constantCoeff (7680 : PowerSeries ℚ) = 7680 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7680
lemma cm7680 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7680 : PowerSeries ℚ) * F) = 7680 * coeff m F := by
  have e : (7680 : PowerSeries ℚ) = C (7680 : ℚ) := (map_ofNat C 7680).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8448 : derivative ℚ (8448 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8448
@[simp] lemma cc8448 : constantCoeff (8448 : PowerSeries ℚ) = 8448 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8448
lemma cm8448 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8448 : PowerSeries ℚ) * F) = 8448 * coeff m F := by
  have e : (8448 : PowerSeries ℚ) = C (8448 : ℚ) := (map_ofNat C 8448).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10432 : derivative ℚ (10432 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10432
@[simp] lemma cc10432 : constantCoeff (10432 : PowerSeries ℚ) = 10432 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10432
lemma cm10432 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10432 : PowerSeries ℚ) * F) = 10432 * coeff m F := by
  have e : (10432 : PowerSeries ℚ) = C (10432 : ℚ) := (map_ofNat C 10432).symm
  rw [e, coeff_C_mul]

noncomputable def R : PowerSeries ℚ := -8*X^3 + 16*X^2 - 8*X + 1
noncomputable def DD : PowerSeries ℚ := -4*X^2 + 2*X
noncomputable def NN (S : PowerSeries ℚ) : PowerSeries ℚ := (1 - 2*X) + (-1) * S

set_option maxHeartbeats 1000000 in
lemma hdD : derivative ℚ DD = 2 - 8*X := by
  simp [DD] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdR : derivative ℚ R = -24*X^2 + 32*X - 8 := by
  simp [R] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdN (S : PowerSeries ℚ) : derivative ℚ (NN S) = -2 + (0) * S + (-1) * derivative ℚ S := by
  simp [NN] <;> ring

set_option maxHeartbeats 4000000 in
lemma ode1 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((-1) * X ^ 1 + (8) * X ^ 2 + (-16) * X ^ 3 + (8) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 0 + (6) * X ^ 1 + (-12) * X ^ 2 + (4) * X ^ 3 : PowerSeries ℚ) * AA = ((-1) * X ^ 0 + (2) * X ^ 1 + (-2) * X ^ 2 : PowerSeries ℚ) := by
  have r1 := hA
  have r2 : derivative ℚ AA * DD + AA * derivative ℚ DD = derivative ℚ (NN S) := by
    have := congrArg (derivative ℚ) hA
    rw [Derivation.leibniz] at this
    simp only [smul_eq_mul] at this
    rw [← this]; ring
  have r4 := sqrt_ode S R hS
  have hK : (2 * R * DD ^ 2 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((8) * X ^ 0 + (-96) * X ^ 1 + (416) * X ^ 2 + (-832) * X ^ 3 + (768) * X ^ 4 + (-256) * X ^ 5 : PowerSeries ℚ)) 2 (by simp only [R, DD]; ring) (by simp [R, DD] <;> norm_num)
  apply mul_left_cancel₀ hK
  rw [hdD, hdN] at r2
  rw [hdR] at r4
  unfold NN at r1
  unfold DD at r1 r2
  unfold R at r4
  unfold DD R
  linear_combination (-768*X^8 + 2944*X^7 - 4352*X^6 + 3168*X^5 - 1200*X^4 + 224*X^3 - 16*X^2) * r1 + (512*X^9 - 2304*X^8 + 4096*X^7 - 3712*X^6 + 1856*X^5 - 512*X^4 + 72*X^3 - 4*X^2) * r2 + (32*X^6 - 80*X^5 + 64*X^4 - 20*X^3 + 2*X^2) * r4

set_option maxHeartbeats 1000000 in
lemma hdV : derivative ℚ ((-1) * X ^ 1 + (8) * X ^ 2 + (-16) * X ^ 3 + (8) * X ^ 4 : PowerSeries ℚ) = ((-1) * X ^ 0 + (16) * X ^ 1 + (-48) * X ^ 2 + (32) * X ^ 3 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU : derivative ℚ ((-1) * X ^ 0 + (6) * X ^ 1 + (-12) * X ^ 2 + (4) * X ^ 3 : PowerSeries ℚ) = ((6) * X ^ 0 + (-24) * X ^ 1 + (12) * X ^ 2 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW : derivative ℚ ((-1) * X ^ 0 + (2) * X ^ 1 + (-2) * X ^ 2 : PowerSeries ℚ) = ((2) * X ^ 0 + (-4) * X ^ 1 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdV1 : derivative ℚ ((-1) * X ^ 0 + (16) * X ^ 1 + (-48) * X ^ 2 + (32) * X ^ 3 : PowerSeries ℚ) = ((16) * X ^ 0 + (-96) * X ^ 1 + (96) * X ^ 2 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU1 : derivative ℚ ((6) * X ^ 0 + (-24) * X ^ 1 + (12) * X ^ 2 : PowerSeries ℚ) = ((-24) * X ^ 0 + (24) * X ^ 1 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW1 : derivative ℚ ((2) * X ^ 0 + (-4) * X ^ 1 : PowerSeries ℚ) = ((-4) * X ^ 0 : PowerSeries ℚ) := by
  simp <;> ring

lemma dmul (F G : PowerSeries ℚ) : derivative ℚ (F * G) = F * derivative ℚ G + G * derivative ℚ F := by
  rw [Derivation.leibniz]; simp only [smul_eq_mul]

set_option maxHeartbeats 4000000 in
lemma ode2 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((-1) * X ^ 0 + (16) * X ^ 1 + (-48) * X ^ 2 + (32) * X ^ 3 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 1 + (8) * X ^ 2 + (-16) * X ^ 3 + (8) * X ^ 4 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((6) * X ^ 0 + (-24) * X ^ 1 + (12) * X ^ 2 : PowerSeries ℚ) * AA + ((-1) * X ^ 0 + (6) * X ^ 1 + (-12) * X ^ 2 + (4) * X ^ 3 : PowerSeries ℚ) * derivative ℚ AA = ((2) * X ^ 0 + (-4) * X ^ 1 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode1 S AA hS hA)
  rw [map_add, dmul, dmul, hdV, hdU, hdW] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3' (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((16) * X ^ 0 + (-96) * X ^ 1 + (96) * X ^ 2 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 0 + (16) * X ^ 1 + (-48) * X ^ 2 + (32) * X ^ 3 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + (((-1) * X ^ 0 + (16) * X ^ 1 + (-48) * X ^ 2 + (32) * X ^ 3 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-1) * X ^ 1 + (8) * X ^ 2 + (-16) * X ^ 3 + (8) * X ^ 4 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA))) + (((-24) * X ^ 0 + (24) * X ^ 1 : PowerSeries ℚ) * AA + ((6) * X ^ 0 + (-24) * X ^ 1 + (12) * X ^ 2 : PowerSeries ℚ) * derivative ℚ AA) + (((6) * X ^ 0 + (-24) * X ^ 1 + (12) * X ^ 2 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 0 + (6) * X ^ 1 + (-12) * X ^ 2 + (4) * X ^ 3 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA)) = ((-4) * X ^ 0 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode2 S AA hS hA)
  rw [map_add, map_add, map_add, dmul, dmul, dmul, dmul, hdV1, hdV, hdU1, hdU, hdW1] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((1) * X ^ 0 + (-6) * X ^ 1 + (12) * X ^ 2 + (-4) * X ^ 3 : PowerSeries ℚ) * AA + ((1) * X ^ 1 + (-8) * X ^ 2 + (16) * X ^ 3 + (-8) * X ^ 4 : PowerSeries ℚ) * derivative ℚ AA = ((1) * X ^ 0 + (-2) * X ^ 1 + (2) * X ^ 2 : PowerSeries ℚ) := by
  have e1 := ode1 S AA hS hA
  have e2 := ode2 S AA hS hA
  have e3 := ode3' S AA hS hA
  have hK : (((-1) * X ^ 1 + (8) * X ^ 2 + (-16) * X ^ 3 + (8) * X ^ 4 : PowerSeries ℚ) ^ 3 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((-1) * X ^ 0 + (24) * X ^ 1 + (-240) * X ^ 2 + (1304) * X ^ 3 + (-4224) * X ^ 4 + (8448) * X ^ 5 + (-10432) * X ^ 6 + (7680) * X ^ 7 + (-3072) * X ^ 8 + (512) * X ^ 9 : PowerSeries ℚ)) 3 (by ring) (by simp <;> norm_num)
  apply mul_left_cancel₀ hK
  linear_combination (((0) * X ^ 0 : PowerSeries ℚ)) * e3 + (((0) * X ^ 0 : PowerSeries ℚ)) * e2 + (((1) * X ^ 3 + (-24) * X ^ 4 + (240) * X ^ 5 + (-1304) * X ^ 6 + (4224) * X ^ 7 + (-8448) * X ^ 8 + (10432) * X ^ 9 + (-7680) * X ^ 10 + (3072) * X ^ 11 + (-512) * X ^ 12 : PowerSeries ℚ)) * e1

set_option maxHeartbeats 4000000 in
lemma rec_a (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) (k : ℕ) : (((k + 3 : ℕ) : ℚ) + 1) * coeff (k + 3) AA + (2 - 8*((k + 3 : ℕ) : ℚ)) * coeff (k + 2) AA + (16*((k + 3 : ℕ) : ℚ) - 20) * coeff (k + 1) AA + (20 - 8*((k + 3 : ℕ) : ℚ)) * coeff (k + 0) AA = 0 := by
  have h := congrArg (coeff (k + 3)) (ode3 S AA hS hA)
  rcases k with _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm16, cm20, cm22, cm24, cm32, cm36, cm48, cm60, cm96, cm240, cm512, cm1304, cm3072, cm4224, cm7680, cm8448, cm10432, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h


end OMA.S_oeis_a059279

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a059279.main := by
  intro T G hT h0 hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hS : ((1 - 2 * X) * T) * ((1 - 2 * X) * T) = OMA.S_oeis_a059279.R := by
    unfold OMA.S_oeis_a059279.R; linear_combination (1 - 2 * X) * hT
  have hA : G * OMA.S_oeis_a059279.DD = OMA.S_oeis_a059279.NN ((1 - 2 * X) * T) := by
    unfold OMA.S_oeis_a059279.DD OMA.S_oeis_a059279.NN
    linear_combination (1 * (1 - 2 * X)) * hG
  have h := OMA.S_oeis_a059279.rec_a _ G hS hA k
  simp only [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k + 0 from by omega]
  push_cast at h ⊢
  linear_combination h
