import OMAStatements.S_oeis_a171854
import Mathlib

namespace OMA.S_oeis_a171854

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
@[simp] lemma dn13 : derivative ℚ (13 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13
@[simp] lemma cc13 : constantCoeff (13 : PowerSeries ℚ) = 13 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13
lemma cm13 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13 : PowerSeries ℚ) * F) = 13 * coeff m F := by
  have e : (13 : PowerSeries ℚ) = C (13 : ℚ) := (map_ofNat C 13).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14 : derivative ℚ (14 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14
@[simp] lemma cc14 : constantCoeff (14 : PowerSeries ℚ) = 14 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14
lemma cm14 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14 : PowerSeries ℚ) * F) = 14 * coeff m F := by
  have e : (14 : PowerSeries ℚ) = C (14 : ℚ) := (map_ofNat C 14).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15 : derivative ℚ (15 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15
@[simp] lemma cc15 : constantCoeff (15 : PowerSeries ℚ) = 15 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15
lemma cm15 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15 : PowerSeries ℚ) * F) = 15 * coeff m F := by
  have e : (15 : PowerSeries ℚ) = C (15 : ℚ) := (map_ofNat C 15).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16 : derivative ℚ (16 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16
@[simp] lemma cc16 : constantCoeff (16 : PowerSeries ℚ) = 16 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16
lemma cm16 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16 : PowerSeries ℚ) * F) = 16 * coeff m F := by
  have e : (16 : PowerSeries ℚ) = C (16 : ℚ) := (map_ofNat C 16).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17 : derivative ℚ (17 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17
@[simp] lemma cc17 : constantCoeff (17 : PowerSeries ℚ) = 17 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17
lemma cm17 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17 : PowerSeries ℚ) * F) = 17 * coeff m F := by
  have e : (17 : PowerSeries ℚ) = C (17 : ℚ) := (map_ofNat C 17).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18 : derivative ℚ (18 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18
@[simp] lemma cc18 : constantCoeff (18 : PowerSeries ℚ) = 18 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18
lemma cm18 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18 : PowerSeries ℚ) * F) = 18 * coeff m F := by
  have e : (18 : PowerSeries ℚ) = C (18 : ℚ) := (map_ofNat C 18).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19 : derivative ℚ (19 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19
@[simp] lemma cc19 : constantCoeff (19 : PowerSeries ℚ) = 19 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19
lemma cm19 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19 : PowerSeries ℚ) * F) = 19 * coeff m F := by
  have e : (19 : PowerSeries ℚ) = C (19 : ℚ) := (map_ofNat C 19).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20 : derivative ℚ (20 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20
@[simp] lemma cc20 : constantCoeff (20 : PowerSeries ℚ) = 20 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20
lemma cm20 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20 : PowerSeries ℚ) * F) = 20 * coeff m F := by
  have e : (20 : PowerSeries ℚ) = C (20 : ℚ) := (map_ofNat C 20).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn21 : derivative ℚ (21 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 21
@[simp] lemma cc21 : constantCoeff (21 : PowerSeries ℚ) = 21 := by simpa using map_natCast (constantCoeff (R := ℚ)) 21
lemma cm21 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((21 : PowerSeries ℚ) * F) = 21 * coeff m F := by
  have e : (21 : PowerSeries ℚ) = C (21 : ℚ) := (map_ofNat C 21).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22 : derivative ℚ (22 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22
@[simp] lemma cc22 : constantCoeff (22 : PowerSeries ℚ) = 22 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22
lemma cm22 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22 : PowerSeries ℚ) * F) = 22 * coeff m F := by
  have e : (22 : PowerSeries ℚ) = C (22 : ℚ) := (map_ofNat C 22).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn23 : derivative ℚ (23 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 23
@[simp] lemma cc23 : constantCoeff (23 : PowerSeries ℚ) = 23 := by simpa using map_natCast (constantCoeff (R := ℚ)) 23
lemma cm23 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((23 : PowerSeries ℚ) * F) = 23 * coeff m F := by
  have e : (23 : PowerSeries ℚ) = C (23 : ℚ) := (map_ofNat C 23).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25 : derivative ℚ (25 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25
@[simp] lemma cc25 : constantCoeff (25 : PowerSeries ℚ) = 25 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25
lemma cm25 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25 : PowerSeries ℚ) * F) = 25 * coeff m F := by
  have e : (25 : PowerSeries ℚ) = C (25 : ℚ) := (map_ofNat C 25).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn26 : derivative ℚ (26 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 26
@[simp] lemma cc26 : constantCoeff (26 : PowerSeries ℚ) = 26 := by simpa using map_natCast (constantCoeff (R := ℚ)) 26
lemma cm26 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((26 : PowerSeries ℚ) * F) = 26 * coeff m F := by
  have e : (26 : PowerSeries ℚ) = C (26 : ℚ) := (map_ofNat C 26).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27 : derivative ℚ (27 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27
@[simp] lemma cc27 : constantCoeff (27 : PowerSeries ℚ) = 27 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27
lemma cm27 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27 : PowerSeries ℚ) * F) = 27 * coeff m F := by
  have e : (27 : PowerSeries ℚ) = C (27 : ℚ) := (map_ofNat C 27).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn28 : derivative ℚ (28 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 28
@[simp] lemma cc28 : constantCoeff (28 : PowerSeries ℚ) = 28 := by simpa using map_natCast (constantCoeff (R := ℚ)) 28
lemma cm28 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((28 : PowerSeries ℚ) * F) = 28 * coeff m F := by
  have e : (28 : PowerSeries ℚ) = C (28 : ℚ) := (map_ofNat C 28).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30 : derivative ℚ (30 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30
@[simp] lemma cc30 : constantCoeff (30 : PowerSeries ℚ) = 30 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30
lemma cm30 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30 : PowerSeries ℚ) * F) = 30 * coeff m F := by
  have e : (30 : PowerSeries ℚ) = C (30 : ℚ) := (map_ofNat C 30).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn33 : derivative ℚ (33 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 33
@[simp] lemma cc33 : constantCoeff (33 : PowerSeries ℚ) = 33 := by simpa using map_natCast (constantCoeff (R := ℚ)) 33
lemma cm33 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((33 : PowerSeries ℚ) * F) = 33 * coeff m F := by
  have e : (33 : PowerSeries ℚ) = C (33 : ℚ) := (map_ofNat C 33).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn35 : derivative ℚ (35 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 35
@[simp] lemma cc35 : constantCoeff (35 : PowerSeries ℚ) = 35 := by simpa using map_natCast (constantCoeff (R := ℚ)) 35
lemma cm35 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((35 : PowerSeries ℚ) * F) = 35 * coeff m F := by
  have e : (35 : PowerSeries ℚ) = C (35 : ℚ) := (map_ofNat C 35).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn36 : derivative ℚ (36 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36
@[simp] lemma cc36 : constantCoeff (36 : PowerSeries ℚ) = 36 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36
lemma cm36 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36 : PowerSeries ℚ) * F) = 36 * coeff m F := by
  have e : (36 : PowerSeries ℚ) = C (36 : ℚ) := (map_ofNat C 36).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn49 : derivative ℚ (49 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 49
@[simp] lemma cc49 : constantCoeff (49 : PowerSeries ℚ) = 49 := by simpa using map_natCast (constantCoeff (R := ℚ)) 49
lemma cm49 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((49 : PowerSeries ℚ) * F) = 49 * coeff m F := by
  have e : (49 : PowerSeries ℚ) = C (49 : ℚ) := (map_ofNat C 49).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn55 : derivative ℚ (55 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 55
@[simp] lemma cc55 : constantCoeff (55 : PowerSeries ℚ) = 55 := by simpa using map_natCast (constantCoeff (R := ℚ)) 55
lemma cm55 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((55 : PowerSeries ℚ) * F) = 55 * coeff m F := by
  have e : (55 : PowerSeries ℚ) = C (55 : ℚ) := (map_ofNat C 55).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn56 : derivative ℚ (56 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 56
@[simp] lemma cc56 : constantCoeff (56 : PowerSeries ℚ) = 56 := by simpa using map_natCast (constantCoeff (R := ℚ)) 56
lemma cm56 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((56 : PowerSeries ℚ) * F) = 56 * coeff m F := by
  have e : (56 : PowerSeries ℚ) = C (56 : ℚ) := (map_ofNat C 56).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn60 : derivative ℚ (60 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 60
@[simp] lemma cc60 : constantCoeff (60 : PowerSeries ℚ) = 60 := by simpa using map_natCast (constantCoeff (R := ℚ)) 60
lemma cm60 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((60 : PowerSeries ℚ) * F) = 60 * coeff m F := by
  have e : (60 : PowerSeries ℚ) = C (60 : ℚ) := (map_ofNat C 60).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn64 : derivative ℚ (64 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 64
@[simp] lemma cc64 : constantCoeff (64 : PowerSeries ℚ) = 64 := by simpa using map_natCast (constantCoeff (R := ℚ)) 64
lemma cm64 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((64 : PowerSeries ℚ) * F) = 64 * coeff m F := by
  have e : (64 : PowerSeries ℚ) = C (64 : ℚ) := (map_ofNat C 64).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn72 : derivative ℚ (72 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72
@[simp] lemma cc72 : constantCoeff (72 : PowerSeries ℚ) = 72 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72
lemma cm72 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72 : PowerSeries ℚ) * F) = 72 * coeff m F := by
  have e : (72 : PowerSeries ℚ) = C (72 : ℚ) := (map_ofNat C 72).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80 : derivative ℚ (80 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80
@[simp] lemma cc80 : constantCoeff (80 : PowerSeries ℚ) = 80 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80
lemma cm80 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80 : PowerSeries ℚ) * F) = 80 * coeff m F := by
  have e : (80 : PowerSeries ℚ) = C (80 : ℚ) := (map_ofNat C 80).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn90 : derivative ℚ (90 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 90
@[simp] lemma cc90 : constantCoeff (90 : PowerSeries ℚ) = 90 := by simpa using map_natCast (constantCoeff (R := ℚ)) 90
lemma cm90 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((90 : PowerSeries ℚ) * F) = 90 * coeff m F := by
  have e : (90 : PowerSeries ℚ) = C (90 : ℚ) := (map_ofNat C 90).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn120 : derivative ℚ (120 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 120
@[simp] lemma cc120 : constantCoeff (120 : PowerSeries ℚ) = 120 := by simpa using map_natCast (constantCoeff (R := ℚ)) 120
lemma cm120 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((120 : PowerSeries ℚ) * F) = 120 * coeff m F := by
  have e : (120 : PowerSeries ℚ) = C (120 : ℚ) := (map_ofNat C 120).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn126 : derivative ℚ (126 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 126
@[simp] lemma cc126 : constantCoeff (126 : PowerSeries ℚ) = 126 := by simpa using map_natCast (constantCoeff (R := ℚ)) 126
lemma cm126 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((126 : PowerSeries ℚ) * F) = 126 * coeff m F := by
  have e : (126 : PowerSeries ℚ) = C (126 : ℚ) := (map_ofNat C 126).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn144 : derivative ℚ (144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 144
@[simp] lemma cc144 : constantCoeff (144 : PowerSeries ℚ) = 144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 144
lemma cm144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((144 : PowerSeries ℚ) * F) = 144 * coeff m F := by
  have e : (144 : PowerSeries ℚ) = C (144 : ℚ) := (map_ofNat C 144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn168 : derivative ℚ (168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 168
@[simp] lemma cc168 : constantCoeff (168 : PowerSeries ℚ) = 168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 168
lemma cm168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((168 : PowerSeries ℚ) * F) = 168 * coeff m F := by
  have e : (168 : PowerSeries ℚ) = C (168 : ℚ) := (map_ofNat C 168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn192 : derivative ℚ (192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 192
@[simp] lemma cc192 : constantCoeff (192 : PowerSeries ℚ) = 192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 192
lemma cm192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((192 : PowerSeries ℚ) * F) = 192 * coeff m F := by
  have e : (192 : PowerSeries ℚ) = C (192 : ℚ) := (map_ofNat C 192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn210 : derivative ℚ (210 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 210
@[simp] lemma cc210 : constantCoeff (210 : PowerSeries ℚ) = 210 := by simpa using map_natCast (constantCoeff (R := ℚ)) 210
lemma cm210 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((210 : PowerSeries ℚ) * F) = 210 * coeff m F := by
  have e : (210 : PowerSeries ℚ) = C (210 : ℚ) := (map_ofNat C 210).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn220 : derivative ℚ (220 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 220
@[simp] lemma cc220 : constantCoeff (220 : PowerSeries ℚ) = 220 := by simpa using map_natCast (constantCoeff (R := ℚ)) 220
lemma cm220 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((220 : PowerSeries ℚ) * F) = 220 * coeff m F := by
  have e : (220 : PowerSeries ℚ) = C (220 : ℚ) := (map_ofNat C 220).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn294 : derivative ℚ (294 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 294
@[simp] lemma cc294 : constantCoeff (294 : PowerSeries ℚ) = 294 := by simpa using map_natCast (constantCoeff (R := ℚ)) 294
lemma cm294 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((294 : PowerSeries ℚ) * F) = 294 * coeff m F := by
  have e : (294 : PowerSeries ℚ) = C (294 : ℚ) := (map_ofNat C 294).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1166 : derivative ℚ (1166 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1166
@[simp] lemma cc1166 : constantCoeff (1166 : PowerSeries ℚ) = 1166 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1166
lemma cm1166 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1166 : PowerSeries ℚ) * F) = 1166 * coeff m F := by
  have e : (1166 : PowerSeries ℚ) = C (1166 : ℚ) := (map_ofNat C 1166).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1204 : derivative ℚ (1204 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1204
@[simp] lemma cc1204 : constantCoeff (1204 : PowerSeries ℚ) = 1204 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1204
lemma cm1204 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1204 : PowerSeries ℚ) * F) = 1204 * coeff m F := by
  have e : (1204 : PowerSeries ℚ) = C (1204 : ℚ) := (map_ofNat C 1204).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1390 : derivative ℚ (1390 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1390
@[simp] lemma cc1390 : constantCoeff (1390 : PowerSeries ℚ) = 1390 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1390
lemma cm1390 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1390 : PowerSeries ℚ) * F) = 1390 * coeff m F := by
  have e : (1390 : PowerSeries ℚ) = C (1390 : ℚ) := (map_ofNat C 1390).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2249 : derivative ℚ (2249 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2249
@[simp] lemma cc2249 : constantCoeff (2249 : PowerSeries ℚ) = 2249 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2249
lemma cm2249 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2249 : PowerSeries ℚ) * F) = 2249 * coeff m F := by
  have e : (2249 : PowerSeries ℚ) = C (2249 : ℚ) := (map_ofNat C 2249).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2878 : derivative ℚ (2878 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2878
@[simp] lemma cc2878 : constantCoeff (2878 : PowerSeries ℚ) = 2878 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2878
lemma cm2878 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2878 : PowerSeries ℚ) * F) = 2878 * coeff m F := by
  have e : (2878 : PowerSeries ℚ) = C (2878 : ℚ) := (map_ofNat C 2878).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3652 : derivative ℚ (3652 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3652
@[simp] lemma cc3652 : constantCoeff (3652 : PowerSeries ℚ) = 3652 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3652
lemma cm3652 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3652 : PowerSeries ℚ) * F) = 3652 * coeff m F := by
  have e : (3652 : PowerSeries ℚ) = C (3652 : ℚ) := (map_ofNat C 3652).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4759 : derivative ℚ (4759 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4759
@[simp] lemma cc4759 : constantCoeff (4759 : PowerSeries ℚ) = 4759 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4759
lemma cm4759 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4759 : PowerSeries ℚ) * F) = 4759 * coeff m F := by
  have e : (4759 : PowerSeries ℚ) = C (4759 : ℚ) := (map_ofNat C 4759).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4884 : derivative ℚ (4884 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4884
@[simp] lemma cc4884 : constantCoeff (4884 : PowerSeries ℚ) = 4884 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4884
lemma cm4884 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4884 : PowerSeries ℚ) * F) = 4884 * coeff m F := by
  have e : (4884 : PowerSeries ℚ) = C (4884 : ℚ) := (map_ofNat C 4884).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5080 : derivative ℚ (5080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5080
@[simp] lemma cc5080 : constantCoeff (5080 : PowerSeries ℚ) = 5080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5080
lemma cm5080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5080 : PowerSeries ℚ) * F) = 5080 * coeff m F := by
  have e : (5080 : PowerSeries ℚ) = C (5080 : ℚ) := (map_ofNat C 5080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5810 : derivative ℚ (5810 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5810
@[simp] lemma cc5810 : constantCoeff (5810 : PowerSeries ℚ) = 5810 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5810
lemma cm5810 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5810 : PowerSeries ℚ) * F) = 5810 * coeff m F := by
  have e : (5810 : PowerSeries ℚ) = C (5810 : ℚ) := (map_ofNat C 5810).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6109 : derivative ℚ (6109 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6109
@[simp] lemma cc6109 : constantCoeff (6109 : PowerSeries ℚ) = 6109 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6109
lemma cm6109 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6109 : PowerSeries ℚ) * F) = 6109 * coeff m F := by
  have e : (6109 : PowerSeries ℚ) = C (6109 : ℚ) := (map_ofNat C 6109).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6110 : derivative ℚ (6110 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6110
@[simp] lemma cc6110 : constantCoeff (6110 : PowerSeries ℚ) = 6110 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6110
lemma cm6110 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6110 : PowerSeries ℚ) * F) = 6110 * coeff m F := by
  have e : (6110 : PowerSeries ℚ) = C (6110 : ℚ) := (map_ofNat C 6110).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6149 : derivative ℚ (6149 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6149
@[simp] lemma cc6149 : constantCoeff (6149 : PowerSeries ℚ) = 6149 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6149
lemma cm6149 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6149 : PowerSeries ℚ) * F) = 6149 * coeff m F := by
  have e : (6149 : PowerSeries ℚ) = C (6149 : ℚ) := (map_ofNat C 6149).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7275 : derivative ℚ (7275 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7275
@[simp] lemma cc7275 : constantCoeff (7275 : PowerSeries ℚ) = 7275 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7275
lemma cm7275 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7275 : PowerSeries ℚ) * F) = 7275 * coeff m F := by
  have e : (7275 : PowerSeries ℚ) = C (7275 : ℚ) := (map_ofNat C 7275).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8476 : derivative ℚ (8476 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8476
@[simp] lemma cc8476 : constantCoeff (8476 : PowerSeries ℚ) = 8476 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8476
lemma cm8476 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8476 : PowerSeries ℚ) * F) = 8476 * coeff m F := by
  have e : (8476 : PowerSeries ℚ) = C (8476 : ℚ) := (map_ofNat C 8476).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8929 : derivative ℚ (8929 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8929
@[simp] lemma cc8929 : constantCoeff (8929 : PowerSeries ℚ) = 8929 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8929
lemma cm8929 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8929 : PowerSeries ℚ) * F) = 8929 * coeff m F := by
  have e : (8929 : PowerSeries ℚ) = C (8929 : ℚ) := (map_ofNat C 8929).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10074 : derivative ℚ (10074 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10074
@[simp] lemma cc10074 : constantCoeff (10074 : PowerSeries ℚ) = 10074 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10074
lemma cm10074 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10074 : PowerSeries ℚ) * F) = 10074 * coeff m F := by
  have e : (10074 : PowerSeries ℚ) = C (10074 : ℚ) := (map_ofNat C 10074).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10890 : derivative ℚ (10890 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10890
@[simp] lemma cc10890 : constantCoeff (10890 : PowerSeries ℚ) = 10890 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10890
lemma cm10890 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10890 : PowerSeries ℚ) * F) = 10890 * coeff m F := by
  have e : (10890 : PowerSeries ℚ) = C (10890 : ℚ) := (map_ofNat C 10890).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11479 : derivative ℚ (11479 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11479
@[simp] lemma cc11479 : constantCoeff (11479 : PowerSeries ℚ) = 11479 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11479
lemma cm11479 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11479 : PowerSeries ℚ) * F) = 11479 * coeff m F := by
  have e : (11479 : PowerSeries ℚ) = C (11479 : ℚ) := (map_ofNat C 11479).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn13574 : derivative ℚ (13574 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13574
@[simp] lemma cc13574 : constantCoeff (13574 : PowerSeries ℚ) = 13574 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13574
lemma cm13574 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13574 : PowerSeries ℚ) * F) = 13574 * coeff m F := by
  have e : (13574 : PowerSeries ℚ) = C (13574 : ℚ) := (map_ofNat C 13574).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14053 : derivative ℚ (14053 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14053
@[simp] lemma cc14053 : constantCoeff (14053 : PowerSeries ℚ) = 14053 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14053
lemma cm14053 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14053 : PowerSeries ℚ) * F) = 14053 * coeff m F := by
  have e : (14053 : PowerSeries ℚ) = C (14053 : ℚ) := (map_ofNat C 14053).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14229 : derivative ℚ (14229 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14229
@[simp] lemma cc14229 : constantCoeff (14229 : PowerSeries ℚ) = 14229 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14229
lemma cm14229 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14229 : PowerSeries ℚ) * F) = 14229 * coeff m F := by
  have e : (14229 : PowerSeries ℚ) = C (14229 : ℚ) := (map_ofNat C 14229).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14564 : derivative ℚ (14564 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14564
@[simp] lemma cc14564 : constantCoeff (14564 : PowerSeries ℚ) = 14564 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14564
lemma cm14564 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14564 : PowerSeries ℚ) * F) = 14564 * coeff m F := by
  have e : (14564 : PowerSeries ℚ) = C (14564 : ℚ) := (map_ofNat C 14564).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15164 : derivative ℚ (15164 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15164
@[simp] lemma cc15164 : constantCoeff (15164 : PowerSeries ℚ) = 15164 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15164
lemma cm15164 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15164 : PowerSeries ℚ) * F) = 15164 * coeff m F := by
  have e : (15164 : PowerSeries ℚ) = C (15164 : ℚ) := (map_ofNat C 15164).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16004 : derivative ℚ (16004 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16004
@[simp] lemma cc16004 : constantCoeff (16004 : PowerSeries ℚ) = 16004 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16004
lemma cm16004 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16004 : PowerSeries ℚ) * F) = 16004 * coeff m F := by
  have e : (16004 : PowerSeries ℚ) = C (16004 : ℚ) := (map_ofNat C 16004).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16511 : derivative ℚ (16511 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16511
@[simp] lemma cc16511 : constantCoeff (16511 : PowerSeries ℚ) = 16511 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16511
lemma cm16511 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16511 : PowerSeries ℚ) * F) = 16511 * coeff m F := by
  have e : (16511 : PowerSeries ℚ) = C (16511 : ℚ) := (map_ofNat C 16511).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17644 : derivative ℚ (17644 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17644
@[simp] lemma cc17644 : constantCoeff (17644 : PowerSeries ℚ) = 17644 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17644
lemma cm17644 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17644 : PowerSeries ℚ) * F) = 17644 * coeff m F := by
  have e : (17644 : PowerSeries ℚ) = C (17644 : ℚ) := (map_ofNat C 17644).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17858 : derivative ℚ (17858 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17858
@[simp] lemma cc17858 : constantCoeff (17858 : PowerSeries ℚ) = 17858 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17858
lemma cm17858 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17858 : PowerSeries ℚ) * F) = 17858 * coeff m F := by
  have e : (17858 : PowerSeries ℚ) = C (17858 : ℚ) := (map_ofNat C 17858).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18627 : derivative ℚ (18627 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18627
@[simp] lemma cc18627 : constantCoeff (18627 : PowerSeries ℚ) = 18627 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18627
lemma cm18627 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18627 : PowerSeries ℚ) * F) = 18627 * coeff m F := by
  have e : (18627 : PowerSeries ℚ) = C (18627 : ℚ) := (map_ofNat C 18627).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19068 : derivative ℚ (19068 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19068
@[simp] lemma cc19068 : constantCoeff (19068 : PowerSeries ℚ) = 19068 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19068
lemma cm19068 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19068 : PowerSeries ℚ) * F) = 19068 * coeff m F := by
  have e : (19068 : PowerSeries ℚ) = C (19068 : ℚ) := (map_ofNat C 19068).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20107 : derivative ℚ (20107 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20107
@[simp] lemma cc20107 : constantCoeff (20107 : PowerSeries ℚ) = 20107 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20107
lemma cm20107 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20107 : PowerSeries ℚ) * F) = 20107 * coeff m F := by
  have e : (20107 : PowerSeries ℚ) = C (20107 : ℚ) := (map_ofNat C 20107).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn23795 : derivative ℚ (23795 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 23795
@[simp] lemma cc23795 : constantCoeff (23795 : PowerSeries ℚ) = 23795 := by simpa using map_natCast (constantCoeff (R := ℚ)) 23795
lemma cm23795 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((23795 : PowerSeries ℚ) * F) = 23795 * coeff m F := by
  have e : (23795 : PowerSeries ℚ) = C (23795 : ℚ) := (map_ofNat C 23795).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25542 : derivative ℚ (25542 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25542
@[simp] lemma cc25542 : constantCoeff (25542 : PowerSeries ℚ) = 25542 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25542
lemma cm25542 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25542 : PowerSeries ℚ) * F) = 25542 * coeff m F := by
  have e : (25542 : PowerSeries ℚ) = C (25542 : ℚ) := (map_ofNat C 25542).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn27888 : derivative ℚ (27888 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 27888
@[simp] lemma cc27888 : constantCoeff (27888 : PowerSeries ℚ) = 27888 := by simpa using map_natCast (constantCoeff (R := ℚ)) 27888
lemma cm27888 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((27888 : PowerSeries ℚ) * F) = 27888 * coeff m F := by
  have e : (27888 : PowerSeries ℚ) = C (27888 : ℚ) := (map_ofNat C 27888).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30139 : derivative ℚ (30139 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30139
@[simp] lemma cc30139 : constantCoeff (30139 : PowerSeries ℚ) = 30139 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30139
lemma cm30139 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30139 : PowerSeries ℚ) * F) = 30139 * coeff m F := by
  have e : (30139 : PowerSeries ℚ) = C (30139 : ℚ) := (map_ofNat C 30139).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30347 : derivative ℚ (30347 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30347
@[simp] lemma cc30347 : constantCoeff (30347 : PowerSeries ℚ) = 30347 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30347
lemma cm30347 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30347 : PowerSeries ℚ) * F) = 30347 * coeff m F := by
  have e : (30347 : PowerSeries ℚ) = C (30347 : ℚ) := (map_ofNat C 30347).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32756 : derivative ℚ (32756 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32756
@[simp] lemma cc32756 : constantCoeff (32756 : PowerSeries ℚ) = 32756 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32756
lemma cm32756 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32756 : PowerSeries ℚ) * F) = 32756 * coeff m F := by
  have e : (32756 : PowerSeries ℚ) = C (32756 : ℚ) := (map_ofNat C 32756).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40765 : derivative ℚ (40765 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40765
@[simp] lemma cc40765 : constantCoeff (40765 : PowerSeries ℚ) = 40765 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40765
lemma cm40765 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40765 : PowerSeries ℚ) * F) = 40765 * coeff m F := by
  have e : (40765 : PowerSeries ℚ) = C (40765 : ℚ) := (map_ofNat C 40765).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn41338 : derivative ℚ (41338 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 41338
@[simp] lemma cc41338 : constantCoeff (41338 : PowerSeries ℚ) = 41338 := by simpa using map_natCast (constantCoeff (R := ℚ)) 41338
lemma cm41338 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((41338 : PowerSeries ℚ) * F) = 41338 * coeff m F := by
  have e : (41338 : PowerSeries ℚ) = C (41338 : ℚ) := (map_ofNat C 41338).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn42976 : derivative ℚ (42976 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 42976
@[simp] lemma cc42976 : constantCoeff (42976 : PowerSeries ℚ) = 42976 := by simpa using map_natCast (constantCoeff (R := ℚ)) 42976
lemma cm42976 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((42976 : PowerSeries ℚ) * F) = 42976 * coeff m F := by
  have e : (42976 : PowerSeries ℚ) = C (42976 : ℚ) := (map_ofNat C 42976).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn49134 : derivative ℚ (49134 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 49134
@[simp] lemma cc49134 : constantCoeff (49134 : PowerSeries ℚ) = 49134 := by simpa using map_natCast (constantCoeff (R := ℚ)) 49134
lemma cm49134 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((49134 : PowerSeries ℚ) * F) = 49134 * coeff m F := by
  have e : (49134 : PowerSeries ℚ) = C (49134 : ℚ) := (map_ofNat C 49134).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn66210 : derivative ℚ (66210 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 66210
@[simp] lemma cc66210 : constantCoeff (66210 : PowerSeries ℚ) = 66210 := by simpa using map_natCast (constantCoeff (R := ℚ)) 66210
lemma cm66210 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((66210 : PowerSeries ℚ) * F) = 66210 * coeff m F := by
  have e : (66210 : PowerSeries ℚ) = C (66210 : ℚ) := (map_ofNat C 66210).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn66812 : derivative ℚ (66812 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 66812
@[simp] lemma cc66812 : constantCoeff (66812 : PowerSeries ℚ) = 66812 := by simpa using map_natCast (constantCoeff (R := ℚ)) 66812
lemma cm66812 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((66812 : PowerSeries ℚ) * F) = 66812 * coeff m F := by
  have e : (66812 : PowerSeries ℚ) = C (66812 : ℚ) := (map_ofNat C 66812).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn68852 : derivative ℚ (68852 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 68852
@[simp] lemma cc68852 : constantCoeff (68852 : PowerSeries ℚ) = 68852 := by simpa using map_natCast (constantCoeff (R := ℚ)) 68852
lemma cm68852 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((68852 : PowerSeries ℚ) * F) = 68852 * coeff m F := by
  have e : (68852 : PowerSeries ℚ) = C (68852 : ℚ) := (map_ofNat C 68852).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn69951 : derivative ℚ (69951 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 69951
@[simp] lemma cc69951 : constantCoeff (69951 : PowerSeries ℚ) = 69951 := by simpa using map_natCast (constantCoeff (R := ℚ)) 69951
lemma cm69951 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((69951 : PowerSeries ℚ) * F) = 69951 * coeff m F := by
  have e : (69951 : PowerSeries ℚ) = C (69951 : ℚ) := (map_ofNat C 69951).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80556 : derivative ℚ (80556 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80556
@[simp] lemma cc80556 : constantCoeff (80556 : PowerSeries ℚ) = 80556 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80556
lemma cm80556 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80556 : PowerSeries ℚ) * F) = 80556 * coeff m F := by
  have e : (80556 : PowerSeries ℚ) = C (80556 : ℚ) := (map_ofNat C 80556).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn85724 : derivative ℚ (85724 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 85724
@[simp] lemma cc85724 : constantCoeff (85724 : PowerSeries ℚ) = 85724 := by simpa using map_natCast (constantCoeff (R := ℚ)) 85724
lemma cm85724 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((85724 : PowerSeries ℚ) * F) = 85724 * coeff m F := by
  have e : (85724 : PowerSeries ℚ) = C (85724 : ℚ) := (map_ofNat C 85724).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn89812 : derivative ℚ (89812 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 89812
@[simp] lemma cc89812 : constantCoeff (89812 : PowerSeries ℚ) = 89812 := by simpa using map_natCast (constantCoeff (R := ℚ)) 89812
lemma cm89812 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((89812 : PowerSeries ℚ) * F) = 89812 * coeff m F := by
  have e : (89812 : PowerSeries ℚ) = C (89812 : ℚ) := (map_ofNat C 89812).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn98877 : derivative ℚ (98877 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 98877
@[simp] lemma cc98877 : constantCoeff (98877 : PowerSeries ℚ) = 98877 := by simpa using map_natCast (constantCoeff (R := ℚ)) 98877
lemma cm98877 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((98877 : PowerSeries ℚ) * F) = 98877 * coeff m F := by
  have e : (98877 : PowerSeries ℚ) = C (98877 : ℚ) := (map_ofNat C 98877).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn99908 : derivative ℚ (99908 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 99908
@[simp] lemma cc99908 : constantCoeff (99908 : PowerSeries ℚ) = 99908 := by simpa using map_natCast (constantCoeff (R := ℚ)) 99908
lemma cm99908 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((99908 : PowerSeries ℚ) * F) = 99908 * coeff m F := by
  have e : (99908 : PowerSeries ℚ) = C (99908 : ℚ) := (map_ofNat C 99908).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn101144 : derivative ℚ (101144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 101144
@[simp] lemma cc101144 : constantCoeff (101144 : PowerSeries ℚ) = 101144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 101144
lemma cm101144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((101144 : PowerSeries ℚ) * F) = 101144 * coeff m F := by
  have e : (101144 : PowerSeries ℚ) = C (101144 : ℚ) := (map_ofNat C 101144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn106020 : derivative ℚ (106020 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 106020
@[simp] lemma cc106020 : constantCoeff (106020 : PowerSeries ℚ) = 106020 := by simpa using map_natCast (constantCoeff (R := ℚ)) 106020
lemma cm106020 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((106020 : PowerSeries ℚ) * F) = 106020 * coeff m F := by
  have e : (106020 : PowerSeries ℚ) = C (106020 : ℚ) := (map_ofNat C 106020).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn109281 : derivative ℚ (109281 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 109281
@[simp] lemma cc109281 : constantCoeff (109281 : PowerSeries ℚ) = 109281 := by simpa using map_natCast (constantCoeff (R := ℚ)) 109281
lemma cm109281 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((109281 : PowerSeries ℚ) * F) = 109281 * coeff m F := by
  have e : (109281 : PowerSeries ℚ) = C (109281 : ℚ) := (map_ofNat C 109281).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn114064 : derivative ℚ (114064 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 114064
@[simp] lemma cc114064 : constantCoeff (114064 : PowerSeries ℚ) = 114064 := by simpa using map_natCast (constantCoeff (R := ℚ)) 114064
lemma cm114064 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((114064 : PowerSeries ℚ) * F) = 114064 * coeff m F := by
  have e : (114064 : PowerSeries ℚ) = C (114064 : ℚ) := (map_ofNat C 114064).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn115735 : derivative ℚ (115735 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 115735
@[simp] lemma cc115735 : constantCoeff (115735 : PowerSeries ℚ) = 115735 := by simpa using map_natCast (constantCoeff (R := ℚ)) 115735
lemma cm115735 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((115735 : PowerSeries ℚ) * F) = 115735 * coeff m F := by
  have e : (115735 : PowerSeries ℚ) = C (115735 : ℚ) := (map_ofNat C 115735).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn124844 : derivative ℚ (124844 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 124844
@[simp] lemma cc124844 : constantCoeff (124844 : PowerSeries ℚ) = 124844 := by simpa using map_natCast (constantCoeff (R := ℚ)) 124844
lemma cm124844 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((124844 : PowerSeries ℚ) * F) = 124844 * coeff m F := by
  have e : (124844 : PowerSeries ℚ) = C (124844 : ℚ) := (map_ofNat C 124844).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn125072 : derivative ℚ (125072 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 125072
@[simp] lemma cc125072 : constantCoeff (125072 : PowerSeries ℚ) = 125072 := by simpa using map_natCast (constantCoeff (R := ℚ)) 125072
lemma cm125072 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((125072 : PowerSeries ℚ) * F) = 125072 * coeff m F := by
  have e : (125072 : PowerSeries ℚ) = C (125072 : ℚ) := (map_ofNat C 125072).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn125452 : derivative ℚ (125452 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 125452
@[simp] lemma cc125452 : constantCoeff (125452 : PowerSeries ℚ) = 125452 := by simpa using map_natCast (constantCoeff (R := ℚ)) 125452
lemma cm125452 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((125452 : PowerSeries ℚ) * F) = 125452 * coeff m F := by
  have e : (125452 : PowerSeries ℚ) = C (125452 : ℚ) := (map_ofNat C 125452).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn205876 : derivative ℚ (205876 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 205876
@[simp] lemma cc205876 : constantCoeff (205876 : PowerSeries ℚ) = 205876 := by simpa using map_natCast (constantCoeff (R := ℚ)) 205876
lemma cm205876 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((205876 : PowerSeries ℚ) * F) = 205876 * coeff m F := by
  have e : (205876 : PowerSeries ℚ) = C (205876 : ℚ) := (map_ofNat C 205876).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn222716 : derivative ℚ (222716 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 222716
@[simp] lemma cc222716 : constantCoeff (222716 : PowerSeries ℚ) = 222716 := by simpa using map_natCast (constantCoeff (R := ℚ)) 222716
lemma cm222716 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((222716 : PowerSeries ℚ) * F) = 222716 * coeff m F := by
  have e : (222716 : PowerSeries ℚ) = C (222716 : ℚ) := (map_ofNat C 222716).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn273644 : derivative ℚ (273644 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 273644
@[simp] lemma cc273644 : constantCoeff (273644 : PowerSeries ℚ) = 273644 := by simpa using map_natCast (constantCoeff (R := ℚ)) 273644
lemma cm273644 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((273644 : PowerSeries ℚ) * F) = 273644 * coeff m F := by
  have e : (273644 : PowerSeries ℚ) = C (273644 : ℚ) := (map_ofNat C 273644).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn352932 : derivative ℚ (352932 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 352932
@[simp] lemma cc352932 : constantCoeff (352932 : PowerSeries ℚ) = 352932 := by simpa using map_natCast (constantCoeff (R := ℚ)) 352932
lemma cm352932 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((352932 : PowerSeries ℚ) * F) = 352932 * coeff m F := by
  have e : (352932 : PowerSeries ℚ) = C (352932 : ℚ) := (map_ofNat C 352932).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn395004 : derivative ℚ (395004 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 395004
@[simp] lemma cc395004 : constantCoeff (395004 : PowerSeries ℚ) = 395004 := by simpa using map_natCast (constantCoeff (R := ℚ)) 395004
lemma cm395004 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((395004 : PowerSeries ℚ) * F) = 395004 * coeff m F := by
  have e : (395004 : PowerSeries ℚ) = C (395004 : ℚ) := (map_ofNat C 395004).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn412428 : derivative ℚ (412428 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 412428
@[simp] lemma cc412428 : constantCoeff (412428 : PowerSeries ℚ) = 412428 := by simpa using map_natCast (constantCoeff (R := ℚ)) 412428
lemma cm412428 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((412428 : PowerSeries ℚ) * F) = 412428 * coeff m F := by
  have e : (412428 : PowerSeries ℚ) = C (412428 : ℚ) := (map_ofNat C 412428).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn456732 : derivative ℚ (456732 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 456732
@[simp] lemma cc456732 : constantCoeff (456732 : PowerSeries ℚ) = 456732 := by simpa using map_natCast (constantCoeff (R := ℚ)) 456732
lemma cm456732 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((456732 : PowerSeries ℚ) * F) = 456732 * coeff m F := by
  have e : (456732 : PowerSeries ℚ) = C (456732 : ℚ) := (map_ofNat C 456732).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn548268 : derivative ℚ (548268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 548268
@[simp] lemma cc548268 : constantCoeff (548268 : PowerSeries ℚ) = 548268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 548268
lemma cm548268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((548268 : PowerSeries ℚ) * F) = 548268 * coeff m F := by
  have e : (548268 : PowerSeries ℚ) = C (548268 : ℚ) := (map_ofNat C 548268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn550332 : derivative ℚ (550332 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 550332
@[simp] lemma cc550332 : constantCoeff (550332 : PowerSeries ℚ) = 550332 := by simpa using map_natCast (constantCoeff (R := ℚ)) 550332
lemma cm550332 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((550332 : PowerSeries ℚ) * F) = 550332 * coeff m F := by
  have e : (550332 : PowerSeries ℚ) = C (550332 : ℚ) := (map_ofNat C 550332).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn621496 : derivative ℚ (621496 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 621496
@[simp] lemma cc621496 : constantCoeff (621496 : PowerSeries ℚ) = 621496 := by simpa using map_natCast (constantCoeff (R := ℚ)) 621496
lemma cm621496 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((621496 : PowerSeries ℚ) * F) = 621496 * coeff m F := by
  have e : (621496 : PowerSeries ℚ) = C (621496 : ℚ) := (map_ofNat C 621496).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn621988 : derivative ℚ (621988 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 621988
@[simp] lemma cc621988 : constantCoeff (621988 : PowerSeries ℚ) = 621988 := by simpa using map_natCast (constantCoeff (R := ℚ)) 621988
lemma cm621988 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((621988 : PowerSeries ℚ) * F) = 621988 * coeff m F := by
  have e : (621988 : PowerSeries ℚ) = C (621988 : ℚ) := (map_ofNat C 621988).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn661260 : derivative ℚ (661260 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 661260
@[simp] lemma cc661260 : constantCoeff (661260 : PowerSeries ℚ) = 661260 := by simpa using map_natCast (constantCoeff (R := ℚ)) 661260
lemma cm661260 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((661260 : PowerSeries ℚ) * F) = 661260 * coeff m F := by
  have e : (661260 : PowerSeries ℚ) = C (661260 : ℚ) := (map_ofNat C 661260).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn748960 : derivative ℚ (748960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 748960
@[simp] lemma cc748960 : constantCoeff (748960 : PowerSeries ℚ) = 748960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 748960
lemma cm748960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((748960 : PowerSeries ℚ) * F) = 748960 * coeff m F := by
  have e : (748960 : PowerSeries ℚ) = C (748960 : ℚ) := (map_ofNat C 748960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn790784 : derivative ℚ (790784 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 790784
@[simp] lemma cc790784 : constantCoeff (790784 : PowerSeries ℚ) = 790784 := by simpa using map_natCast (constantCoeff (R := ℚ)) 790784
lemma cm790784 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((790784 : PowerSeries ℚ) * F) = 790784 * coeff m F := by
  have e : (790784 : PowerSeries ℚ) = C (790784 : ℚ) := (map_ofNat C 790784).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn877268 : derivative ℚ (877268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 877268
@[simp] lemma cc877268 : constantCoeff (877268 : PowerSeries ℚ) = 877268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 877268
lemma cm877268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((877268 : PowerSeries ℚ) * F) = 877268 * coeff m F := by
  have e : (877268 : PowerSeries ℚ) = C (877268 : ℚ) := (map_ofNat C 877268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1148202 : derivative ℚ (1148202 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1148202
@[simp] lemma cc1148202 : constantCoeff (1148202 : PowerSeries ℚ) = 1148202 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1148202
lemma cm1148202 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1148202 : PowerSeries ℚ) * F) = 1148202 * coeff m F := by
  have e : (1148202 : PowerSeries ℚ) = C (1148202 : ℚ) := (map_ofNat C 1148202).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1265304 : derivative ℚ (1265304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1265304
@[simp] lemma cc1265304 : constantCoeff (1265304 : PowerSeries ℚ) = 1265304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1265304
lemma cm1265304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1265304 : PowerSeries ℚ) * F) = 1265304 * coeff m F := by
  have e : (1265304 : PowerSeries ℚ) = C (1265304 : ℚ) := (map_ofNat C 1265304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1449044 : derivative ℚ (1449044 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1449044
@[simp] lemma cc1449044 : constantCoeff (1449044 : PowerSeries ℚ) = 1449044 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1449044
lemma cm1449044 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1449044 : PowerSeries ℚ) * F) = 1449044 * coeff m F := by
  have e : (1449044 : PowerSeries ℚ) = C (1449044 : ℚ) := (map_ofNat C 1449044).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1854552 : derivative ℚ (1854552 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1854552
@[simp] lemma cc1854552 : constantCoeff (1854552 : PowerSeries ℚ) = 1854552 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1854552
lemma cm1854552 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1854552 : PowerSeries ℚ) * F) = 1854552 * coeff m F := by
  have e : (1854552 : PowerSeries ℚ) = C (1854552 : ℚ) := (map_ofNat C 1854552).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2114748 : derivative ℚ (2114748 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2114748
@[simp] lemma cc2114748 : constantCoeff (2114748 : PowerSeries ℚ) = 2114748 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2114748
lemma cm2114748 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2114748 : PowerSeries ℚ) * F) = 2114748 * coeff m F := by
  have e : (2114748 : PowerSeries ℚ) = C (2114748 : ℚ) := (map_ofNat C 2114748).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2371788 : derivative ℚ (2371788 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2371788
@[simp] lemma cc2371788 : constantCoeff (2371788 : PowerSeries ℚ) = 2371788 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2371788
lemma cm2371788 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2371788 : PowerSeries ℚ) * F) = 2371788 * coeff m F := by
  have e : (2371788 : PowerSeries ℚ) = C (2371788 : ℚ) := (map_ofNat C 2371788).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3393404 : derivative ℚ (3393404 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3393404
@[simp] lemma cc3393404 : constantCoeff (3393404 : PowerSeries ℚ) = 3393404 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3393404
lemma cm3393404 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3393404 : PowerSeries ℚ) * F) = 3393404 * coeff m F := by
  have e : (3393404 : PowerSeries ℚ) = C (3393404 : ℚ) := (map_ofNat C 3393404).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3897428 : derivative ℚ (3897428 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3897428
@[simp] lemma cc3897428 : constantCoeff (3897428 : PowerSeries ℚ) = 3897428 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3897428
lemma cm3897428 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3897428 : PowerSeries ℚ) * F) = 3897428 * coeff m F := by
  have e : (3897428 : PowerSeries ℚ) = C (3897428 : ℚ) := (map_ofNat C 3897428).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4103960 : derivative ℚ (4103960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4103960
@[simp] lemma cc4103960 : constantCoeff (4103960 : PowerSeries ℚ) = 4103960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4103960
lemma cm4103960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4103960 : PowerSeries ℚ) * F) = 4103960 * coeff m F := by
  have e : (4103960 : PowerSeries ℚ) = C (4103960 : ℚ) := (map_ofNat C 4103960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5423052 : derivative ℚ (5423052 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5423052
@[simp] lemma cc5423052 : constantCoeff (5423052 : PowerSeries ℚ) = 5423052 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5423052
lemma cm5423052 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5423052 : PowerSeries ℚ) * F) = 5423052 * coeff m F := by
  have e : (5423052 : PowerSeries ℚ) = C (5423052 : ℚ) := (map_ofNat C 5423052).symm
  rw [e, coeff_C_mul]

noncomputable def R : PowerSeries ℚ := X^4 - 2*X^3 - X^2 - 2*X + 1
noncomputable def DD : PowerSeries ℚ := -2*X^6 + 4*X^5 + 2*X^4 + 4*X^3 - 2*X^2
noncomputable def NN (S : PowerSeries ℚ) : PowerSeries ℚ := (X^7 - 3*X^6 + 2*X^4 + 2*X^3 - 3*X + 1) + (X^5 + X^3 - X^2 - 2*X + 1) * S

set_option maxHeartbeats 1000000 in
lemma hdD : derivative ℚ DD = -12*X^5 + 20*X^4 + 8*X^3 + 12*X^2 - 4*X := by
  simp [DD] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdR : derivative ℚ R = 4*X^3 - 6*X^2 - 2*X - 2 := by
  simp [R] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdN (S : PowerSeries ℚ) : derivative ℚ (NN S) = 7*X^6 - 18*X^5 + 8*X^3 + 6*X^2 - 3 + (5*X^4 + 3*X^2 - 2*X - 2) * S + (X^5 + X^3 - X^2 - 2*X + 1) * derivative ℚ S := by
  simp [NN] <;> ring

set_option maxHeartbeats 4000000 in
lemma ode1 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((1) * X ^ 1 + (-4) * X ^ 2 + (2) * X ^ 3 + (3) * X ^ 4 + (4) * X ^ 5 + (-5) * X ^ 7 + (-2) * X ^ 9 + (1) * X ^ 10 : PowerSeries ℚ) * derivative ℚ AA + ((2) * X ^ 0 + (-7) * X ^ 1 + (3) * X ^ 2 + (-3) * X ^ 3 + (16) * X ^ 4 + (-6) * X ^ 5 + (2) * X ^ 6 + (3) * X ^ 7 + (3) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) * AA = ((5) * X ^ 3 + (-1) * X ^ 4 + (-11) * X ^ 5 + (2) * X ^ 6 + (7) * X ^ 7 + (-1) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) := by
  have r1 := hA
  have r2 : derivative ℚ AA * DD + AA * derivative ℚ DD = derivative ℚ (NN S) := by
    have := congrArg (derivative ℚ) hA
    rw [Derivation.leibniz] at this
    simp only [smul_eq_mul] at this
    rw [← this]; ring
  have r4 := sqrt_ode S R hS
  have hK : (2 * R * DD ^ 2 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((8) * X ^ 0 + (-48) * X ^ 1 + (72) * X ^ 2 + (-16) * X ^ 3 + (144) * X ^ 4 + (-240) * X ^ 5 + (-56) * X ^ 6 + (-240) * X ^ 7 + (144) * X ^ 8 + (-16) * X ^ 9 + (72) * X ^ 10 + (-48) * X ^ 11 + (8) * X ^ 12 : PowerSeries ℚ)) 4 (by simp only [R, DD]; ring) (by simp [R, DD] <;> norm_num)
  apply mul_left_cancel₀ hK
  rw [hdD, hdN] at r2
  rw [hdR] at r4
  unfold NN at r1
  unfold DD at r1 r2
  unfold R at r4
  unfold DD R
  linear_combination (28*X^19 - 164*X^18 + 260*X^17 - 184*X^16 + 692*X^15 - 764*X^14 - 64*X^13 - 1340*X^12 + 328*X^11 + 196*X^10 + 768*X^9 + 68*X^8 - 180*X^7 - 88*X^6 - 36*X^5 + 60*X^4 - 12*X^3) * r1 + (-4*X^20 + 24*X^19 - 40*X^18 + 36*X^17 - 124*X^16 + 112*X^15 + 44*X^14 + 260*X^13 - 12*X^12 - 212*X^11 - 164*X^10 - 108*X^9 + 216*X^8 - 28*X^7 + 52*X^6 - 80*X^5 + 32*X^4 - 4*X^3) * r2 + (-2*X^21 + 8*X^20 - 8*X^19 + 20*X^18 - 40*X^17 - 16*X^16 - 30*X^15 + 16*X^14 + 112*X^13 + 24*X^12 + 16*X^11 - 128*X^10 - 30*X^9 + 40*X^8 + 24*X^7 + 20*X^6 - 40*X^5 + 16*X^4 - 2*X^3) * r4

set_option maxHeartbeats 1000000 in
lemma hdV : derivative ℚ ((1) * X ^ 1 + (-4) * X ^ 2 + (2) * X ^ 3 + (3) * X ^ 4 + (4) * X ^ 5 + (-5) * X ^ 7 + (-2) * X ^ 9 + (1) * X ^ 10 : PowerSeries ℚ) = ((1) * X ^ 0 + (-8) * X ^ 1 + (6) * X ^ 2 + (12) * X ^ 3 + (20) * X ^ 4 + (-35) * X ^ 6 + (-18) * X ^ 8 + (10) * X ^ 9 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU : derivative ℚ ((2) * X ^ 0 + (-7) * X ^ 1 + (3) * X ^ 2 + (-3) * X ^ 3 + (16) * X ^ 4 + (-6) * X ^ 5 + (2) * X ^ 6 + (3) * X ^ 7 + (3) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) = ((-7) * X ^ 0 + (6) * X ^ 1 + (-9) * X ^ 2 + (64) * X ^ 3 + (-30) * X ^ 4 + (12) * X ^ 5 + (21) * X ^ 6 + (24) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW : derivative ℚ ((5) * X ^ 3 + (-1) * X ^ 4 + (-11) * X ^ 5 + (2) * X ^ 6 + (7) * X ^ 7 + (-1) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) = ((15) * X ^ 2 + (-4) * X ^ 3 + (-55) * X ^ 4 + (12) * X ^ 5 + (49) * X ^ 6 + (-8) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdV1 : derivative ℚ ((1) * X ^ 0 + (-8) * X ^ 1 + (6) * X ^ 2 + (12) * X ^ 3 + (20) * X ^ 4 + (-35) * X ^ 6 + (-18) * X ^ 8 + (10) * X ^ 9 : PowerSeries ℚ) = ((-8) * X ^ 0 + (12) * X ^ 1 + (36) * X ^ 2 + (80) * X ^ 3 + (-210) * X ^ 5 + (-144) * X ^ 7 + (90) * X ^ 8 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU1 : derivative ℚ ((-7) * X ^ 0 + (6) * X ^ 1 + (-9) * X ^ 2 + (64) * X ^ 3 + (-30) * X ^ 4 + (12) * X ^ 5 + (21) * X ^ 6 + (24) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) = ((6) * X ^ 0 + (-18) * X ^ 1 + (192) * X ^ 2 + (-120) * X ^ 3 + (60) * X ^ 4 + (126) * X ^ 5 + (168) * X ^ 6 + (-72) * X ^ 7 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW1 : derivative ℚ ((15) * X ^ 2 + (-4) * X ^ 3 + (-55) * X ^ 4 + (12) * X ^ 5 + (49) * X ^ 6 + (-8) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) = ((30) * X ^ 1 + (-12) * X ^ 2 + (-220) * X ^ 3 + (60) * X ^ 4 + (294) * X ^ 5 + (-56) * X ^ 6 + (-72) * X ^ 7 : PowerSeries ℚ) := by
  simp <;> ring

lemma dmul (F G : PowerSeries ℚ) : derivative ℚ (F * G) = F * derivative ℚ G + G * derivative ℚ F := by
  rw [Derivation.leibniz]; simp only [smul_eq_mul]

set_option maxHeartbeats 4000000 in
lemma ode2 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((1) * X ^ 0 + (-8) * X ^ 1 + (6) * X ^ 2 + (12) * X ^ 3 + (20) * X ^ 4 + (-35) * X ^ 6 + (-18) * X ^ 8 + (10) * X ^ 9 : PowerSeries ℚ) * derivative ℚ AA + ((1) * X ^ 1 + (-4) * X ^ 2 + (2) * X ^ 3 + (3) * X ^ 4 + (4) * X ^ 5 + (-5) * X ^ 7 + (-2) * X ^ 9 + (1) * X ^ 10 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-7) * X ^ 0 + (6) * X ^ 1 + (-9) * X ^ 2 + (64) * X ^ 3 + (-30) * X ^ 4 + (12) * X ^ 5 + (21) * X ^ 6 + (24) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) * AA + ((2) * X ^ 0 + (-7) * X ^ 1 + (3) * X ^ 2 + (-3) * X ^ 3 + (16) * X ^ 4 + (-6) * X ^ 5 + (2) * X ^ 6 + (3) * X ^ 7 + (3) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) * derivative ℚ AA = ((15) * X ^ 2 + (-4) * X ^ 3 + (-55) * X ^ 4 + (12) * X ^ 5 + (49) * X ^ 6 + (-8) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode1 S AA hS hA)
  rw [map_add, dmul, dmul, hdV, hdU, hdW] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3' (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((-8) * X ^ 0 + (12) * X ^ 1 + (36) * X ^ 2 + (80) * X ^ 3 + (-210) * X ^ 5 + (-144) * X ^ 7 + (90) * X ^ 8 : PowerSeries ℚ) * derivative ℚ AA + ((1) * X ^ 0 + (-8) * X ^ 1 + (6) * X ^ 2 + (12) * X ^ 3 + (20) * X ^ 4 + (-35) * X ^ 6 + (-18) * X ^ 8 + (10) * X ^ 9 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + (((1) * X ^ 0 + (-8) * X ^ 1 + (6) * X ^ 2 + (12) * X ^ 3 + (20) * X ^ 4 + (-35) * X ^ 6 + (-18) * X ^ 8 + (10) * X ^ 9 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((1) * X ^ 1 + (-4) * X ^ 2 + (2) * X ^ 3 + (3) * X ^ 4 + (4) * X ^ 5 + (-5) * X ^ 7 + (-2) * X ^ 9 + (1) * X ^ 10 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA))) + (((6) * X ^ 0 + (-18) * X ^ 1 + (192) * X ^ 2 + (-120) * X ^ 3 + (60) * X ^ 4 + (126) * X ^ 5 + (168) * X ^ 6 + (-72) * X ^ 7 : PowerSeries ℚ) * AA + ((-7) * X ^ 0 + (6) * X ^ 1 + (-9) * X ^ 2 + (64) * X ^ 3 + (-30) * X ^ 4 + (12) * X ^ 5 + (21) * X ^ 6 + (24) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) * derivative ℚ AA) + (((-7) * X ^ 0 + (6) * X ^ 1 + (-9) * X ^ 2 + (64) * X ^ 3 + (-30) * X ^ 4 + (12) * X ^ 5 + (21) * X ^ 6 + (24) * X ^ 7 + (-9) * X ^ 8 : PowerSeries ℚ) * derivative ℚ AA + ((2) * X ^ 0 + (-7) * X ^ 1 + (3) * X ^ 2 + (-3) * X ^ 3 + (16) * X ^ 4 + (-6) * X ^ 5 + (2) * X ^ 6 + (3) * X ^ 7 + (3) * X ^ 8 + (-1) * X ^ 9 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA)) = ((30) * X ^ 1 + (-12) * X ^ 2 + (-220) * X ^ 3 + (60) * X ^ 4 + (294) * X ^ 5 + (-56) * X ^ 6 + (-72) * X ^ 7 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode2 S AA hS hA)
  rw [map_add, map_add, map_add, dmul, dmul, dmul, dmul, hdV1, hdV, hdU1, hdU, hdW1] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((17858) * X ^ 0 + (-40765) * X ^ 1 + (-14229) * X ^ 2 + (-14053) * X ^ 3 + (30347) * X ^ 4 + (6109) * X ^ 5 + (-7275) * X ^ 6 : PowerSeries ℚ) * AA + ((4759) * X ^ 1 + (-10890) * X ^ 2 + (-5810) * X ^ 3 + (13574) * X ^ 4 + (-10074) * X ^ 5 + (1166) * X ^ 6 + (7275) * X ^ 7 : PowerSeries ℚ) * derivative ℚ AA + ((-1390) * X ^ 2 + (4884) * X ^ 3 + (60) * X ^ 4 + (-5080) * X ^ 5 + (-8476) * X ^ 6 + (-3652) * X ^ 7 + (2878) * X ^ 8 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) = ((23795) * X ^ 3 + (16511) * X ^ 4 + (-11479) * X ^ 5 + (-7275) * X ^ 6 : PowerSeries ℚ) := by
  have e1 := ode1 S AA hS hA
  have e2 := ode2 S AA hS hA
  have e3 := ode3' S AA hS hA
  have hK : (((1) * X ^ 1 + (-4) * X ^ 2 + (2) * X ^ 3 + (3) * X ^ 4 + (4) * X ^ 5 + (-5) * X ^ 7 + (-2) * X ^ 9 + (1) * X ^ 10 : PowerSeries ℚ) ^ 3 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((1) * X ^ 0 + (-12) * X ^ 1 + (54) * X ^ 2 + (-103) * X ^ 3 + (48) * X ^ 4 + (36) * X ^ 5 + (116) * X ^ 6 + (-72) * X ^ 7 + (-444) * X ^ 8 + (180) * X ^ 9 + (240) * X ^ 10 + (564) * X ^ 11 + (-194) * X ^ 12 + (-576) * X ^ 13 + (-240) * X ^ 14 + (-114) * X ^ 15 + (528) * X ^ 16 + (108) * X ^ 17 + (100) * X ^ 18 + (-120) * X ^ 19 + (-132) * X ^ 20 + (36) * X ^ 21 + (-48) * X ^ 22 + (60) * X ^ 23 + (-23) * X ^ 24 + (12) * X ^ 25 + (-6) * X ^ 26 + (1) * X ^ 27 : PowerSeries ℚ)) 3 (by ring) (by simp <;> norm_num)
  apply mul_left_cancel₀ hK
  linear_combination (((0) * X ^ 0 : PowerSeries ℚ)) * e3 + (((-1390) * X ^ 4 + (16004) * X ^ 5 + (-66812) * X ^ 6 + (106020) * X ^ 7 + (1204) * X ^ 8 + (-68852) * X ^ 9 + (-205876) * X ^ 10 + (32756) * X ^ 11 + (621988) * X ^ 12 + (89812) * X ^ 13 + (-395004) * X ^ 14 + (-877268) * X ^ 15 + (-125072) * X ^ 16 + (661260) * X ^ 17 + (548268) * X ^ 18 + (273644) * X ^ 19 + (-352932) * X ^ 20 + (-222716) * X ^ 21 + (-125452) * X ^ 22 + (19068) * X ^ 23 + (80556) * X ^ 24 + (-14564) * X ^ 25 + (17644) * X ^ 26 + (-15164) * X ^ 27 + (2878) * X ^ 28 : PowerSeries ℚ)) * e2 + (((8929) * X ^ 3 + (-101144) * X ^ 4 + (412428) * X ^ 5 + (-621496) * X ^ 6 + (-85724) * X ^ 7 + (456732) * X ^ 8 + (1265304) * X ^ 9 + (-27888) * X ^ 10 + (-3897428) * X ^ 11 + (-790784) * X ^ 12 + (2371788) * X ^ 13 + (5423052) * X ^ 14 + (1148202) * X ^ 15 + (-4103960) * X ^ 16 + (-3393404) * X ^ 17 + (-1854552) * X ^ 18 + (2114748) * X ^ 19 + (1449044) * X ^ 20 + (748960) * X ^ 21 + (-42976) * X ^ 22 + (-550332) * X ^ 23 + (114064) * X ^ 24 + (-124844) * X ^ 25 + (99908) * X ^ 26 + (-18627) * X ^ 27 : PowerSeries ℚ)) * e1

set_option maxHeartbeats 4000000 in
lemma rec_a (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) (k : ℕ) : (-1390*((k + 7 : ℕ) : ℚ)^2 + 6149*((k + 7 : ℕ) : ℚ) + 17858) * coeff (k + 7) AA + (4884*((k + 7 : ℕ) : ℚ)^2 - 25542*((k + 7 : ℕ) : ℚ) - 20107) * coeff (k + 6) AA + (60*((k + 7 : ℕ) : ℚ)^2 - 6110*((k + 7 : ℕ) : ℚ) - 2249) * coeff (k + 5) AA + (-5080*((k + 7 : ℕ) : ℚ)^2 + 49134*((k + 7 : ℕ) : ℚ) - 115735) * coeff (k + 4) AA + (-8476*((k + 7 : ℕ) : ℚ)^2 + 66210*((k + 7 : ℕ) : ℚ) - 98877) * coeff (k + 3) AA + (-3652*((k + 7 : ℕ) : ℚ)^2 + 41338*((k + 7 : ℕ) : ℚ) - 109281) * coeff (k + 2) AA + (2878*((k + 7 : ℕ) : ℚ)^2 - 30139*((k + 7 : ℕ) : ℚ) + 69951) * coeff (k + 1) AA = 0 := by
  have h := congrArg (coeff (k + 7)) (ode3 S AA hS hA)
  rcases k with _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm14, cm15, cm16, cm17, cm18, cm19, cm20, cm21, cm22, cm23, cm24, cm25, cm26, cm27, cm28, cm30, cm33, cm35, cm36, cm49, cm55, cm56, cm60, cm64, cm72, cm80, cm90, cm120, cm126, cm144, cm168, cm192, cm210, cm220, cm294, cm1166, cm1204, cm1390, cm2249, cm2878, cm3652, cm4759, cm4884, cm5080, cm5810, cm6109, cm6110, cm6149, cm7275, cm8476, cm8929, cm10074, cm10890, cm11479, cm13574, cm14053, cm14229, cm14564, cm15164, cm16004, cm16511, cm17644, cm17858, cm18627, cm19068, cm20107, cm23795, cm25542, cm27888, cm30139, cm30347, cm32756, cm40765, cm41338, cm42976, cm49134, cm66210, cm66812, cm68852, cm69951, cm80556, cm85724, cm89812, cm98877, cm99908, cm101144, cm106020, cm109281, cm114064, cm115735, cm124844, cm125072, cm125452, cm205876, cm222716, cm273644, cm352932, cm395004, cm412428, cm456732, cm548268, cm550332, cm621496, cm621988, cm661260, cm748960, cm790784, cm877268, cm1148202, cm1265304, cm1449044, cm1854552, cm2114748, cm2371788, cm3393404, cm3897428, cm4103960, cm5423052, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h


end OMA.S_oeis_a171854

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a171854.main := by
  intro T G hT hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  have hS : (2 * X ^ 2 * T + (X - X ^ 2 - 1)) * (2 * X ^ 2 * T + (X - X ^ 2 - 1)) = OMA.S_oeis_a171854.R := by
    unfold OMA.S_oeis_a171854.R; linear_combination (-4 * X ^ 2) * hT
  have hA : G * OMA.S_oeis_a171854.DD = OMA.S_oeis_a171854.NN (2 * X ^ 2 * T + (X - X ^ 2 - 1)) := by
    unfold OMA.S_oeis_a171854.DD OMA.S_oeis_a171854.NN
    linear_combination (1 * 2 * X ^ 2 * (T * X ^ 4 - T * X ^ 3 + T * X ^ 2 - X ^ 4 + 2 * X ^ 3 - X ^ 2 + 2 * X - 1)) * hG + (-(1 * 2 * X ^ 2) * (G * (T * (X ^ 4 - X ^ 3 + X ^ 2) + 2 * X ^ 2) + (-T ^ 2 * X ^ 6 + T ^ 2 * X ^ 5 - T ^ 2 * X ^ 3 + T ^ 2 * X ^ 2 + T * X ^ 6 - T * X ^ 5 - 2 * T * X ^ 4 + T * X ^ 3 + T * X ^ 2 + X ^ 4 + X ^ 3 - 2 * X ^ 2 - X + 1))) * hT
  have h := OMA.S_oeis_a171854.rec_a _ G hS hA k
  simp only [show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 7 - 5 = k + 2 from by omega, show k + 7 - 6 = k + 1 from by omega]
  push_cast at h ⊢
  linear_combination h
