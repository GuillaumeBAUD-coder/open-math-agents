import OMAStatements.S_oeis_a134424
import Mathlib

namespace OMA.S_oeis_a134424

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
@[simp] lemma dn29 : derivative ℚ (29 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 29
@[simp] lemma cc29 : constantCoeff (29 : PowerSeries ℚ) = 29 := by simpa using map_natCast (constantCoeff (R := ℚ)) 29
lemma cm29 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((29 : PowerSeries ℚ) * F) = 29 * coeff m F := by
  have e : (29 : PowerSeries ℚ) = C (29 : ℚ) := (map_ofNat C 29).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30 : derivative ℚ (30 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30
@[simp] lemma cc30 : constantCoeff (30 : PowerSeries ℚ) = 30 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30
lemma cm30 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30 : PowerSeries ℚ) * F) = 30 * coeff m F := by
  have e : (30 : PowerSeries ℚ) = C (30 : ℚ) := (map_ofNat C 30).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn31 : derivative ℚ (31 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 31
@[simp] lemma cc31 : constantCoeff (31 : PowerSeries ℚ) = 31 := by simpa using map_natCast (constantCoeff (R := ℚ)) 31
lemma cm31 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((31 : PowerSeries ℚ) * F) = 31 * coeff m F := by
  have e : (31 : PowerSeries ℚ) = C (31 : ℚ) := (map_ofNat C 31).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32 : derivative ℚ (32 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32
@[simp] lemma cc32 : constantCoeff (32 : PowerSeries ℚ) = 32 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32
lemma cm32 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32 : PowerSeries ℚ) * F) = 32 * coeff m F := by
  have e : (32 : PowerSeries ℚ) = C (32 : ℚ) := (map_ofNat C 32).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn33 : derivative ℚ (33 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 33
@[simp] lemma cc33 : constantCoeff (33 : PowerSeries ℚ) = 33 := by simpa using map_natCast (constantCoeff (R := ℚ)) 33
lemma cm33 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((33 : PowerSeries ℚ) * F) = 33 * coeff m F := by
  have e : (33 : PowerSeries ℚ) = C (33 : ℚ) := (map_ofNat C 33).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn34 : derivative ℚ (34 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 34
@[simp] lemma cc34 : constantCoeff (34 : PowerSeries ℚ) = 34 := by simpa using map_natCast (constantCoeff (R := ℚ)) 34
lemma cm34 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((34 : PowerSeries ℚ) * F) = 34 * coeff m F := by
  have e : (34 : PowerSeries ℚ) = C (34 : ℚ) := (map_ofNat C 34).symm
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
@[simp] lemma dn37 : derivative ℚ (37 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 37
@[simp] lemma cc37 : constantCoeff (37 : PowerSeries ℚ) = 37 := by simpa using map_natCast (constantCoeff (R := ℚ)) 37
lemma cm37 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((37 : PowerSeries ℚ) * F) = 37 * coeff m F := by
  have e : (37 : PowerSeries ℚ) = C (37 : ℚ) := (map_ofNat C 37).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn38 : derivative ℚ (38 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 38
@[simp] lemma cc38 : constantCoeff (38 : PowerSeries ℚ) = 38 := by simpa using map_natCast (constantCoeff (R := ℚ)) 38
lemma cm38 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((38 : PowerSeries ℚ) * F) = 38 * coeff m F := by
  have e : (38 : PowerSeries ℚ) = C (38 : ℚ) := (map_ofNat C 38).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40 : derivative ℚ (40 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40
@[simp] lemma cc40 : constantCoeff (40 : PowerSeries ℚ) = 40 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40
lemma cm40 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40 : PowerSeries ℚ) * F) = 40 * coeff m F := by
  have e : (40 : PowerSeries ℚ) = C (40 : ℚ) := (map_ofNat C 40).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn42 : derivative ℚ (42 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 42
@[simp] lemma cc42 : constantCoeff (42 : PowerSeries ℚ) = 42 := by simpa using map_natCast (constantCoeff (R := ℚ)) 42
lemma cm42 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((42 : PowerSeries ℚ) * F) = 42 * coeff m F := by
  have e : (42 : PowerSeries ℚ) = C (42 : ℚ) := (map_ofNat C 42).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn43 : derivative ℚ (43 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 43
@[simp] lemma cc43 : constantCoeff (43 : PowerSeries ℚ) = 43 := by simpa using map_natCast (constantCoeff (R := ℚ)) 43
lemma cm43 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((43 : PowerSeries ℚ) * F) = 43 * coeff m F := by
  have e : (43 : PowerSeries ℚ) = C (43 : ℚ) := (map_ofNat C 43).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn45 : derivative ℚ (45 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 45
@[simp] lemma cc45 : constantCoeff (45 : PowerSeries ℚ) = 45 := by simpa using map_natCast (constantCoeff (R := ℚ)) 45
lemma cm45 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((45 : PowerSeries ℚ) * F) = 45 * coeff m F := by
  have e : (45 : PowerSeries ℚ) = C (45 : ℚ) := (map_ofNat C 45).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn48 : derivative ℚ (48 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 48
@[simp] lemma cc48 : constantCoeff (48 : PowerSeries ℚ) = 48 := by simpa using map_natCast (constantCoeff (R := ℚ)) 48
lemma cm48 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((48 : PowerSeries ℚ) * F) = 48 * coeff m F := by
  have e : (48 : PowerSeries ℚ) = C (48 : ℚ) := (map_ofNat C 48).symm
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
@[simp] lemma dn72 : derivative ℚ (72 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72
@[simp] lemma cc72 : constantCoeff (72 : PowerSeries ℚ) = 72 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72
lemma cm72 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72 : PowerSeries ℚ) * F) = 72 * coeff m F := by
  have e : (72 : PowerSeries ℚ) = C (72 : ℚ) := (map_ofNat C 72).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn76 : derivative ℚ (76 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 76
@[simp] lemma cc76 : constantCoeff (76 : PowerSeries ℚ) = 76 := by simpa using map_natCast (constantCoeff (R := ℚ)) 76
lemma cm76 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((76 : PowerSeries ℚ) * F) = 76 * coeff m F := by
  have e : (76 : PowerSeries ℚ) = C (76 : ℚ) := (map_ofNat C 76).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80 : derivative ℚ (80 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80
@[simp] lemma cc80 : constantCoeff (80 : PowerSeries ℚ) = 80 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80
lemma cm80 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80 : PowerSeries ℚ) * F) = 80 * coeff m F := by
  have e : (80 : PowerSeries ℚ) = C (80 : ℚ) := (map_ofNat C 80).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn83 : derivative ℚ (83 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 83
@[simp] lemma cc83 : constantCoeff (83 : PowerSeries ℚ) = 83 := by simpa using map_natCast (constantCoeff (R := ℚ)) 83
lemma cm83 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((83 : PowerSeries ℚ) * F) = 83 * coeff m F := by
  have e : (83 : PowerSeries ℚ) = C (83 : ℚ) := (map_ofNat C 83).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn107 : derivative ℚ (107 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 107
@[simp] lemma cc107 : constantCoeff (107 : PowerSeries ℚ) = 107 := by simpa using map_natCast (constantCoeff (R := ℚ)) 107
lemma cm107 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((107 : PowerSeries ℚ) * F) = 107 * coeff m F := by
  have e : (107 : PowerSeries ℚ) = C (107 : ℚ) := (map_ofNat C 107).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn116 : derivative ℚ (116 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 116
@[simp] lemma cc116 : constantCoeff (116 : PowerSeries ℚ) = 116 := by simpa using map_natCast (constantCoeff (R := ℚ)) 116
lemma cm116 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((116 : PowerSeries ℚ) * F) = 116 * coeff m F := by
  have e : (116 : PowerSeries ℚ) = C (116 : ℚ) := (map_ofNat C 116).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn122 : derivative ℚ (122 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 122
@[simp] lemma cc122 : constantCoeff (122 : PowerSeries ℚ) = 122 := by simpa using map_natCast (constantCoeff (R := ℚ)) 122
lemma cm122 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((122 : PowerSeries ℚ) * F) = 122 * coeff m F := by
  have e : (122 : PowerSeries ℚ) = C (122 : ℚ) := (map_ofNat C 122).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn126 : derivative ℚ (126 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 126
@[simp] lemma cc126 : constantCoeff (126 : PowerSeries ℚ) = 126 := by simpa using map_natCast (constantCoeff (R := ℚ)) 126
lemma cm126 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((126 : PowerSeries ℚ) * F) = 126 * coeff m F := by
  have e : (126 : PowerSeries ℚ) = C (126 : ℚ) := (map_ofNat C 126).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn127 : derivative ℚ (127 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 127
@[simp] lemma cc127 : constantCoeff (127 : PowerSeries ℚ) = 127 := by simpa using map_natCast (constantCoeff (R := ℚ)) 127
lemma cm127 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((127 : PowerSeries ℚ) * F) = 127 * coeff m F := by
  have e : (127 : PowerSeries ℚ) = C (127 : ℚ) := (map_ofNat C 127).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn135 : derivative ℚ (135 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 135
@[simp] lemma cc135 : constantCoeff (135 : PowerSeries ℚ) = 135 := by simpa using map_natCast (constantCoeff (R := ℚ)) 135
lemma cm135 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((135 : PowerSeries ℚ) * F) = 135 * coeff m F := by
  have e : (135 : PowerSeries ℚ) = C (135 : ℚ) := (map_ofNat C 135).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn137 : derivative ℚ (137 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 137
@[simp] lemma cc137 : constantCoeff (137 : PowerSeries ℚ) = 137 := by simpa using map_natCast (constantCoeff (R := ℚ)) 137
lemma cm137 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((137 : PowerSeries ℚ) * F) = 137 * coeff m F := by
  have e : (137 : PowerSeries ℚ) = C (137 : ℚ) := (map_ofNat C 137).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn144 : derivative ℚ (144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 144
@[simp] lemma cc144 : constantCoeff (144 : PowerSeries ℚ) = 144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 144
lemma cm144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((144 : PowerSeries ℚ) * F) = 144 * coeff m F := by
  have e : (144 : PowerSeries ℚ) = C (144 : ℚ) := (map_ofNat C 144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn156 : derivative ℚ (156 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 156
@[simp] lemma cc156 : constantCoeff (156 : PowerSeries ℚ) = 156 := by simpa using map_natCast (constantCoeff (R := ℚ)) 156
lemma cm156 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((156 : PowerSeries ℚ) * F) = 156 * coeff m F := by
  have e : (156 : PowerSeries ℚ) = C (156 : ℚ) := (map_ofNat C 156).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn162 : derivative ℚ (162 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 162
@[simp] lemma cc162 : constantCoeff (162 : PowerSeries ℚ) = 162 := by simpa using map_natCast (constantCoeff (R := ℚ)) 162
lemma cm162 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((162 : PowerSeries ℚ) * F) = 162 * coeff m F := by
  have e : (162 : PowerSeries ℚ) = C (162 : ℚ) := (map_ofNat C 162).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn168 : derivative ℚ (168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 168
@[simp] lemma cc168 : constantCoeff (168 : PowerSeries ℚ) = 168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 168
lemma cm168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((168 : PowerSeries ℚ) * F) = 168 * coeff m F := by
  have e : (168 : PowerSeries ℚ) = C (168 : ℚ) := (map_ofNat C 168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn180 : derivative ℚ (180 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 180
@[simp] lemma cc180 : constantCoeff (180 : PowerSeries ℚ) = 180 := by simpa using map_natCast (constantCoeff (R := ℚ)) 180
lemma cm180 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((180 : PowerSeries ℚ) * F) = 180 * coeff m F := by
  have e : (180 : PowerSeries ℚ) = C (180 : ℚ) := (map_ofNat C 180).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn192 : derivative ℚ (192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 192
@[simp] lemma cc192 : constantCoeff (192 : PowerSeries ℚ) = 192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 192
lemma cm192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((192 : PowerSeries ℚ) * F) = 192 * coeff m F := by
  have e : (192 : PowerSeries ℚ) = C (192 : ℚ) := (map_ofNat C 192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn198 : derivative ℚ (198 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 198
@[simp] lemma cc198 : constantCoeff (198 : PowerSeries ℚ) = 198 := by simpa using map_natCast (constantCoeff (R := ℚ)) 198
lemma cm198 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((198 : PowerSeries ℚ) * F) = 198 * coeff m F := by
  have e : (198 : PowerSeries ℚ) = C (198 : ℚ) := (map_ofNat C 198).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn204 : derivative ℚ (204 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 204
@[simp] lemma cc204 : constantCoeff (204 : PowerSeries ℚ) = 204 := by simpa using map_natCast (constantCoeff (R := ℚ)) 204
lemma cm204 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((204 : PowerSeries ℚ) * F) = 204 * coeff m F := by
  have e : (204 : PowerSeries ℚ) = C (204 : ℚ) := (map_ofNat C 204).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn216 : derivative ℚ (216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 216
@[simp] lemma cc216 : constantCoeff (216 : PowerSeries ℚ) = 216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 216
lemma cm216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((216 : PowerSeries ℚ) * F) = 216 * coeff m F := by
  have e : (216 : PowerSeries ℚ) = C (216 : ℚ) := (map_ofNat C 216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn220 : derivative ℚ (220 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 220
@[simp] lemma cc220 : constantCoeff (220 : PowerSeries ℚ) = 220 := by simpa using map_natCast (constantCoeff (R := ℚ)) 220
lemma cm220 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((220 : PowerSeries ℚ) * F) = 220 * coeff m F := by
  have e : (220 : PowerSeries ℚ) = C (220 : ℚ) := (map_ofNat C 220).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn224 : derivative ℚ (224 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 224
@[simp] lemma cc224 : constantCoeff (224 : PowerSeries ℚ) = 224 := by simpa using map_natCast (constantCoeff (R := ℚ)) 224
lemma cm224 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((224 : PowerSeries ℚ) * F) = 224 * coeff m F := by
  have e : (224 : PowerSeries ℚ) = C (224 : ℚ) := (map_ofNat C 224).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn228 : derivative ℚ (228 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 228
@[simp] lemma cc228 : constantCoeff (228 : PowerSeries ℚ) = 228 := by simpa using map_natCast (constantCoeff (R := ℚ)) 228
lemma cm228 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((228 : PowerSeries ℚ) * F) = 228 * coeff m F := by
  have e : (228 : PowerSeries ℚ) = C (228 : ℚ) := (map_ofNat C 228).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn235 : derivative ℚ (235 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 235
@[simp] lemma cc235 : constantCoeff (235 : PowerSeries ℚ) = 235 := by simpa using map_natCast (constantCoeff (R := ℚ)) 235
lemma cm235 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((235 : PowerSeries ℚ) * F) = 235 * coeff m F := by
  have e : (235 : PowerSeries ℚ) = C (235 : ℚ) := (map_ofNat C 235).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn244 : derivative ℚ (244 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 244
@[simp] lemma cc244 : constantCoeff (244 : PowerSeries ℚ) = 244 := by simpa using map_natCast (constantCoeff (R := ℚ)) 244
lemma cm244 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((244 : PowerSeries ℚ) * F) = 244 * coeff m F := by
  have e : (244 : PowerSeries ℚ) = C (244 : ℚ) := (map_ofNat C 244).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn264 : derivative ℚ (264 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 264
@[simp] lemma cc264 : constantCoeff (264 : PowerSeries ℚ) = 264 := by simpa using map_natCast (constantCoeff (R := ℚ)) 264
lemma cm264 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((264 : PowerSeries ℚ) * F) = 264 * coeff m F := by
  have e : (264 : PowerSeries ℚ) = C (264 : ℚ) := (map_ofNat C 264).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn272 : derivative ℚ (272 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 272
@[simp] lemma cc272 : constantCoeff (272 : PowerSeries ℚ) = 272 := by simpa using map_natCast (constantCoeff (R := ℚ)) 272
lemma cm272 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((272 : PowerSeries ℚ) * F) = 272 * coeff m F := by
  have e : (272 : PowerSeries ℚ) = C (272 : ℚ) := (map_ofNat C 272).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn288 : derivative ℚ (288 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 288
@[simp] lemma cc288 : constantCoeff (288 : PowerSeries ℚ) = 288 := by simpa using map_natCast (constantCoeff (R := ℚ)) 288
lemma cm288 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((288 : PowerSeries ℚ) * F) = 288 * coeff m F := by
  have e : (288 : PowerSeries ℚ) = C (288 : ℚ) := (map_ofNat C 288).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn290 : derivative ℚ (290 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 290
@[simp] lemma cc290 : constantCoeff (290 : PowerSeries ℚ) = 290 := by simpa using map_natCast (constantCoeff (R := ℚ)) 290
lemma cm290 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((290 : PowerSeries ℚ) * F) = 290 * coeff m F := by
  have e : (290 : PowerSeries ℚ) = C (290 : ℚ) := (map_ofNat C 290).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn324 : derivative ℚ (324 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 324
@[simp] lemma cc324 : constantCoeff (324 : PowerSeries ℚ) = 324 := by simpa using map_natCast (constantCoeff (R := ℚ)) 324
lemma cm324 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((324 : PowerSeries ℚ) * F) = 324 * coeff m F := by
  have e : (324 : PowerSeries ℚ) = C (324 : ℚ) := (map_ofNat C 324).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn330 : derivative ℚ (330 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 330
@[simp] lemma cc330 : constantCoeff (330 : PowerSeries ℚ) = 330 := by simpa using map_natCast (constantCoeff (R := ℚ)) 330
lemma cm330 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((330 : PowerSeries ℚ) * F) = 330 * coeff m F := by
  have e : (330 : PowerSeries ℚ) = C (330 : ℚ) := (map_ofNat C 330).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn348 : derivative ℚ (348 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 348
@[simp] lemma cc348 : constantCoeff (348 : PowerSeries ℚ) = 348 := by simpa using map_natCast (constantCoeff (R := ℚ)) 348
lemma cm348 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((348 : PowerSeries ℚ) * F) = 348 * coeff m F := by
  have e : (348 : PowerSeries ℚ) = C (348 : ℚ) := (map_ofNat C 348).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn360 : derivative ℚ (360 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 360
@[simp] lemma cc360 : constantCoeff (360 : PowerSeries ℚ) = 360 := by simpa using map_natCast (constantCoeff (R := ℚ)) 360
lemma cm360 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((360 : PowerSeries ℚ) * F) = 360 * coeff m F := by
  have e : (360 : PowerSeries ℚ) = C (360 : ℚ) := (map_ofNat C 360).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn390 : derivative ℚ (390 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 390
@[simp] lemma cc390 : constantCoeff (390 : PowerSeries ℚ) = 390 := by simpa using map_natCast (constantCoeff (R := ℚ)) 390
lemma cm390 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((390 : PowerSeries ℚ) * F) = 390 * coeff m F := by
  have e : (390 : PowerSeries ℚ) = C (390 : ℚ) := (map_ofNat C 390).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn420 : derivative ℚ (420 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 420
@[simp] lemma cc420 : constantCoeff (420 : PowerSeries ℚ) = 420 := by simpa using map_natCast (constantCoeff (R := ℚ)) 420
lemma cm420 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((420 : PowerSeries ℚ) * F) = 420 * coeff m F := by
  have e : (420 : PowerSeries ℚ) = C (420 : ℚ) := (map_ofNat C 420).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn456 : derivative ℚ (456 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 456
@[simp] lemma cc456 : constantCoeff (456 : PowerSeries ℚ) = 456 := by simpa using map_natCast (constantCoeff (R := ℚ)) 456
lemma cm456 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((456 : PowerSeries ℚ) * F) = 456 * coeff m F := by
  have e : (456 : PowerSeries ℚ) = C (456 : ℚ) := (map_ofNat C 456).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn477 : derivative ℚ (477 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 477
@[simp] lemma cc477 : constantCoeff (477 : PowerSeries ℚ) = 477 := by simpa using map_natCast (constantCoeff (R := ℚ)) 477
lemma cm477 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((477 : PowerSeries ℚ) * F) = 477 * coeff m F := by
  have e : (477 : PowerSeries ℚ) = C (477 : ℚ) := (map_ofNat C 477).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn480 : derivative ℚ (480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 480
@[simp] lemma cc480 : constantCoeff (480 : PowerSeries ℚ) = 480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 480
lemma cm480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((480 : PowerSeries ℚ) * F) = 480 * coeff m F := by
  have e : (480 : PowerSeries ℚ) = C (480 : ℚ) := (map_ofNat C 480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn540 : derivative ℚ (540 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 540
@[simp] lemma cc540 : constantCoeff (540 : PowerSeries ℚ) = 540 := by simpa using map_natCast (constantCoeff (R := ℚ)) 540
lemma cm540 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((540 : PowerSeries ℚ) * F) = 540 * coeff m F := by
  have e : (540 : PowerSeries ℚ) = C (540 : ℚ) := (map_ofNat C 540).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn550 : derivative ℚ (550 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 550
@[simp] lemma cc550 : constantCoeff (550 : PowerSeries ℚ) = 550 := by simpa using map_natCast (constantCoeff (R := ℚ)) 550
lemma cm550 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((550 : PowerSeries ℚ) * F) = 550 * coeff m F := by
  have e : (550 : PowerSeries ℚ) = C (550 : ℚ) := (map_ofNat C 550).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn608 : derivative ℚ (608 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 608
@[simp] lemma cc608 : constantCoeff (608 : PowerSeries ℚ) = 608 := by simpa using map_natCast (constantCoeff (R := ℚ)) 608
lemma cm608 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((608 : PowerSeries ℚ) * F) = 608 * coeff m F := by
  have e : (608 : PowerSeries ℚ) = C (608 : ℚ) := (map_ofNat C 608).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn630 : derivative ℚ (630 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 630
@[simp] lemma cc630 : constantCoeff (630 : PowerSeries ℚ) = 630 := by simpa using map_natCast (constantCoeff (R := ℚ)) 630
lemma cm630 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((630 : PowerSeries ℚ) * F) = 630 * coeff m F := by
  have e : (630 : PowerSeries ℚ) = C (630 : ℚ) := (map_ofNat C 630).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn655 : derivative ℚ (655 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 655
@[simp] lemma cc655 : constantCoeff (655 : PowerSeries ℚ) = 655 := by simpa using map_natCast (constantCoeff (R := ℚ)) 655
lemma cm655 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((655 : PowerSeries ℚ) * F) = 655 * coeff m F := by
  have e : (655 : PowerSeries ℚ) = C (655 : ℚ) := (map_ofNat C 655).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn660 : derivative ℚ (660 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 660
@[simp] lemma cc660 : constantCoeff (660 : PowerSeries ℚ) = 660 := by simpa using map_natCast (constantCoeff (R := ℚ)) 660
lemma cm660 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((660 : PowerSeries ℚ) * F) = 660 * coeff m F := by
  have e : (660 : PowerSeries ℚ) = C (660 : ℚ) := (map_ofNat C 660).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn705 : derivative ℚ (705 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 705
@[simp] lemma cc705 : constantCoeff (705 : PowerSeries ℚ) = 705 := by simpa using map_natCast (constantCoeff (R := ℚ)) 705
lemma cm705 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((705 : PowerSeries ℚ) * F) = 705 * coeff m F := by
  have e : (705 : PowerSeries ℚ) = C (705 : ℚ) := (map_ofNat C 705).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn725 : derivative ℚ (725 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 725
@[simp] lemma cc725 : constantCoeff (725 : PowerSeries ℚ) = 725 := by simpa using map_natCast (constantCoeff (R := ℚ)) 725
lemma cm725 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((725 : PowerSeries ℚ) * F) = 725 * coeff m F := by
  have e : (725 : PowerSeries ℚ) = C (725 : ℚ) := (map_ofNat C 725).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn742 : derivative ℚ (742 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 742
@[simp] lemma cc742 : constantCoeff (742 : PowerSeries ℚ) = 742 := by simpa using map_natCast (constantCoeff (R := ℚ)) 742
lemma cm742 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((742 : PowerSeries ℚ) * F) = 742 * coeff m F := by
  have e : (742 : PowerSeries ℚ) = C (742 : ℚ) := (map_ofNat C 742).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn756 : derivative ℚ (756 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 756
@[simp] lemma cc756 : constantCoeff (756 : PowerSeries ℚ) = 756 := by simpa using map_natCast (constantCoeff (R := ℚ)) 756
lemma cm756 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((756 : PowerSeries ℚ) * F) = 756 * coeff m F := by
  have e : (756 : PowerSeries ℚ) = C (756 : ℚ) := (map_ofNat C 756).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn783 : derivative ℚ (783 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 783
@[simp] lemma cc783 : constantCoeff (783 : PowerSeries ℚ) = 783 := by simpa using map_natCast (constantCoeff (R := ℚ)) 783
lemma cm783 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((783 : PowerSeries ℚ) * F) = 783 * coeff m F := by
  have e : (783 : PowerSeries ℚ) = C (783 : ℚ) := (map_ofNat C 783).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn790 : derivative ℚ (790 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 790
@[simp] lemma cc790 : constantCoeff (790 : PowerSeries ℚ) = 790 := by simpa using map_natCast (constantCoeff (R := ℚ)) 790
lemma cm790 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((790 : PowerSeries ℚ) * F) = 790 * coeff m F := by
  have e : (790 : PowerSeries ℚ) = C (790 : ℚ) := (map_ofNat C 790).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn812 : derivative ℚ (812 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 812
@[simp] lemma cc812 : constantCoeff (812 : PowerSeries ℚ) = 812 := by simpa using map_natCast (constantCoeff (R := ℚ)) 812
lemma cm812 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((812 : PowerSeries ℚ) * F) = 812 * coeff m F := by
  have e : (812 : PowerSeries ℚ) = C (812 : ℚ) := (map_ofNat C 812).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn900 : derivative ℚ (900 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 900
@[simp] lemma cc900 : constantCoeff (900 : PowerSeries ℚ) = 900 := by simpa using map_natCast (constantCoeff (R := ℚ)) 900
lemma cm900 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((900 : PowerSeries ℚ) * F) = 900 * coeff m F := by
  have e : (900 : PowerSeries ℚ) = C (900 : ℚ) := (map_ofNat C 900).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn990 : derivative ℚ (990 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 990
@[simp] lemma cc990 : constantCoeff (990 : PowerSeries ℚ) = 990 := by simpa using map_natCast (constantCoeff (R := ℚ)) 990
lemma cm990 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((990 : PowerSeries ℚ) * F) = 990 * coeff m F := by
  have e : (990 : PowerSeries ℚ) = C (990 : ℚ) := (map_ofNat C 990).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1008 : derivative ℚ (1008 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1008
@[simp] lemma cc1008 : constantCoeff (1008 : PowerSeries ℚ) = 1008 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1008
lemma cm1008 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1008 : PowerSeries ℚ) * F) = 1008 * coeff m F := by
  have e : (1008 : PowerSeries ℚ) = C (1008 : ℚ) := (map_ofNat C 1008).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1173 : derivative ℚ (1173 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1173
@[simp] lemma cc1173 : constantCoeff (1173 : PowerSeries ℚ) = 1173 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1173
lemma cm1173 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1173 : PowerSeries ℚ) * F) = 1173 * coeff m F := by
  have e : (1173 : PowerSeries ℚ) = C (1173 : ℚ) := (map_ofNat C 1173).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1248 : derivative ℚ (1248 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1248
@[simp] lemma cc1248 : constantCoeff (1248 : PowerSeries ℚ) = 1248 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1248
lemma cm1248 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1248 : PowerSeries ℚ) * F) = 1248 * coeff m F := by
  have e : (1248 : PowerSeries ℚ) = C (1248 : ℚ) := (map_ofNat C 1248).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1296 : derivative ℚ (1296 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1296
@[simp] lemma cc1296 : constantCoeff (1296 : PowerSeries ℚ) = 1296 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1296
lemma cm1296 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1296 : PowerSeries ℚ) * F) = 1296 * coeff m F := by
  have e : (1296 : PowerSeries ℚ) = C (1296 : ℚ) := (map_ofNat C 1296).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1408 : derivative ℚ (1408 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1408
@[simp] lemma cc1408 : constantCoeff (1408 : PowerSeries ℚ) = 1408 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1408
lemma cm1408 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1408 : PowerSeries ℚ) * F) = 1408 * coeff m F := by
  have e : (1408 : PowerSeries ℚ) = C (1408 : ℚ) := (map_ofNat C 1408).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1505 : derivative ℚ (1505 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1505
@[simp] lemma cc1505 : constantCoeff (1505 : PowerSeries ℚ) = 1505 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1505
lemma cm1505 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1505 : PowerSeries ℚ) * F) = 1505 * coeff m F := by
  have e : (1505 : PowerSeries ℚ) = C (1505 : ℚ) := (map_ofNat C 1505).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1584 : derivative ℚ (1584 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1584
@[simp] lemma cc1584 : constantCoeff (1584 : PowerSeries ℚ) = 1584 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1584
lemma cm1584 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1584 : PowerSeries ℚ) * F) = 1584 * coeff m F := by
  have e : (1584 : PowerSeries ℚ) = C (1584 : ℚ) := (map_ofNat C 1584).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1776 : derivative ℚ (1776 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1776
@[simp] lemma cc1776 : constantCoeff (1776 : PowerSeries ℚ) = 1776 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1776
lemma cm1776 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1776 : PowerSeries ℚ) * F) = 1776 * coeff m F := by
  have e : (1776 : PowerSeries ℚ) = C (1776 : ℚ) := (map_ofNat C 1776).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1835 : derivative ℚ (1835 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1835
@[simp] lemma cc1835 : constantCoeff (1835 : PowerSeries ℚ) = 1835 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1835
lemma cm1835 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1835 : PowerSeries ℚ) * F) = 1835 * coeff m F := by
  have e : (1835 : PowerSeries ℚ) = C (1835 : ℚ) := (map_ofNat C 1835).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1848 : derivative ℚ (1848 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1848
@[simp] lemma cc1848 : constantCoeff (1848 : PowerSeries ℚ) = 1848 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1848
lemma cm1848 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1848 : PowerSeries ℚ) * F) = 1848 * coeff m F := by
  have e : (1848 : PowerSeries ℚ) = C (1848 : ℚ) := (map_ofNat C 1848).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1880 : derivative ℚ (1880 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1880
@[simp] lemma cc1880 : constantCoeff (1880 : PowerSeries ℚ) = 1880 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1880
lemma cm1880 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1880 : PowerSeries ℚ) * F) = 1880 * coeff m F := by
  have e : (1880 : PowerSeries ℚ) = C (1880 : ℚ) := (map_ofNat C 1880).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2352 : derivative ℚ (2352 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2352
@[simp] lemma cc2352 : constantCoeff (2352 : PowerSeries ℚ) = 2352 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2352
lemma cm2352 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2352 : PowerSeries ℚ) * F) = 2352 * coeff m F := by
  have e : (2352 : PowerSeries ℚ) = C (2352 : ℚ) := (map_ofNat C 2352).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2430 : derivative ℚ (2430 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2430
@[simp] lemma cc2430 : constantCoeff (2430 : PowerSeries ℚ) = 2430 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2430
lemma cm2430 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2430 : PowerSeries ℚ) * F) = 2430 * coeff m F := by
  have e : (2430 : PowerSeries ℚ) = C (2430 : ℚ) := (map_ofNat C 2430).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2520 : derivative ℚ (2520 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2520
@[simp] lemma cc2520 : constantCoeff (2520 : PowerSeries ℚ) = 2520 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2520
lemma cm2520 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2520 : PowerSeries ℚ) * F) = 2520 * coeff m F := by
  have e : (2520 : PowerSeries ℚ) = C (2520 : ℚ) := (map_ofNat C 2520).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2610 : derivative ℚ (2610 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2610
@[simp] lemma cc2610 : constantCoeff (2610 : PowerSeries ℚ) = 2610 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2610
lemma cm2610 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2610 : PowerSeries ℚ) * F) = 2610 * coeff m F := by
  have e : (2610 : PowerSeries ℚ) = C (2610 : ℚ) := (map_ofNat C 2610).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2766 : derivative ℚ (2766 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2766
@[simp] lemma cc2766 : constantCoeff (2766 : PowerSeries ℚ) = 2766 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2766
lemma cm2766 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2766 : PowerSeries ℚ) * F) = 2766 * coeff m F := by
  have e : (2766 : PowerSeries ℚ) = C (2766 : ℚ) := (map_ofNat C 2766).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3070 : derivative ℚ (3070 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3070
@[simp] lemma cc3070 : constantCoeff (3070 : PowerSeries ℚ) = 3070 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3070
lemma cm3070 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3070 : PowerSeries ℚ) * F) = 3070 * coeff m F := by
  have e : (3070 : PowerSeries ℚ) = C (3070 : ℚ) := (map_ofNat C 3070).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3358 : derivative ℚ (3358 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3358
@[simp] lemma cc3358 : constantCoeff (3358 : PowerSeries ℚ) = 3358 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3358
lemma cm3358 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3358 : PowerSeries ℚ) * F) = 3358 * coeff m F := by
  have e : (3358 : PowerSeries ℚ) = C (3358 : ℚ) := (map_ofNat C 3358).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3976 : derivative ℚ (3976 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3976
@[simp] lemma cc3976 : constantCoeff (3976 : PowerSeries ℚ) = 3976 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3976
lemma cm3976 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3976 : PowerSeries ℚ) * F) = 3976 * coeff m F := by
  have e : (3976 : PowerSeries ℚ) = C (3976 : ℚ) := (map_ofNat C 3976).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4941 : derivative ℚ (4941 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4941
@[simp] lemma cc4941 : constantCoeff (4941 : PowerSeries ℚ) = 4941 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4941
lemma cm4941 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4941 : PowerSeries ℚ) * F) = 4941 * coeff m F := by
  have e : (4941 : PowerSeries ℚ) = C (4941 : ℚ) := (map_ofNat C 4941).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5734 : derivative ℚ (5734 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5734
@[simp] lemma cc5734 : constantCoeff (5734 : PowerSeries ℚ) = 5734 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5734
lemma cm5734 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5734 : PowerSeries ℚ) * F) = 5734 * coeff m F := by
  have e : (5734 : PowerSeries ℚ) = C (5734 : ℚ) := (map_ofNat C 5734).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6659 : derivative ℚ (6659 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6659
@[simp] lemma cc6659 : constantCoeff (6659 : PowerSeries ℚ) = 6659 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6659
lemma cm6659 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6659 : PowerSeries ℚ) * F) = 6659 * coeff m F := by
  have e : (6659 : PowerSeries ℚ) = C (6659 : ℚ) := (map_ofNat C 6659).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8023 : derivative ℚ (8023 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8023
@[simp] lemma cc8023 : constantCoeff (8023 : PowerSeries ℚ) = 8023 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8023
lemma cm8023 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8023 : PowerSeries ℚ) * F) = 8023 * coeff m F := by
  have e : (8023 : PowerSeries ℚ) = C (8023 : ℚ) := (map_ofNat C 8023).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10327 : derivative ℚ (10327 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10327
@[simp] lemma cc10327 : constantCoeff (10327 : PowerSeries ℚ) = 10327 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10327
lemma cm10327 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10327 : PowerSeries ℚ) * F) = 10327 * coeff m F := by
  have e : (10327 : PowerSeries ℚ) = C (10327 : ℚ) := (map_ofNat C 10327).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12606 : derivative ℚ (12606 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12606
@[simp] lemma cc12606 : constantCoeff (12606 : PowerSeries ℚ) = 12606 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12606
lemma cm12606 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12606 : PowerSeries ℚ) * F) = 12606 * coeff m F := by
  have e : (12606 : PowerSeries ℚ) = C (12606 : ℚ) := (map_ofNat C 12606).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20015 : derivative ℚ (20015 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20015
@[simp] lemma cc20015 : constantCoeff (20015 : PowerSeries ℚ) = 20015 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20015
lemma cm20015 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20015 : PowerSeries ℚ) * F) = 20015 * coeff m F := by
  have e : (20015 : PowerSeries ℚ) = C (20015 : ℚ) := (map_ofNat C 20015).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30055 : derivative ℚ (30055 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30055
@[simp] lemma cc30055 : constantCoeff (30055 : PowerSeries ℚ) = 30055 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30055
lemma cm30055 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30055 : PowerSeries ℚ) * F) = 30055 * coeff m F := by
  have e : (30055 : PowerSeries ℚ) = C (30055 : ℚ) := (map_ofNat C 30055).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn31442 : derivative ℚ (31442 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 31442
@[simp] lemma cc31442 : constantCoeff (31442 : PowerSeries ℚ) = 31442 := by simpa using map_natCast (constantCoeff (R := ℚ)) 31442
lemma cm31442 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((31442 : PowerSeries ℚ) * F) = 31442 * coeff m F := by
  have e : (31442 : PowerSeries ℚ) = C (31442 : ℚ) := (map_ofNat C 31442).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn55605 : derivative ℚ (55605 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 55605
@[simp] lemma cc55605 : constantCoeff (55605 : PowerSeries ℚ) = 55605 := by simpa using map_natCast (constantCoeff (R := ℚ)) 55605
lemma cm55605 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((55605 : PowerSeries ℚ) * F) = 55605 * coeff m F := by
  have e : (55605 : PowerSeries ℚ) = C (55605 : ℚ) := (map_ofNat C 55605).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn83911 : derivative ℚ (83911 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 83911
@[simp] lemma cc83911 : constantCoeff (83911 : PowerSeries ℚ) = 83911 := by simpa using map_natCast (constantCoeff (R := ℚ)) 83911
lemma cm83911 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((83911 : PowerSeries ℚ) * F) = 83911 * coeff m F := by
  have e : (83911 : PowerSeries ℚ) = C (83911 : ℚ) := (map_ofNat C 83911).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn99140 : derivative ℚ (99140 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 99140
@[simp] lemma cc99140 : constantCoeff (99140 : PowerSeries ℚ) = 99140 := by simpa using map_natCast (constantCoeff (R := ℚ)) 99140
lemma cm99140 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((99140 : PowerSeries ℚ) * F) = 99140 * coeff m F := by
  have e : (99140 : PowerSeries ℚ) = C (99140 : ℚ) := (map_ofNat C 99140).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn111275 : derivative ℚ (111275 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 111275
@[simp] lemma cc111275 : constantCoeff (111275 : PowerSeries ℚ) = 111275 := by simpa using map_natCast (constantCoeff (R := ℚ)) 111275
lemma cm111275 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((111275 : PowerSeries ℚ) * F) = 111275 * coeff m F := by
  have e : (111275 : PowerSeries ℚ) = C (111275 : ℚ) := (map_ofNat C 111275).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn116239 : derivative ℚ (116239 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 116239
@[simp] lemma cc116239 : constantCoeff (116239 : PowerSeries ℚ) = 116239 := by simpa using map_natCast (constantCoeff (R := ℚ)) 116239
lemma cm116239 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((116239 : PowerSeries ℚ) * F) = 116239 * coeff m F := by
  have e : (116239 : PowerSeries ℚ) = C (116239 : ℚ) := (map_ofNat C 116239).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn134290 : derivative ℚ (134290 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 134290
@[simp] lemma cc134290 : constantCoeff (134290 : PowerSeries ℚ) = 134290 := by simpa using map_natCast (constantCoeff (R := ℚ)) 134290
lemma cm134290 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((134290 : PowerSeries ℚ) * F) = 134290 * coeff m F := by
  have e : (134290 : PowerSeries ℚ) = C (134290 : ℚ) := (map_ofNat C 134290).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn185811 : derivative ℚ (185811 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 185811
@[simp] lemma cc185811 : constantCoeff (185811 : PowerSeries ℚ) = 185811 := by simpa using map_natCast (constantCoeff (R := ℚ)) 185811
lemma cm185811 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((185811 : PowerSeries ℚ) * F) = 185811 * coeff m F := by
  have e : (185811 : PowerSeries ℚ) = C (185811 : ℚ) := (map_ofNat C 185811).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn255115 : derivative ℚ (255115 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 255115
@[simp] lemma cc255115 : constantCoeff (255115 : PowerSeries ℚ) = 255115 := by simpa using map_natCast (constantCoeff (R := ℚ)) 255115
lemma cm255115 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((255115 : PowerSeries ℚ) * F) = 255115 * coeff m F := by
  have e : (255115 : PowerSeries ℚ) = C (255115 : ℚ) := (map_ofNat C 255115).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn335644 : derivative ℚ (335644 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 335644
@[simp] lemma cc335644 : constantCoeff (335644 : PowerSeries ℚ) = 335644 := by simpa using map_natCast (constantCoeff (R := ℚ)) 335644
lemma cm335644 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((335644 : PowerSeries ℚ) * F) = 335644 * coeff m F := by
  have e : (335644 : PowerSeries ℚ) = C (335644 : ℚ) := (map_ofNat C 335644).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn341755 : derivative ℚ (341755 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 341755
@[simp] lemma cc341755 : constantCoeff (341755 : PowerSeries ℚ) = 341755 := by simpa using map_natCast (constantCoeff (R := ℚ)) 341755
lemma cm341755 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((341755 : PowerSeries ℚ) * F) = 341755 * coeff m F := by
  have e : (341755 : PowerSeries ℚ) = C (341755 : ℚ) := (map_ofNat C 341755).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn370239 : derivative ℚ (370239 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 370239
@[simp] lemma cc370239 : constantCoeff (370239 : PowerSeries ℚ) = 370239 := by simpa using map_natCast (constantCoeff (R := ℚ)) 370239
lemma cm370239 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((370239 : PowerSeries ℚ) * F) = 370239 * coeff m F := by
  have e : (370239 : PowerSeries ℚ) = C (370239 : ℚ) := (map_ofNat C 370239).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn372585 : derivative ℚ (372585 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 372585
@[simp] lemma cc372585 : constantCoeff (372585 : PowerSeries ℚ) = 372585 := by simpa using map_natCast (constantCoeff (R := ℚ)) 372585
lemma cm372585 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((372585 : PowerSeries ℚ) * F) = 372585 * coeff m F := by
  have e : (372585 : PowerSeries ℚ) = C (372585 : ℚ) := (map_ofNat C 372585).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn392998 : derivative ℚ (392998 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 392998
@[simp] lemma cc392998 : constantCoeff (392998 : PowerSeries ℚ) = 392998 := by simpa using map_natCast (constantCoeff (R := ℚ)) 392998
lemma cm392998 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((392998 : PowerSeries ℚ) * F) = 392998 * coeff m F := by
  have e : (392998 : PowerSeries ℚ) = C (392998 : ℚ) := (map_ofNat C 392998).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn424505 : derivative ℚ (424505 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 424505
@[simp] lemma cc424505 : constantCoeff (424505 : PowerSeries ℚ) = 424505 := by simpa using map_natCast (constantCoeff (R := ℚ)) 424505
lemma cm424505 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((424505 : PowerSeries ℚ) * F) = 424505 * coeff m F := by
  have e : (424505 : PowerSeries ℚ) = C (424505 : ℚ) := (map_ofNat C 424505).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn655756 : derivative ℚ (655756 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 655756
@[simp] lemma cc655756 : constantCoeff (655756 : PowerSeries ℚ) = 655756 := by simpa using map_natCast (constantCoeff (R := ℚ)) 655756
lemma cm655756 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((655756 : PowerSeries ℚ) * F) = 655756 * coeff m F := by
  have e : (655756 : PowerSeries ℚ) = C (655756 : ℚ) := (map_ofNat C 655756).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn753971 : derivative ℚ (753971 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 753971
@[simp] lemma cc753971 : constantCoeff (753971 : PowerSeries ℚ) = 753971 := by simpa using map_natCast (constantCoeff (R := ℚ)) 753971
lemma cm753971 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((753971 : PowerSeries ℚ) * F) = 753971 * coeff m F := by
  have e : (753971 : PowerSeries ℚ) = C (753971 : ℚ) := (map_ofNat C 753971).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn855380 : derivative ℚ (855380 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 855380
@[simp] lemma cc855380 : constantCoeff (855380 : PowerSeries ℚ) = 855380 := by simpa using map_natCast (constantCoeff (R := ℚ)) 855380
lemma cm855380 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((855380 : PowerSeries ℚ) * F) = 855380 * coeff m F := by
  have e : (855380 : PowerSeries ℚ) = C (855380 : ℚ) := (map_ofNat C 855380).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn911707 : derivative ℚ (911707 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 911707
@[simp] lemma cc911707 : constantCoeff (911707 : PowerSeries ℚ) = 911707 := by simpa using map_natCast (constantCoeff (R := ℚ)) 911707
lemma cm911707 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((911707 : PowerSeries ℚ) * F) = 911707 * coeff m F := by
  have e : (911707 : PowerSeries ℚ) = C (911707 : ℚ) := (map_ofNat C 911707).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1212257 : derivative ℚ (1212257 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1212257
@[simp] lemma cc1212257 : constantCoeff (1212257 : PowerSeries ℚ) = 1212257 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1212257
lemma cm1212257 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1212257 : PowerSeries ℚ) * F) = 1212257 * coeff m F := by
  have e : (1212257 : PowerSeries ℚ) = C (1212257 : ℚ) := (map_ofNat C 1212257).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1238130 : derivative ℚ (1238130 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1238130
@[simp] lemma cc1238130 : constantCoeff (1238130 : PowerSeries ℚ) = 1238130 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1238130
lemma cm1238130 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1238130 : PowerSeries ℚ) * F) = 1238130 * coeff m F := by
  have e : (1238130 : PowerSeries ℚ) = C (1238130 : ℚ) := (map_ofNat C 1238130).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1245743 : derivative ℚ (1245743 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1245743
@[simp] lemma cc1245743 : constantCoeff (1245743 : PowerSeries ℚ) = 1245743 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1245743
lemma cm1245743 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1245743 : PowerSeries ℚ) * F) = 1245743 * coeff m F := by
  have e : (1245743 : PowerSeries ℚ) = C (1245743 : ℚ) := (map_ofNat C 1245743).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1614291 : derivative ℚ (1614291 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1614291
@[simp] lemma cc1614291 : constantCoeff (1614291 : PowerSeries ℚ) = 1614291 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1614291
lemma cm1614291 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1614291 : PowerSeries ℚ) * F) = 1614291 * coeff m F := by
  have e : (1614291 : PowerSeries ℚ) = C (1614291 : ℚ) := (map_ofNat C 1614291).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1735898 : derivative ℚ (1735898 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1735898
@[simp] lemma cc1735898 : constantCoeff (1735898 : PowerSeries ℚ) = 1735898 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1735898
lemma cm1735898 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1735898 : PowerSeries ℚ) * F) = 1735898 * coeff m F := by
  have e : (1735898 : PowerSeries ℚ) = C (1735898 : ℚ) := (map_ofNat C 1735898).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1797179 : derivative ℚ (1797179 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1797179
@[simp] lemma cc1797179 : constantCoeff (1797179 : PowerSeries ℚ) = 1797179 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1797179
lemma cm1797179 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1797179 : PowerSeries ℚ) * F) = 1797179 * coeff m F := by
  have e : (1797179 : PowerSeries ℚ) = C (1797179 : ℚ) := (map_ofNat C 1797179).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1878355 : derivative ℚ (1878355 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1878355
@[simp] lemma cc1878355 : constantCoeff (1878355 : PowerSeries ℚ) = 1878355 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1878355
lemma cm1878355 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1878355 : PowerSeries ℚ) * F) = 1878355 * coeff m F := by
  have e : (1878355 : PowerSeries ℚ) = C (1878355 : ℚ) := (map_ofNat C 1878355).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2111559 : derivative ℚ (2111559 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2111559
@[simp] lemma cc2111559 : constantCoeff (2111559 : PowerSeries ℚ) = 2111559 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2111559
lemma cm2111559 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2111559 : PowerSeries ℚ) * F) = 2111559 * coeff m F := by
  have e : (2111559 : PowerSeries ℚ) = C (2111559 : ℚ) := (map_ofNat C 2111559).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2171807 : derivative ℚ (2171807 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2171807
@[simp] lemma cc2171807 : constantCoeff (2171807 : PowerSeries ℚ) = 2171807 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2171807
lemma cm2171807 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2171807 : PowerSeries ℚ) * F) = 2171807 * coeff m F := by
  have e : (2171807 : PowerSeries ℚ) = C (2171807 : ℚ) := (map_ofNat C 2171807).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3577715 : derivative ℚ (3577715 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3577715
@[simp] lemma cc3577715 : constantCoeff (3577715 : PowerSeries ℚ) = 3577715 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3577715
lemma cm3577715 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3577715 : PowerSeries ℚ) * F) = 3577715 * coeff m F := by
  have e : (3577715 : PowerSeries ℚ) = C (3577715 : ℚ) := (map_ofNat C 3577715).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4276900 : derivative ℚ (4276900 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4276900
@[simp] lemma cc4276900 : constantCoeff (4276900 : PowerSeries ℚ) = 4276900 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4276900
lemma cm4276900 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4276900 : PowerSeries ℚ) * F) = 4276900 * coeff m F := by
  have e : (4276900 : PowerSeries ℚ) = C (4276900 : ℚ) := (map_ofNat C 4276900).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4356325 : derivative ℚ (4356325 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4356325
@[simp] lemma cc4356325 : constantCoeff (4356325 : PowerSeries ℚ) = 4356325 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4356325
lemma cm4356325 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4356325 : PowerSeries ℚ) * F) = 4356325 * coeff m F := by
  have e : (4356325 : PowerSeries ℚ) = C (4356325 : ℚ) := (map_ofNat C 4356325).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5931342 : derivative ℚ (5931342 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5931342
@[simp] lemma cc5931342 : constantCoeff (5931342 : PowerSeries ℚ) = 5931342 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5931342
lemma cm5931342 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5931342 : PowerSeries ℚ) * F) = 5931342 * coeff m F := by
  have e : (5931342 : PowerSeries ℚ) = C (5931342 : ℚ) := (map_ofNat C 5931342).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6449958 : derivative ℚ (6449958 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6449958
@[simp] lemma cc6449958 : constantCoeff (6449958 : PowerSeries ℚ) = 6449958 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6449958
lemma cm6449958 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6449958 : PowerSeries ℚ) * F) = 6449958 * coeff m F := by
  have e : (6449958 : PowerSeries ℚ) = C (6449958 : ℚ) := (map_ofNat C 6449958).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9122117 : derivative ℚ (9122117 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9122117
@[simp] lemma cc9122117 : constantCoeff (9122117 : PowerSeries ℚ) = 9122117 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9122117
lemma cm9122117 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9122117 : PowerSeries ℚ) * F) = 9122117 * coeff m F := by
  have e : (9122117 : PowerSeries ℚ) = C (9122117 : ℚ) := (map_ofNat C 9122117).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9661433 : derivative ℚ (9661433 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9661433
@[simp] lemma cc9661433 : constantCoeff (9661433 : PowerSeries ℚ) = 9661433 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9661433
lemma cm9661433 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9661433 : PowerSeries ℚ) * F) = 9661433 * coeff m F := by
  have e : (9661433 : PowerSeries ℚ) = C (9661433 : ℚ) := (map_ofNat C 9661433).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17131585 : derivative ℚ (17131585 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17131585
@[simp] lemma cc17131585 : constantCoeff (17131585 : PowerSeries ℚ) = 17131585 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17131585
lemma cm17131585 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17131585 : PowerSeries ℚ) * F) = 17131585 * coeff m F := by
  have e : (17131585 : PowerSeries ℚ) = C (17131585 : ℚ) := (map_ofNat C 17131585).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18645565 : derivative ℚ (18645565 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18645565
@[simp] lemma cc18645565 : constantCoeff (18645565 : PowerSeries ℚ) = 18645565 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18645565
lemma cm18645565 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18645565 : PowerSeries ℚ) * F) = 18645565 * coeff m F := by
  have e : (18645565 : PowerSeries ℚ) = C (18645565 : ℚ) := (map_ofNat C 18645565).symm
  rw [e, coeff_C_mul]

noncomputable def R : PowerSeries ℚ := X^4 + 2*X^3 - 5*X^2 - 2*X + 1
noncomputable def DD : PowerSeries ℚ := 2*X^6 + 4*X^5 - 10*X^4 - 4*X^3 + 2*X^2
noncomputable def NN (S : PowerSeries ℚ) : PowerSeries ℚ := (X^6 + 2*X^5 - 2*X^4 - 2*X^2 - 2*X + 1) + (-X^4 - X^3 - X + 1) * S

set_option maxHeartbeats 1000000 in
lemma hdD : derivative ℚ DD = 12*X^5 + 20*X^4 - 40*X^3 - 12*X^2 + 4*X := by
  simp [DD] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdR : derivative ℚ R = 4*X^3 + 6*X^2 - 10*X - 2 := by
  simp [R] <;> ring
set_option maxHeartbeats 1000000 in
lemma hdN (S : PowerSeries ℚ) : derivative ℚ (NN S) = 6*X^5 + 10*X^4 - 8*X^3 - 4*X - 2 + (-4*X^3 - 3*X^2 - 1) * S + (-X^4 - X^3 - X + 1) * derivative ℚ S := by
  simp [NN] <;> ring

set_option maxHeartbeats 4000000 in
lemma ode1 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((-1) * X ^ 1 + (5) * X ^ 2 + (2) * X ^ 3 + (-29) * X ^ 4 + (2) * X ^ 5 + (33) * X ^ 6 + (33) * X ^ 8 + (-2) * X ^ 9 + (-29) * X ^ 10 + (-2) * X ^ 11 + (5) * X ^ 12 + (1) * X ^ 13 : PowerSeries ℚ) * derivative ℚ AA + ((-2) * X ^ 0 + (10) * X ^ 1 + (10) * X ^ 2 + (-76) * X ^ 3 + (-14) * X ^ 4 + (126) * X ^ 5 + (-30) * X ^ 6 + (-60) * X ^ 7 + (-18) * X ^ 8 + (18) * X ^ 9 + (6) * X ^ 10 : PowerSeries ℚ) * AA = ((-4) * X ^ 2 + (-12) * X ^ 4 + (-12) * X ^ 6 + (-4) * X ^ 8 : PowerSeries ℚ) := by
  have r1 := hA
  have r2 : derivative ℚ AA * DD + AA * derivative ℚ DD = derivative ℚ (NN S) := by
    have := congrArg (derivative ℚ) hA
    rw [Derivation.leibniz] at this
    simp only [smul_eq_mul] at this
    rw [← this]; ring
  have r4 := sqrt_ode S R hS
  have hK : (2 * R * DD ^ 2 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((8) * X ^ 0 + (-48) * X ^ 1 + (-24) * X ^ 2 + (464) * X ^ 3 + (-48) * X ^ 4 + (-1584) * X ^ 5 + (-88) * X ^ 6 + (1584) * X ^ 7 + (-48) * X ^ 8 + (-464) * X ^ 9 + (-24) * X ^ 10 + (48) * X ^ 11 + (8) * X ^ 12 : PowerSeries ℚ)) 4 (by simp only [R, DD]; ring) (by simp [R, DD] <;> norm_num)
  apply mul_left_cancel₀ hK
  rw [hdD, hdN] at r2
  rw [hdR] at r4
  unfold NN at r1
  unfold DD at r1 r2
  unfold R at r4
  unfold DD R
  linear_combination (-24*X^22 - 208*X^21 - 248*X^20 + 2072*X^19 + 4288*X^18 - 8352*X^17 - 18592*X^16 + 17328*X^15 + 30360*X^14 - 14576*X^13 - 16184*X^12 + 1448*X^11 - 3216*X^10 + 672*X^9 + 3392*X^8 - 432*X^7 - 680*X^6 + 112*X^5 + 40*X^4 - 8*X^3) * r1 + (4*X^23 + 36*X^22 + 48*X^21 - 364*X^20 - 828*X^19 + 1464*X^18 + 3664*X^17 - 3000*X^16 - 5596*X^15 + 2188*X^14 + 2188*X^12 + 5596*X^11 - 3000*X^10 - 3664*X^9 + 1464*X^8 + 828*X^7 - 364*X^6 - 48*X^5 + 36*X^4 - 4*X^3) * r2 + (-2*X^23 - 16*X^22 - 20*X^21 + 112*X^20 + 226*X^19 - 240*X^18 - 504*X^17 + 48*X^16 - 170*X^15 + 416*X^14 + 1156*X^13 - 416*X^12 - 170*X^11 - 48*X^10 - 504*X^9 + 240*X^8 + 226*X^7 - 112*X^6 - 20*X^5 + 16*X^4 - 2*X^3) * r4

set_option maxHeartbeats 1000000 in
lemma hdV : derivative ℚ ((-1) * X ^ 1 + (5) * X ^ 2 + (2) * X ^ 3 + (-29) * X ^ 4 + (2) * X ^ 5 + (33) * X ^ 6 + (33) * X ^ 8 + (-2) * X ^ 9 + (-29) * X ^ 10 + (-2) * X ^ 11 + (5) * X ^ 12 + (1) * X ^ 13 : PowerSeries ℚ) = ((-1) * X ^ 0 + (10) * X ^ 1 + (6) * X ^ 2 + (-116) * X ^ 3 + (10) * X ^ 4 + (198) * X ^ 5 + (264) * X ^ 7 + (-18) * X ^ 8 + (-290) * X ^ 9 + (-22) * X ^ 10 + (60) * X ^ 11 + (13) * X ^ 12 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU : derivative ℚ ((-2) * X ^ 0 + (10) * X ^ 1 + (10) * X ^ 2 + (-76) * X ^ 3 + (-14) * X ^ 4 + (126) * X ^ 5 + (-30) * X ^ 6 + (-60) * X ^ 7 + (-18) * X ^ 8 + (18) * X ^ 9 + (6) * X ^ 10 : PowerSeries ℚ) = ((10) * X ^ 0 + (20) * X ^ 1 + (-228) * X ^ 2 + (-56) * X ^ 3 + (630) * X ^ 4 + (-180) * X ^ 5 + (-420) * X ^ 6 + (-144) * X ^ 7 + (162) * X ^ 8 + (60) * X ^ 9 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW : derivative ℚ ((-4) * X ^ 2 + (-12) * X ^ 4 + (-12) * X ^ 6 + (-4) * X ^ 8 : PowerSeries ℚ) = ((-8) * X ^ 1 + (-48) * X ^ 3 + (-72) * X ^ 5 + (-32) * X ^ 7 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdV1 : derivative ℚ ((-1) * X ^ 0 + (10) * X ^ 1 + (6) * X ^ 2 + (-116) * X ^ 3 + (10) * X ^ 4 + (198) * X ^ 5 + (264) * X ^ 7 + (-18) * X ^ 8 + (-290) * X ^ 9 + (-22) * X ^ 10 + (60) * X ^ 11 + (13) * X ^ 12 : PowerSeries ℚ) = ((10) * X ^ 0 + (12) * X ^ 1 + (-348) * X ^ 2 + (40) * X ^ 3 + (990) * X ^ 4 + (1848) * X ^ 6 + (-144) * X ^ 7 + (-2610) * X ^ 8 + (-220) * X ^ 9 + (660) * X ^ 10 + (156) * X ^ 11 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdU1 : derivative ℚ ((10) * X ^ 0 + (20) * X ^ 1 + (-228) * X ^ 2 + (-56) * X ^ 3 + (630) * X ^ 4 + (-180) * X ^ 5 + (-420) * X ^ 6 + (-144) * X ^ 7 + (162) * X ^ 8 + (60) * X ^ 9 : PowerSeries ℚ) = ((20) * X ^ 0 + (-456) * X ^ 1 + (-168) * X ^ 2 + (2520) * X ^ 3 + (-900) * X ^ 4 + (-2520) * X ^ 5 + (-1008) * X ^ 6 + (1296) * X ^ 7 + (540) * X ^ 8 : PowerSeries ℚ) := by
  simp <;> ring
set_option maxHeartbeats 1000000 in
lemma hdW1 : derivative ℚ ((-8) * X ^ 1 + (-48) * X ^ 3 + (-72) * X ^ 5 + (-32) * X ^ 7 : PowerSeries ℚ) = ((-8) * X ^ 0 + (-144) * X ^ 2 + (-360) * X ^ 4 + (-224) * X ^ 6 : PowerSeries ℚ) := by
  simp <;> ring

lemma dmul (F G : PowerSeries ℚ) : derivative ℚ (F * G) = F * derivative ℚ G + G * derivative ℚ F := by
  rw [Derivation.leibniz]; simp only [smul_eq_mul]

set_option maxHeartbeats 4000000 in
lemma ode2 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((-1) * X ^ 0 + (10) * X ^ 1 + (6) * X ^ 2 + (-116) * X ^ 3 + (10) * X ^ 4 + (198) * X ^ 5 + (264) * X ^ 7 + (-18) * X ^ 8 + (-290) * X ^ 9 + (-22) * X ^ 10 + (60) * X ^ 11 + (13) * X ^ 12 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 1 + (5) * X ^ 2 + (2) * X ^ 3 + (-29) * X ^ 4 + (2) * X ^ 5 + (33) * X ^ 6 + (33) * X ^ 8 + (-2) * X ^ 9 + (-29) * X ^ 10 + (-2) * X ^ 11 + (5) * X ^ 12 + (1) * X ^ 13 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((10) * X ^ 0 + (20) * X ^ 1 + (-228) * X ^ 2 + (-56) * X ^ 3 + (630) * X ^ 4 + (-180) * X ^ 5 + (-420) * X ^ 6 + (-144) * X ^ 7 + (162) * X ^ 8 + (60) * X ^ 9 : PowerSeries ℚ) * AA + ((-2) * X ^ 0 + (10) * X ^ 1 + (10) * X ^ 2 + (-76) * X ^ 3 + (-14) * X ^ 4 + (126) * X ^ 5 + (-30) * X ^ 6 + (-60) * X ^ 7 + (-18) * X ^ 8 + (18) * X ^ 9 + (6) * X ^ 10 : PowerSeries ℚ) * derivative ℚ AA = ((-8) * X ^ 1 + (-48) * X ^ 3 + (-72) * X ^ 5 + (-32) * X ^ 7 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode1 S AA hS hA)
  rw [map_add, dmul, dmul, hdV, hdU, hdW] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3' (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((10) * X ^ 0 + (12) * X ^ 1 + (-348) * X ^ 2 + (40) * X ^ 3 + (990) * X ^ 4 + (1848) * X ^ 6 + (-144) * X ^ 7 + (-2610) * X ^ 8 + (-220) * X ^ 9 + (660) * X ^ 10 + (156) * X ^ 11 : PowerSeries ℚ) * derivative ℚ AA + ((-1) * X ^ 0 + (10) * X ^ 1 + (6) * X ^ 2 + (-116) * X ^ 3 + (10) * X ^ 4 + (198) * X ^ 5 + (264) * X ^ 7 + (-18) * X ^ 8 + (-290) * X ^ 9 + (-22) * X ^ 10 + (60) * X ^ 11 + (13) * X ^ 12 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + (((-1) * X ^ 0 + (10) * X ^ 1 + (6) * X ^ 2 + (-116) * X ^ 3 + (10) * X ^ 4 + (198) * X ^ 5 + (264) * X ^ 7 + (-18) * X ^ 8 + (-290) * X ^ 9 + (-22) * X ^ 10 + (60) * X ^ 11 + (13) * X ^ 12 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) + ((-1) * X ^ 1 + (5) * X ^ 2 + (2) * X ^ 3 + (-29) * X ^ 4 + (2) * X ^ 5 + (33) * X ^ 6 + (33) * X ^ 8 + (-2) * X ^ 9 + (-29) * X ^ 10 + (-2) * X ^ 11 + (5) * X ^ 12 + (1) * X ^ 13 : PowerSeries ℚ) * derivative ℚ (derivative ℚ (derivative ℚ AA))) + (((20) * X ^ 0 + (-456) * X ^ 1 + (-168) * X ^ 2 + (2520) * X ^ 3 + (-900) * X ^ 4 + (-2520) * X ^ 5 + (-1008) * X ^ 6 + (1296) * X ^ 7 + (540) * X ^ 8 : PowerSeries ℚ) * AA + ((10) * X ^ 0 + (20) * X ^ 1 + (-228) * X ^ 2 + (-56) * X ^ 3 + (630) * X ^ 4 + (-180) * X ^ 5 + (-420) * X ^ 6 + (-144) * X ^ 7 + (162) * X ^ 8 + (60) * X ^ 9 : PowerSeries ℚ) * derivative ℚ AA) + (((10) * X ^ 0 + (20) * X ^ 1 + (-228) * X ^ 2 + (-56) * X ^ 3 + (630) * X ^ 4 + (-180) * X ^ 5 + (-420) * X ^ 6 + (-144) * X ^ 7 + (162) * X ^ 8 + (60) * X ^ 9 : PowerSeries ℚ) * derivative ℚ AA + ((-2) * X ^ 0 + (10) * X ^ 1 + (10) * X ^ 2 + (-76) * X ^ 3 + (-14) * X ^ 4 + (126) * X ^ 5 + (-30) * X ^ 6 + (-60) * X ^ 7 + (-18) * X ^ 8 + (18) * X ^ 9 + (6) * X ^ 10 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA)) = ((-8) * X ^ 0 + (-144) * X ^ 2 + (-360) * X ^ 4 + (-224) * X ^ 6 : PowerSeries ℚ) := by
  have h := congrArg (derivative ℚ) (ode2 S AA hS hA)
  rw [map_add, map_add, map_add, dmul, dmul, dmul, dmul, hdV1, hdV, hdU1, hdU, hdW1] at h
  linear_combination h

set_option maxHeartbeats 4000000 in
lemma ode3 (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) : ((14) * X ^ 0 + (244) * X ^ 1 + (-812) * X ^ 2 + (-1776) * X ^ 3 + (2430) * X ^ 4 + (2352) * X ^ 5 + (-1248) * X ^ 6 + (-756) * X ^ 7 + (42) * X ^ 8 : PowerSeries ℚ) * AA + ((-8) * X ^ 1 + (107) * X ^ 2 + (20) * X ^ 3 + (-480) * X ^ 4 + (-1584) * X ^ 5 + (-705) * X ^ 6 + (2766) * X ^ 7 + (540) * X ^ 8 + (-790) * X ^ 9 + (-137) * X ^ 10 + (22) * X ^ 11 : PowerSeries ℚ) * derivative ℚ AA + ((-5) * X ^ 2 + (-5) * X ^ 3 + (135) * X ^ 4 + (10) * X ^ 5 + (-725) * X ^ 6 + (-235) * X ^ 7 + (725) * X ^ 8 + (10) * X ^ 9 + (-135) * X ^ 10 + (-5) * X ^ 11 + (5) * X ^ 12 : PowerSeries ℚ) * derivative ℚ (derivative ℚ AA) = ((-12) * X ^ 2 + (288) * X ^ 3 + (288) * X ^ 5 + (12) * X ^ 6 : PowerSeries ℚ) := by
  have e1 := ode1 S AA hS hA
  have e2 := ode2 S AA hS hA
  have e3 := ode3' S AA hS hA
  have hK : (((-1) * X ^ 1 + (5) * X ^ 2 + (2) * X ^ 3 + (-29) * X ^ 4 + (2) * X ^ 5 + (33) * X ^ 6 + (33) * X ^ 8 + (-2) * X ^ 9 + (-29) * X ^ 10 + (-2) * X ^ 11 + (5) * X ^ 12 + (1) * X ^ 13 : PowerSeries ℚ) ^ 3 : PowerSeries ℚ) ≠ 0 :=
    ne_zero_of _ (((-1) * X ^ 0 + (15) * X ^ 1 + (-69) * X ^ 2 + (-22) * X ^ 3 + (1014) * X ^ 4 + (-1728) * X ^ 5 + (-5119) * X ^ 6 + (14913) * X ^ 7 + (10044) * X ^ 8 + (-51683) * X ^ 9 + (759) * X ^ 10 + (69108) * X ^ 11 + (-26299) * X ^ 12 + (48393) * X ^ 13 + (14844) * X ^ 14 + (-242235) * X ^ 15 + (23046) * X ^ 16 + (166155) * X ^ 17 + (166155) * X ^ 19 + (-23046) * X ^ 20 + (-242235) * X ^ 21 + (-14844) * X ^ 22 + (48393) * X ^ 23 + (26299) * X ^ 24 + (69108) * X ^ 25 + (-759) * X ^ 26 + (-51683) * X ^ 27 + (-10044) * X ^ 28 + (14913) * X ^ 29 + (5119) * X ^ 30 + (-1728) * X ^ 31 + (-1014) * X ^ 32 + (-22) * X ^ 33 + (69) * X ^ 34 + (15) * X ^ 35 + (1) * X ^ 36 : PowerSeries ℚ)) 3 (by ring) (by simp <;> norm_num)
  apply mul_left_cancel₀ hK
  linear_combination (((0) * X ^ 0 : PowerSeries ℚ)) * e3 + (((-5) * X ^ 4 + (45) * X ^ 5 + (80) * X ^ 6 + (-1835) * X ^ 7 + (3070) * X ^ 8 + (20015) * X ^ 9 + (-55605) * X ^ 10 + (-99140) * X ^ 11 + (372585) * X ^ 12 + (255115) * X ^ 13 + (-1238130) * X ^ 14 + (-341755) * X ^ 15 + (1878355) * X ^ 16 + (134290) * X ^ 17 + (-30055) * X ^ 18 + (424505) * X ^ 19 + (-3577715) * X ^ 20 + (-855380) * X ^ 21 + (3577715) * X ^ 22 + (424505) * X ^ 23 + (30055) * X ^ 24 + (134290) * X ^ 25 + (-1878355) * X ^ 26 + (-341755) * X ^ 27 + (1238130) * X ^ 28 + (255115) * X ^ 29 + (-372585) * X ^ 30 + (-99140) * X ^ 31 + (55605) * X ^ 32 + (20015) * X ^ 33 + (-3070) * X ^ 34 + (-1835) * X ^ 35 + (-80) * X ^ 36 + (45) * X ^ 37 + (5) * X ^ 38 : PowerSeries ℚ)) * e2 + (((7) * X ^ 3 + (27) * X ^ 4 + (-1408) * X ^ 5 + (8023) * X ^ 6 + (742) * X ^ 7 + (-116239) * X ^ 8 + (185811) * X ^ 9 + (655756) * X ^ 10 + (-1614291) * X ^ 11 + (-1797179) * X ^ 12 + (5931342) * X ^ 13 + (2171807) * X ^ 14 + (-9661433) * X ^ 15 + (392998) * X ^ 16 + (1212257) * X ^ 17 + (-4356325) * X ^ 18 + (17131585) * X ^ 19 + (4276900) * X ^ 20 + (-18645565) * X ^ 21 + (111275) * X ^ 22 + (911707) * X ^ 23 + (-1735898) * X ^ 24 + (9122117) * X ^ 25 + (1245743) * X ^ 26 + (-6449958) * X ^ 27 + (-753971) * X ^ 28 + (2111559) * X ^ 29 + (335644) * X ^ 30 + (-370239) * X ^ 31 + (-83911) * X ^ 32 + (31442) * X ^ 33 + (10327) * X ^ 34 + (-608) * X ^ 35 + (-477) * X ^ 36 + (-43) * X ^ 37 : PowerSeries ℚ)) * e1

set_option maxHeartbeats 4000000 in
lemma rec_a (S AA : PowerSeries ℚ) (hS : S * S = R) (hA : AA * DD = NN S) (k : ℕ) : (-5*((k + 10 : ℕ) : ℚ)^2 - 3*((k + 10 : ℕ) : ℚ) + 14) * coeff (k + 10) AA + (-5*((k + 10 : ℕ) : ℚ)^2 + 122*((k + 10 : ℕ) : ℚ) + 127) * coeff (k + 9) AA + (135*((k + 10 : ℕ) : ℚ)^2 - 655*((k + 10 : ℕ) : ℚ) - 42) * coeff (k + 8) AA + (10*((k + 10 : ℕ) : ℚ)^2 - 550*((k + 10 : ℕ) : ℚ) - 216) * coeff (k + 7) AA + (-725*((k + 10 : ℕ) : ℚ)^2 + 4941*((k + 10 : ℕ) : ℚ) - 5734) * coeff (k + 6) AA + (-235*((k + 10 : ℕ) : ℚ)^2 + 1880*((k + 10 : ℕ) : ℚ) - 1173) * coeff (k + 5) AA + (725*((k + 10 : ℕ) : ℚ)^2 - 6659*((k + 10 : ℕ) : ℚ) + 12606) * coeff (k + 4) AA + (10*((k + 10 : ℕ) : ℚ)^2 + 390*((k + 10 : ℕ) : ℚ) - 3976) * coeff (k + 3) AA + (-135*((k + 10 : ℕ) : ℚ)^2 + 1505*((k + 10 : ℕ) : ℚ) - 3358) * coeff (k + 2) AA + (-5*((k + 10 : ℕ) : ℚ)^2 - 42*((k + 10 : ℕ) : ℚ) + 783) * coeff (k + 1) AA + (5*((k + 10 : ℕ) : ℚ)^2 - 83*((k + 10 : ℕ) : ℚ) + 330) * coeff (k + 0) AA = 0 := by
  have h := congrArg (coeff (k + 10)) (ode3 S AA hS hA)
  rcases k with _ | _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm14, cm15, cm16, cm17, cm18, cm19, cm20, cm21, cm22, cm23, cm24, cm25, cm26, cm27, cm28, cm29, cm30, cm31, cm32, cm33, cm34, cm35, cm36, cm37, cm38, cm40, cm42, cm43, cm45, cm48, cm56, cm60, cm72, cm76, cm80, cm83, cm107, cm116, cm122, cm126, cm127, cm135, cm137, cm144, cm156, cm162, cm168, cm180, cm192, cm198, cm204, cm216, cm220, cm224, cm228, cm235, cm244, cm264, cm272, cm288, cm290, cm324, cm330, cm348, cm360, cm390, cm420, cm456, cm477, cm480, cm540, cm550, cm608, cm630, cm655, cm660, cm705, cm725, cm742, cm756, cm783, cm790, cm812, cm900, cm990, cm1008, cm1173, cm1248, cm1296, cm1408, cm1505, cm1584, cm1776, cm1835, cm1848, cm1880, cm2352, cm2430, cm2520, cm2610, cm2766, cm3070, cm3358, cm3976, cm4941, cm5734, cm6659, cm8023, cm10327, cm12606, cm20015, cm30055, cm31442, cm55605, cm83911, cm99140, cm111275, cm116239, cm134290, cm185811, cm255115, cm335644, cm341755, cm370239, cm372585, cm392998, cm424505, cm655756, cm753971, cm855380, cm911707, cm1212257, cm1238130, cm1245743, cm1614291, cm1735898, cm1797179, cm1878355, cm2111559, cm2171807, cm3577715, cm4276900, cm4356325, cm5931342, cm6449958, cm9122117, cm9661433, cm17131585, cm18645565, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h


end OMA.S_oeis_a134424

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a134424.main := by
  intro T G hT hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  have hS : (2 * X ^ 2 * T + (X + X ^ 2 - 1)) * (2 * X ^ 2 * T + (X + X ^ 2 - 1)) = OMA.S_oeis_a134424.R := by
    unfold OMA.S_oeis_a134424.R; linear_combination (-4 * X ^ 2) * hT
  have hA : G * OMA.S_oeis_a134424.DD = OMA.S_oeis_a134424.NN (2 * X ^ 2 * T + (X + X ^ 2 - 1)) := by
    unfold OMA.S_oeis_a134424.DD OMA.S_oeis_a134424.NN
    linear_combination (2 * X ^ 2) * hG + (-(2 * X ^ 2) * (1 + X ^ 2)) * hT
  have h := OMA.S_oeis_a134424.rec_a _ G hS hA k
  simp only [show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega, show k + 10 - 4 = k + 6 from by omega, show k + 10 - 5 = k + 5 from by omega, show k + 10 - 6 = k + 4 from by omega, show k + 10 - 7 = k + 3 from by omega, show k + 10 - 8 = k + 2 from by omega, show k + 10 - 9 = k + 1 from by omega, show k + 10 - 10 = k + 0 from by omega]
  push_cast at h ⊢
  linear_combination h
