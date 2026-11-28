import OMAStatements.S_oeis_a243816
import Mathlib

namespace OMA.S_oeis_a243816

open PowerSeries

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
@[simp] lemma dn24 : derivative ℚ (24 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24
@[simp] lemma cc24 : constantCoeff (24 : PowerSeries ℚ) = 24 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24
lemma cm24 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24 : PowerSeries ℚ) * F) = 24 * coeff m F := by
  have e : (24 : PowerSeries ℚ) = C (24 : ℚ) := (map_ofNat C 24).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn26 : derivative ℚ (26 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 26
@[simp] lemma cc26 : constantCoeff (26 : PowerSeries ℚ) = 26 := by simpa using map_natCast (constantCoeff (R := ℚ)) 26
lemma cm26 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((26 : PowerSeries ℚ) * F) = 26 * coeff m F := by
  have e : (26 : PowerSeries ℚ) = C (26 : ℚ) := (map_ofNat C 26).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn30 : derivative ℚ (30 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 30
@[simp] lemma cc30 : constantCoeff (30 : PowerSeries ℚ) = 30 := by simpa using map_natCast (constantCoeff (R := ℚ)) 30
lemma cm30 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((30 : PowerSeries ℚ) * F) = 30 * coeff m F := by
  have e : (30 : PowerSeries ℚ) = C (30 : ℚ) := (map_ofNat C 30).symm
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
@[simp] lemma dn36 : derivative ℚ (36 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36
@[simp] lemma cc36 : constantCoeff (36 : PowerSeries ℚ) = 36 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36
lemma cm36 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36 : PowerSeries ℚ) * F) = 36 * coeff m F := by
  have e : (36 : PowerSeries ℚ) = C (36 : ℚ) := (map_ofNat C 36).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn44 : derivative ℚ (44 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 44
@[simp] lemma cc44 : constantCoeff (44 : PowerSeries ℚ) = 44 := by simpa using map_natCast (constantCoeff (R := ℚ)) 44
lemma cm44 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((44 : PowerSeries ℚ) * F) = 44 * coeff m F := by
  have e : (44 : PowerSeries ℚ) = C (44 : ℚ) := (map_ofNat C 44).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn47 : derivative ℚ (47 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 47
@[simp] lemma cc47 : constantCoeff (47 : PowerSeries ℚ) = 47 := by simpa using map_natCast (constantCoeff (R := ℚ)) 47
lemma cm47 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((47 : PowerSeries ℚ) * F) = 47 * coeff m F := by
  have e : (47 : PowerSeries ℚ) = C (47 : ℚ) := (map_ofNat C 47).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn48 : derivative ℚ (48 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 48
@[simp] lemma cc48 : constantCoeff (48 : PowerSeries ℚ) = 48 := by simpa using map_natCast (constantCoeff (R := ℚ)) 48
lemma cm48 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((48 : PowerSeries ℚ) * F) = 48 * coeff m F := by
  have e : (48 : PowerSeries ℚ) = C (48 : ℚ) := (map_ofNat C 48).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn50 : derivative ℚ (50 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 50
@[simp] lemma cc50 : constantCoeff (50 : PowerSeries ℚ) = 50 := by simpa using map_natCast (constantCoeff (R := ℚ)) 50
lemma cm50 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((50 : PowerSeries ℚ) * F) = 50 * coeff m F := by
  have e : (50 : PowerSeries ℚ) = C (50 : ℚ) := (map_ofNat C 50).symm
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
@[simp] lemma dn68 : derivative ℚ (68 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 68
@[simp] lemma cc68 : constantCoeff (68 : PowerSeries ℚ) = 68 := by simpa using map_natCast (constantCoeff (R := ℚ)) 68
lemma cm68 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((68 : PowerSeries ℚ) * F) = 68 * coeff m F := by
  have e : (68 : PowerSeries ℚ) = C (68 : ℚ) := (map_ofNat C 68).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn72 : derivative ℚ (72 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72
@[simp] lemma cc72 : constantCoeff (72 : PowerSeries ℚ) = 72 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72
lemma cm72 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72 : PowerSeries ℚ) * F) = 72 * coeff m F := by
  have e : (72 : PowerSeries ℚ) = C (72 : ℚ) := (map_ofNat C 72).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn74 : derivative ℚ (74 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 74
@[simp] lemma cc74 : constantCoeff (74 : PowerSeries ℚ) = 74 := by simpa using map_natCast (constantCoeff (R := ℚ)) 74
lemma cm74 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((74 : PowerSeries ℚ) * F) = 74 * coeff m F := by
  have e : (74 : PowerSeries ℚ) = C (74 : ℚ) := (map_ofNat C 74).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn75 : derivative ℚ (75 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 75
@[simp] lemma cc75 : constantCoeff (75 : PowerSeries ℚ) = 75 := by simpa using map_natCast (constantCoeff (R := ℚ)) 75
lemma cm75 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((75 : PowerSeries ℚ) * F) = 75 * coeff m F := by
  have e : (75 : PowerSeries ℚ) = C (75 : ℚ) := (map_ofNat C 75).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80 : derivative ℚ (80 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80
@[simp] lemma cc80 : constantCoeff (80 : PowerSeries ℚ) = 80 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80
lemma cm80 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80 : PowerSeries ℚ) * F) = 80 * coeff m F := by
  have e : (80 : PowerSeries ℚ) = C (80 : ℚ) := (map_ofNat C 80).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn82 : derivative ℚ (82 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 82
@[simp] lemma cc82 : constantCoeff (82 : PowerSeries ℚ) = 82 := by simpa using map_natCast (constantCoeff (R := ℚ)) 82
lemma cm82 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((82 : PowerSeries ℚ) * F) = 82 * coeff m F := by
  have e : (82 : PowerSeries ℚ) = C (82 : ℚ) := (map_ofNat C 82).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn96 : derivative ℚ (96 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 96
@[simp] lemma cc96 : constantCoeff (96 : PowerSeries ℚ) = 96 := by simpa using map_natCast (constantCoeff (R := ℚ)) 96
lemma cm96 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((96 : PowerSeries ℚ) * F) = 96 * coeff m F := by
  have e : (96 : PowerSeries ℚ) = C (96 : ℚ) := (map_ofNat C 96).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn98 : derivative ℚ (98 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 98
@[simp] lemma cc98 : constantCoeff (98 : PowerSeries ℚ) = 98 := by simpa using map_natCast (constantCoeff (R := ℚ)) 98
lemma cm98 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((98 : PowerSeries ℚ) * F) = 98 * coeff m F := by
  have e : (98 : PowerSeries ℚ) = C (98 : ℚ) := (map_ofNat C 98).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn100 : derivative ℚ (100 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 100
@[simp] lemma cc100 : constantCoeff (100 : PowerSeries ℚ) = 100 := by simpa using map_natCast (constantCoeff (R := ℚ)) 100
lemma cm100 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((100 : PowerSeries ℚ) * F) = 100 * coeff m F := by
  have e : (100 : PowerSeries ℚ) = C (100 : ℚ) := (map_ofNat C 100).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn104 : derivative ℚ (104 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 104
@[simp] lemma cc104 : constantCoeff (104 : PowerSeries ℚ) = 104 := by simpa using map_natCast (constantCoeff (R := ℚ)) 104
lemma cm104 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((104 : PowerSeries ℚ) * F) = 104 * coeff m F := by
  have e : (104 : PowerSeries ℚ) = C (104 : ℚ) := (map_ofNat C 104).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn106 : derivative ℚ (106 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 106
@[simp] lemma cc106 : constantCoeff (106 : PowerSeries ℚ) = 106 := by simpa using map_natCast (constantCoeff (R := ℚ)) 106
lemma cm106 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((106 : PowerSeries ℚ) * F) = 106 * coeff m F := by
  have e : (106 : PowerSeries ℚ) = C (106 : ℚ) := (map_ofNat C 106).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn110 : derivative ℚ (110 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 110
@[simp] lemma cc110 : constantCoeff (110 : PowerSeries ℚ) = 110 := by simpa using map_natCast (constantCoeff (R := ℚ)) 110
lemma cm110 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((110 : PowerSeries ℚ) * F) = 110 * coeff m F := by
  have e : (110 : PowerSeries ℚ) = C (110 : ℚ) := (map_ofNat C 110).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn112 : derivative ℚ (112 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 112
@[simp] lemma cc112 : constantCoeff (112 : PowerSeries ℚ) = 112 := by simpa using map_natCast (constantCoeff (R := ℚ)) 112
lemma cm112 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((112 : PowerSeries ℚ) * F) = 112 * coeff m F := by
  have e : (112 : PowerSeries ℚ) = C (112 : ℚ) := (map_ofNat C 112).symm
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
@[simp] lemma dn128 : derivative ℚ (128 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 128
@[simp] lemma cc128 : constantCoeff (128 : PowerSeries ℚ) = 128 := by simpa using map_natCast (constantCoeff (R := ℚ)) 128
lemma cm128 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((128 : PowerSeries ℚ) * F) = 128 * coeff m F := by
  have e : (128 : PowerSeries ℚ) = C (128 : ℚ) := (map_ofNat C 128).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn132 : derivative ℚ (132 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 132
@[simp] lemma cc132 : constantCoeff (132 : PowerSeries ℚ) = 132 := by simpa using map_natCast (constantCoeff (R := ℚ)) 132
lemma cm132 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((132 : PowerSeries ℚ) * F) = 132 * coeff m F := by
  have e : (132 : PowerSeries ℚ) = C (132 : ℚ) := (map_ofNat C 132).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn136 : derivative ℚ (136 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 136
@[simp] lemma cc136 : constantCoeff (136 : PowerSeries ℚ) = 136 := by simpa using map_natCast (constantCoeff (R := ℚ)) 136
lemma cm136 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((136 : PowerSeries ℚ) * F) = 136 * coeff m F := by
  have e : (136 : PowerSeries ℚ) = C (136 : ℚ) := (map_ofNat C 136).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn144 : derivative ℚ (144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 144
@[simp] lemma cc144 : constantCoeff (144 : PowerSeries ℚ) = 144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 144
lemma cm144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((144 : PowerSeries ℚ) * F) = 144 * coeff m F := by
  have e : (144 : PowerSeries ℚ) = C (144 : ℚ) := (map_ofNat C 144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn152 : derivative ℚ (152 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 152
@[simp] lemma cc152 : constantCoeff (152 : PowerSeries ℚ) = 152 := by simpa using map_natCast (constantCoeff (R := ℚ)) 152
lemma cm152 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((152 : PowerSeries ℚ) * F) = 152 * coeff m F := by
  have e : (152 : PowerSeries ℚ) = C (152 : ℚ) := (map_ofNat C 152).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn160 : derivative ℚ (160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 160
@[simp] lemma cc160 : constantCoeff (160 : PowerSeries ℚ) = 160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 160
lemma cm160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((160 : PowerSeries ℚ) * F) = 160 * coeff m F := by
  have e : (160 : PowerSeries ℚ) = C (160 : ℚ) := (map_ofNat C 160).symm
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
@[simp] lemma dn192 : derivative ℚ (192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 192
@[simp] lemma cc192 : constantCoeff (192 : PowerSeries ℚ) = 192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 192
lemma cm192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((192 : PowerSeries ℚ) * F) = 192 * coeff m F := by
  have e : (192 : PowerSeries ℚ) = C (192 : ℚ) := (map_ofNat C 192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn196 : derivative ℚ (196 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 196
@[simp] lemma cc196 : constantCoeff (196 : PowerSeries ℚ) = 196 := by simpa using map_natCast (constantCoeff (R := ℚ)) 196
lemma cm196 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((196 : PowerSeries ℚ) * F) = 196 * coeff m F := by
  have e : (196 : PowerSeries ℚ) = C (196 : ℚ) := (map_ofNat C 196).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn204 : derivative ℚ (204 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 204
@[simp] lemma cc204 : constantCoeff (204 : PowerSeries ℚ) = 204 := by simpa using map_natCast (constantCoeff (R := ℚ)) 204
lemma cm204 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((204 : PowerSeries ℚ) * F) = 204 * coeff m F := by
  have e : (204 : PowerSeries ℚ) = C (204 : ℚ) := (map_ofNat C 204).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn212 : derivative ℚ (212 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 212
@[simp] lemma cc212 : constantCoeff (212 : PowerSeries ℚ) = 212 := by simpa using map_natCast (constantCoeff (R := ℚ)) 212
lemma cm212 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((212 : PowerSeries ℚ) * F) = 212 * coeff m F := by
  have e : (212 : PowerSeries ℚ) = C (212 : ℚ) := (map_ofNat C 212).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn232 : derivative ℚ (232 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 232
@[simp] lemma cc232 : constantCoeff (232 : PowerSeries ℚ) = 232 := by simpa using map_natCast (constantCoeff (R := ℚ)) 232
lemma cm232 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((232 : PowerSeries ℚ) * F) = 232 * coeff m F := by
  have e : (232 : PowerSeries ℚ) = C (232 : ℚ) := (map_ofNat C 232).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn244 : derivative ℚ (244 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 244
@[simp] lemma cc244 : constantCoeff (244 : PowerSeries ℚ) = 244 := by simpa using map_natCast (constantCoeff (R := ℚ)) 244
lemma cm244 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((244 : PowerSeries ℚ) * F) = 244 * coeff m F := by
  have e : (244 : PowerSeries ℚ) = C (244 : ℚ) := (map_ofNat C 244).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn250 : derivative ℚ (250 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 250
@[simp] lemma cc250 : constantCoeff (250 : PowerSeries ℚ) = 250 := by simpa using map_natCast (constantCoeff (R := ℚ)) 250
lemma cm250 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((250 : PowerSeries ℚ) * F) = 250 * coeff m F := by
  have e : (250 : PowerSeries ℚ) = C (250 : ℚ) := (map_ofNat C 250).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn256 : derivative ℚ (256 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 256
@[simp] lemma cc256 : constantCoeff (256 : PowerSeries ℚ) = 256 := by simpa using map_natCast (constantCoeff (R := ℚ)) 256
lemma cm256 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((256 : PowerSeries ℚ) * F) = 256 * coeff m F := by
  have e : (256 : PowerSeries ℚ) = C (256 : ℚ) := (map_ofNat C 256).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn260 : derivative ℚ (260 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 260
@[simp] lemma cc260 : constantCoeff (260 : PowerSeries ℚ) = 260 := by simpa using map_natCast (constantCoeff (R := ℚ)) 260
lemma cm260 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((260 : PowerSeries ℚ) * F) = 260 * coeff m F := by
  have e : (260 : PowerSeries ℚ) = C (260 : ℚ) := (map_ofNat C 260).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn268 : derivative ℚ (268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 268
@[simp] lemma cc268 : constantCoeff (268 : PowerSeries ℚ) = 268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 268
lemma cm268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((268 : PowerSeries ℚ) * F) = 268 * coeff m F := by
  have e : (268 : PowerSeries ℚ) = C (268 : ℚ) := (map_ofNat C 268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn276 : derivative ℚ (276 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 276
@[simp] lemma cc276 : constantCoeff (276 : PowerSeries ℚ) = 276 := by simpa using map_natCast (constantCoeff (R := ℚ)) 276
lemma cm276 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((276 : PowerSeries ℚ) * F) = 276 * coeff m F := by
  have e : (276 : PowerSeries ℚ) = C (276 : ℚ) := (map_ofNat C 276).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn289 : derivative ℚ (289 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 289
@[simp] lemma cc289 : constantCoeff (289 : PowerSeries ℚ) = 289 := by simpa using map_natCast (constantCoeff (R := ℚ)) 289
lemma cm289 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((289 : PowerSeries ℚ) * F) = 289 * coeff m F := by
  have e : (289 : PowerSeries ℚ) = C (289 : ℚ) := (map_ofNat C 289).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn290 : derivative ℚ (290 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 290
@[simp] lemma cc290 : constantCoeff (290 : PowerSeries ℚ) = 290 := by simpa using map_natCast (constantCoeff (R := ℚ)) 290
lemma cm290 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((290 : PowerSeries ℚ) * F) = 290 * coeff m F := by
  have e : (290 : PowerSeries ℚ) = C (290 : ℚ) := (map_ofNat C 290).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn296 : derivative ℚ (296 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 296
@[simp] lemma cc296 : constantCoeff (296 : PowerSeries ℚ) = 296 := by simpa using map_natCast (constantCoeff (R := ℚ)) 296
lemma cm296 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((296 : PowerSeries ℚ) * F) = 296 * coeff m F := by
  have e : (296 : PowerSeries ℚ) = C (296 : ℚ) := (map_ofNat C 296).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn312 : derivative ℚ (312 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 312
@[simp] lemma cc312 : constantCoeff (312 : PowerSeries ℚ) = 312 := by simpa using map_natCast (constantCoeff (R := ℚ)) 312
lemma cm312 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((312 : PowerSeries ℚ) * F) = 312 * coeff m F := by
  have e : (312 : PowerSeries ℚ) = C (312 : ℚ) := (map_ofNat C 312).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn324 : derivative ℚ (324 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 324
@[simp] lemma cc324 : constantCoeff (324 : PowerSeries ℚ) = 324 := by simpa using map_natCast (constantCoeff (R := ℚ)) 324
lemma cm324 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((324 : PowerSeries ℚ) * F) = 324 * coeff m F := by
  have e : (324 : PowerSeries ℚ) = C (324 : ℚ) := (map_ofNat C 324).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn348 : derivative ℚ (348 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 348
@[simp] lemma cc348 : constantCoeff (348 : PowerSeries ℚ) = 348 := by simpa using map_natCast (constantCoeff (R := ℚ)) 348
lemma cm348 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((348 : PowerSeries ℚ) * F) = 348 * coeff m F := by
  have e : (348 : PowerSeries ℚ) = C (348 : ℚ) := (map_ofNat C 348).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn353 : derivative ℚ (353 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 353
@[simp] lemma cc353 : constantCoeff (353 : PowerSeries ℚ) = 353 := by simpa using map_natCast (constantCoeff (R := ℚ)) 353
lemma cm353 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((353 : PowerSeries ℚ) * F) = 353 * coeff m F := by
  have e : (353 : PowerSeries ℚ) = C (353 : ℚ) := (map_ofNat C 353).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn376 : derivative ℚ (376 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 376
@[simp] lemma cc376 : constantCoeff (376 : PowerSeries ℚ) = 376 := by simpa using map_natCast (constantCoeff (R := ℚ)) 376
lemma cm376 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((376 : PowerSeries ℚ) * F) = 376 * coeff m F := by
  have e : (376 : PowerSeries ℚ) = C (376 : ℚ) := (map_ofNat C 376).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn378 : derivative ℚ (378 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 378
@[simp] lemma cc378 : constantCoeff (378 : PowerSeries ℚ) = 378 := by simpa using map_natCast (constantCoeff (R := ℚ)) 378
lemma cm378 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((378 : PowerSeries ℚ) * F) = 378 * coeff m F := by
  have e : (378 : PowerSeries ℚ) = C (378 : ℚ) := (map_ofNat C 378).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn384 : derivative ℚ (384 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 384
@[simp] lemma cc384 : constantCoeff (384 : PowerSeries ℚ) = 384 := by simpa using map_natCast (constantCoeff (R := ℚ)) 384
lemma cm384 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((384 : PowerSeries ℚ) * F) = 384 * coeff m F := by
  have e : (384 : PowerSeries ℚ) = C (384 : ℚ) := (map_ofNat C 384).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn400 : derivative ℚ (400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 400
@[simp] lemma cc400 : constantCoeff (400 : PowerSeries ℚ) = 400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 400
lemma cm400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((400 : PowerSeries ℚ) * F) = 400 * coeff m F := by
  have e : (400 : PowerSeries ℚ) = C (400 : ℚ) := (map_ofNat C 400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn404 : derivative ℚ (404 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 404
@[simp] lemma cc404 : constantCoeff (404 : PowerSeries ℚ) = 404 := by simpa using map_natCast (constantCoeff (R := ℚ)) 404
lemma cm404 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((404 : PowerSeries ℚ) * F) = 404 * coeff m F := by
  have e : (404 : PowerSeries ℚ) = C (404 : ℚ) := (map_ofNat C 404).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn420 : derivative ℚ (420 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 420
@[simp] lemma cc420 : constantCoeff (420 : PowerSeries ℚ) = 420 := by simpa using map_natCast (constantCoeff (R := ℚ)) 420
lemma cm420 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((420 : PowerSeries ℚ) * F) = 420 * coeff m F := by
  have e : (420 : PowerSeries ℚ) = C (420 : ℚ) := (map_ofNat C 420).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn432 : derivative ℚ (432 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 432
@[simp] lemma cc432 : constantCoeff (432 : PowerSeries ℚ) = 432 := by simpa using map_natCast (constantCoeff (R := ℚ)) 432
lemma cm432 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((432 : PowerSeries ℚ) * F) = 432 * coeff m F := by
  have e : (432 : PowerSeries ℚ) = C (432 : ℚ) := (map_ofNat C 432).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn480 : derivative ℚ (480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 480
@[simp] lemma cc480 : constantCoeff (480 : PowerSeries ℚ) = 480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 480
lemma cm480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((480 : PowerSeries ℚ) * F) = 480 * coeff m F := by
  have e : (480 : PowerSeries ℚ) = C (480 : ℚ) := (map_ofNat C 480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn481 : derivative ℚ (481 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 481
@[simp] lemma cc481 : constantCoeff (481 : PowerSeries ℚ) = 481 := by simpa using map_natCast (constantCoeff (R := ℚ)) 481
lemma cm481 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((481 : PowerSeries ℚ) * F) = 481 * coeff m F := by
  have e : (481 : PowerSeries ℚ) = C (481 : ℚ) := (map_ofNat C 481).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn488 : derivative ℚ (488 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 488
@[simp] lemma cc488 : constantCoeff (488 : PowerSeries ℚ) = 488 := by simpa using map_natCast (constantCoeff (R := ℚ)) 488
lemma cm488 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((488 : PowerSeries ℚ) * F) = 488 * coeff m F := by
  have e : (488 : PowerSeries ℚ) = C (488 : ℚ) := (map_ofNat C 488).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn512 : derivative ℚ (512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 512
@[simp] lemma cc512 : constantCoeff (512 : PowerSeries ℚ) = 512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 512
lemma cm512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((512 : PowerSeries ℚ) * F) = 512 * coeff m F := by
  have e : (512 : PowerSeries ℚ) = C (512 : ℚ) := (map_ofNat C 512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn540 : derivative ℚ (540 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 540
@[simp] lemma cc540 : constantCoeff (540 : PowerSeries ℚ) = 540 := by simpa using map_natCast (constantCoeff (R := ℚ)) 540
lemma cm540 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((540 : PowerSeries ℚ) * F) = 540 * coeff m F := by
  have e : (540 : PowerSeries ℚ) = C (540 : ℚ) := (map_ofNat C 540).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn676 : derivative ℚ (676 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 676
@[simp] lemma cc676 : constantCoeff (676 : PowerSeries ℚ) = 676 := by simpa using map_natCast (constantCoeff (R := ℚ)) 676
lemma cm676 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((676 : PowerSeries ℚ) * F) = 676 * coeff m F := by
  have e : (676 : PowerSeries ℚ) = C (676 : ℚ) := (map_ofNat C 676).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn706 : derivative ℚ (706 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 706
@[simp] lemma cc706 : constantCoeff (706 : PowerSeries ℚ) = 706 := by simpa using map_natCast (constantCoeff (R := ℚ)) 706
lemma cm706 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((706 : PowerSeries ℚ) * F) = 706 * coeff m F := by
  have e : (706 : PowerSeries ℚ) = C (706 : ℚ) := (map_ofNat C 706).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn720 : derivative ℚ (720 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 720
@[simp] lemma cc720 : constantCoeff (720 : PowerSeries ℚ) = 720 := by simpa using map_natCast (constantCoeff (R := ℚ)) 720
lemma cm720 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((720 : PowerSeries ℚ) * F) = 720 * coeff m F := by
  have e : (720 : PowerSeries ℚ) = C (720 : ℚ) := (map_ofNat C 720).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn752 : derivative ℚ (752 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 752
@[simp] lemma cc752 : constantCoeff (752 : PowerSeries ℚ) = 752 := by simpa using map_natCast (constantCoeff (R := ℚ)) 752
lemma cm752 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((752 : PowerSeries ℚ) * F) = 752 * coeff m F := by
  have e : (752 : PowerSeries ℚ) = C (752 : ℚ) := (map_ofNat C 752).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn760 : derivative ℚ (760 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 760
@[simp] lemma cc760 : constantCoeff (760 : PowerSeries ℚ) = 760 := by simpa using map_natCast (constantCoeff (R := ℚ)) 760
lemma cm760 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((760 : PowerSeries ℚ) * F) = 760 * coeff m F := by
  have e : (760 : PowerSeries ℚ) = C (760 : ℚ) := (map_ofNat C 760).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn768 : derivative ℚ (768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 768
@[simp] lemma cc768 : constantCoeff (768 : PowerSeries ℚ) = 768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 768
lemma cm768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((768 : PowerSeries ℚ) * F) = 768 * coeff m F := by
  have e : (768 : PowerSeries ℚ) = C (768 : ℚ) := (map_ofNat C 768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn788 : derivative ℚ (788 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 788
@[simp] lemma cc788 : constantCoeff (788 : PowerSeries ℚ) = 788 := by simpa using map_natCast (constantCoeff (R := ℚ)) 788
lemma cm788 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((788 : PowerSeries ℚ) * F) = 788 * coeff m F := by
  have e : (788 : PowerSeries ℚ) = C (788 : ℚ) := (map_ofNat C 788).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn816 : derivative ℚ (816 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 816
@[simp] lemma cc816 : constantCoeff (816 : PowerSeries ℚ) = 816 := by simpa using map_natCast (constantCoeff (R := ℚ)) 816
lemma cm816 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((816 : PowerSeries ℚ) * F) = 816 * coeff m F := by
  have e : (816 : PowerSeries ℚ) = C (816 : ℚ) := (map_ofNat C 816).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn860 : derivative ℚ (860 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 860
@[simp] lemma cc860 : constantCoeff (860 : PowerSeries ℚ) = 860 := by simpa using map_natCast (constantCoeff (R := ℚ)) 860
lemma cm860 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((860 : PowerSeries ℚ) * F) = 860 * coeff m F := by
  have e : (860 : PowerSeries ℚ) = C (860 : ℚ) := (map_ofNat C 860).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn900 : derivative ℚ (900 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 900
@[simp] lemma cc900 : constantCoeff (900 : PowerSeries ℚ) = 900 := by simpa using map_natCast (constantCoeff (R := ℚ)) 900
lemma cm900 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((900 : PowerSeries ℚ) * F) = 900 * coeff m F := by
  have e : (900 : PowerSeries ℚ) = C (900 : ℚ) := (map_ofNat C 900).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn912 : derivative ℚ (912 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 912
@[simp] lemma cc912 : constantCoeff (912 : PowerSeries ℚ) = 912 := by simpa using map_natCast (constantCoeff (R := ℚ)) 912
lemma cm912 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((912 : PowerSeries ℚ) * F) = 912 * coeff m F := by
  have e : (912 : PowerSeries ℚ) = C (912 : ℚ) := (map_ofNat C 912).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn928 : derivative ℚ (928 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 928
@[simp] lemma cc928 : constantCoeff (928 : PowerSeries ℚ) = 928 := by simpa using map_natCast (constantCoeff (R := ℚ)) 928
lemma cm928 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((928 : PowerSeries ℚ) * F) = 928 * coeff m F := by
  have e : (928 : PowerSeries ℚ) = C (928 : ℚ) := (map_ofNat C 928).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn960 : derivative ℚ (960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 960
@[simp] lemma cc960 : constantCoeff (960 : PowerSeries ℚ) = 960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 960
lemma cm960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((960 : PowerSeries ℚ) * F) = 960 * coeff m F := by
  have e : (960 : PowerSeries ℚ) = C (960 : ℚ) := (map_ofNat C 960).symm
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
@[simp] lemma dn1024 : derivative ℚ (1024 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1024
@[simp] lemma cc1024 : constantCoeff (1024 : PowerSeries ℚ) = 1024 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1024
lemma cm1024 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1024 : PowerSeries ℚ) * F) = 1024 * coeff m F := by
  have e : (1024 : PowerSeries ℚ) = C (1024 : ℚ) := (map_ofNat C 1024).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1200 : derivative ℚ (1200 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1200
@[simp] lemma cc1200 : constantCoeff (1200 : PowerSeries ℚ) = 1200 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1200
lemma cm1200 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1200 : PowerSeries ℚ) * F) = 1200 * coeff m F := by
  have e : (1200 : PowerSeries ℚ) = C (1200 : ℚ) := (map_ofNat C 1200).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1332 : derivative ℚ (1332 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1332
@[simp] lemma cc1332 : constantCoeff (1332 : PowerSeries ℚ) = 1332 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1332
lemma cm1332 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1332 : PowerSeries ℚ) * F) = 1332 * coeff m F := by
  have e : (1332 : PowerSeries ℚ) = C (1332 : ℚ) := (map_ofNat C 1332).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1352 : derivative ℚ (1352 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1352
@[simp] lemma cc1352 : constantCoeff (1352 : PowerSeries ℚ) = 1352 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1352
lemma cm1352 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1352 : PowerSeries ℚ) * F) = 1352 * coeff m F := by
  have e : (1352 : PowerSeries ℚ) = C (1352 : ℚ) := (map_ofNat C 1352).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1392 : derivative ℚ (1392 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1392
@[simp] lemma cc1392 : constantCoeff (1392 : PowerSeries ℚ) = 1392 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1392
lemma cm1392 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1392 : PowerSeries ℚ) * F) = 1392 * coeff m F := by
  have e : (1392 : PowerSeries ℚ) = C (1392 : ℚ) := (map_ofNat C 1392).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1440 : derivative ℚ (1440 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1440
@[simp] lemma cc1440 : constantCoeff (1440 : PowerSeries ℚ) = 1440 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1440
lemma cm1440 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1440 : PowerSeries ℚ) * F) = 1440 * coeff m F := by
  have e : (1440 : PowerSeries ℚ) = C (1440 : ℚ) := (map_ofNat C 1440).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1450 : derivative ℚ (1450 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1450
@[simp] lemma cc1450 : constantCoeff (1450 : PowerSeries ℚ) = 1450 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1450
lemma cm1450 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1450 : PowerSeries ℚ) * F) = 1450 * coeff m F := by
  have e : (1450 : PowerSeries ℚ) = C (1450 : ℚ) := (map_ofNat C 1450).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1520 : derivative ℚ (1520 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1520
@[simp] lemma cc1520 : constantCoeff (1520 : PowerSeries ℚ) = 1520 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1520
lemma cm1520 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1520 : PowerSeries ℚ) * F) = 1520 * coeff m F := by
  have e : (1520 : PowerSeries ℚ) = C (1520 : ℚ) := (map_ofNat C 1520).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1728 : derivative ℚ (1728 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1728
@[simp] lemma cc1728 : constantCoeff (1728 : PowerSeries ℚ) = 1728 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1728
lemma cm1728 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1728 : PowerSeries ℚ) * F) = 1728 * coeff m F := by
  have e : (1728 : PowerSeries ℚ) = C (1728 : ℚ) := (map_ofNat C 1728).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1765 : derivative ℚ (1765 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1765
@[simp] lemma cc1765 : constantCoeff (1765 : PowerSeries ℚ) = 1765 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1765
lemma cm1765 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1765 : PowerSeries ℚ) * F) = 1765 * coeff m F := by
  have e : (1765 : PowerSeries ℚ) = C (1765 : ℚ) := (map_ofNat C 1765).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1920 : derivative ℚ (1920 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1920
@[simp] lemma cc1920 : constantCoeff (1920 : PowerSeries ℚ) = 1920 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1920
lemma cm1920 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1920 : PowerSeries ℚ) * F) = 1920 * coeff m F := by
  have e : (1920 : PowerSeries ℚ) = C (1920 : ℚ) := (map_ofNat C 1920).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1980 : derivative ℚ (1980 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1980
@[simp] lemma cc1980 : constantCoeff (1980 : PowerSeries ℚ) = 1980 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1980
lemma cm1980 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1980 : PowerSeries ℚ) * F) = 1980 * coeff m F := by
  have e : (1980 : PowerSeries ℚ) = C (1980 : ℚ) := (map_ofNat C 1980).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2056 : derivative ℚ (2056 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2056
@[simp] lemma cc2056 : constantCoeff (2056 : PowerSeries ℚ) = 2056 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2056
lemma cm2056 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2056 : PowerSeries ℚ) * F) = 2056 * coeff m F := by
  have e : (2056 : PowerSeries ℚ) = C (2056 : ℚ) := (map_ofNat C 2056).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2080 : derivative ℚ (2080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2080
@[simp] lemma cc2080 : constantCoeff (2080 : PowerSeries ℚ) = 2080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2080
lemma cm2080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2080 : PowerSeries ℚ) * F) = 2080 * coeff m F := by
  have e : (2080 : PowerSeries ℚ) = C (2080 : ℚ) := (map_ofNat C 2080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2118 : derivative ℚ (2118 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2118
@[simp] lemma cc2118 : constantCoeff (2118 : PowerSeries ℚ) = 2118 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2118
lemma cm2118 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2118 : PowerSeries ℚ) * F) = 2118 * coeff m F := by
  have e : (2118 : PowerSeries ℚ) = C (2118 : ℚ) := (map_ofNat C 2118).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2240 : derivative ℚ (2240 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2240
@[simp] lemma cc2240 : constantCoeff (2240 : PowerSeries ℚ) = 2240 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2240
lemma cm2240 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2240 : PowerSeries ℚ) * F) = 2240 * coeff m F := by
  have e : (2240 : PowerSeries ℚ) = C (2240 : ℚ) := (map_ofNat C 2240).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2520 : derivative ℚ (2520 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2520
@[simp] lemma cc2520 : constantCoeff (2520 : PowerSeries ℚ) = 2520 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2520
lemma cm2520 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2520 : PowerSeries ℚ) * F) = 2520 * coeff m F := by
  have e : (2520 : PowerSeries ℚ) = C (2520 : ℚ) := (map_ofNat C 2520).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2640 : derivative ℚ (2640 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2640
@[simp] lemma cc2640 : constantCoeff (2640 : PowerSeries ℚ) = 2640 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2640
lemma cm2640 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2640 : PowerSeries ℚ) * F) = 2640 * coeff m F := by
  have e : (2640 : PowerSeries ℚ) = C (2640 : ℚ) := (map_ofNat C 2640).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2970 : derivative ℚ (2970 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2970
@[simp] lemma cc2970 : constantCoeff (2970 : PowerSeries ℚ) = 2970 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2970
lemma cm2970 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2970 : PowerSeries ℚ) * F) = 2970 * coeff m F := by
  have e : (2970 : PowerSeries ℚ) = C (2970 : ℚ) := (map_ofNat C 2970).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3040 : derivative ℚ (3040 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3040
@[simp] lemma cc3040 : constantCoeff (3040 : PowerSeries ℚ) = 3040 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3040
lemma cm3040 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3040 : PowerSeries ℚ) * F) = 3040 * coeff m F := by
  have e : (3040 : PowerSeries ℚ) = C (3040 : ℚ) := (map_ofNat C 3040).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3108 : derivative ℚ (3108 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3108
@[simp] lemma cc3108 : constantCoeff (3108 : PowerSeries ℚ) = 3108 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3108
lemma cm3108 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3108 : PowerSeries ℚ) * F) = 3108 * coeff m F := by
  have e : (3108 : PowerSeries ℚ) = C (3108 : ℚ) := (map_ofNat C 3108).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3336 : derivative ℚ (3336 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3336
@[simp] lemma cc3336 : constantCoeff (3336 : PowerSeries ℚ) = 3336 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3336
lemma cm3336 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3336 : PowerSeries ℚ) * F) = 3336 * coeff m F := by
  have e : (3336 : PowerSeries ℚ) = C (3336 : ℚ) := (map_ofNat C 3336).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3468 : derivative ℚ (3468 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3468
@[simp] lemma cc3468 : constantCoeff (3468 : PowerSeries ℚ) = 3468 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3468
lemma cm3468 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3468 : PowerSeries ℚ) * F) = 3468 * coeff m F := by
  have e : (3468 : PowerSeries ℚ) = C (3468 : ℚ) := (map_ofNat C 3468).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3600 : derivative ℚ (3600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3600
@[simp] lemma cc3600 : constantCoeff (3600 : PowerSeries ℚ) = 3600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3600
lemma cm3600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3600 : PowerSeries ℚ) * F) = 3600 * coeff m F := by
  have e : (3600 : PowerSeries ℚ) = C (3600 : ℚ) := (map_ofNat C 3600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3648 : derivative ℚ (3648 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3648
@[simp] lemma cc3648 : constantCoeff (3648 : PowerSeries ℚ) = 3648 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3648
lemma cm3648 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3648 : PowerSeries ℚ) * F) = 3648 * coeff m F := by
  have e : (3648 : PowerSeries ℚ) = C (3648 : ℚ) := (map_ofNat C 3648).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4024 : derivative ℚ (4024 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4024
@[simp] lemma cc4024 : constantCoeff (4024 : PowerSeries ℚ) = 4024 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4024
lemma cm4024 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4024 : PowerSeries ℚ) * F) = 4024 * coeff m F := by
  have e : (4024 : PowerSeries ℚ) = C (4024 : ℚ) := (map_ofNat C 4024).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4300 : derivative ℚ (4300 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4300
@[simp] lemma cc4300 : constantCoeff (4300 : PowerSeries ℚ) = 4300 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4300
lemma cm4300 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4300 : PowerSeries ℚ) * F) = 4300 * coeff m F := by
  have e : (4300 : PowerSeries ℚ) = C (4300 : ℚ) := (map_ofNat C 4300).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4780 : derivative ℚ (4780 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4780
@[simp] lemma cc4780 : constantCoeff (4780 : PowerSeries ℚ) = 4780 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4780
lemma cm4780 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4780 : PowerSeries ℚ) * F) = 4780 * coeff m F := by
  have e : (4780 : PowerSeries ℚ) = C (4780 : ℚ) := (map_ofNat C 4780).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5116 : derivative ℚ (5116 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5116
@[simp] lemma cc5116 : constantCoeff (5116 : PowerSeries ℚ) = 5116 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5116
lemma cm5116 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5116 : PowerSeries ℚ) * F) = 5116 * coeff m F := by
  have e : (5116 : PowerSeries ℚ) = C (5116 : ℚ) := (map_ofNat C 5116).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5364 : derivative ℚ (5364 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5364
@[simp] lemma cc5364 : constantCoeff (5364 : PowerSeries ℚ) = 5364 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5364
lemma cm5364 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5364 : PowerSeries ℚ) * F) = 5364 * coeff m F := by
  have e : (5364 : PowerSeries ℚ) = C (5364 : ℚ) := (map_ofNat C 5364).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5760 : derivative ℚ (5760 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5760
@[simp] lemma cc5760 : constantCoeff (5760 : PowerSeries ℚ) = 5760 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5760
lemma cm5760 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5760 : PowerSeries ℚ) * F) = 5760 * coeff m F := by
  have e : (5760 : PowerSeries ℚ) = C (5760 : ℚ) := (map_ofNat C 5760).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6000 : derivative ℚ (6000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6000
@[simp] lemma cc6000 : constantCoeff (6000 : PowerSeries ℚ) = 6000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6000
lemma cm6000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6000 : PowerSeries ℚ) * F) = 6000 * coeff m F := by
  have e : (6000 : PowerSeries ℚ) = C (6000 : ℚ) := (map_ofNat C 6000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6144 : derivative ℚ (6144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6144
@[simp] lemma cc6144 : constantCoeff (6144 : PowerSeries ℚ) = 6144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6144
lemma cm6144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6144 : PowerSeries ℚ) * F) = 6144 * coeff m F := by
  have e : (6144 : PowerSeries ℚ) = C (6144 : ℚ) := (map_ofNat C 6144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7584 : derivative ℚ (7584 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7584
@[simp] lemma cc7584 : constantCoeff (7584 : PowerSeries ℚ) = 7584 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7584
lemma cm7584 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7584 : PowerSeries ℚ) * F) = 7584 * coeff m F := by
  have e : (7584 : PowerSeries ℚ) = C (7584 : ℚ) := (map_ofNat C 7584).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11784 : derivative ℚ (11784 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11784
@[simp] lemma cc11784 : constantCoeff (11784 : PowerSeries ℚ) = 11784 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11784
lemma cm11784 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11784 : PowerSeries ℚ) * F) = 11784 * coeff m F := by
  have e : (11784 : PowerSeries ℚ) = C (11784 : ℚ) := (map_ofNat C 11784).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11808 : derivative ℚ (11808 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11808
@[simp] lemma cc11808 : constantCoeff (11808 : PowerSeries ℚ) = 11808 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11808
lemma cm11808 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11808 : PowerSeries ℚ) * F) = 11808 * coeff m F := by
  have e : (11808 : PowerSeries ℚ) = C (11808 : ℚ) := (map_ofNat C 11808).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12015 : derivative ℚ (12015 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12015
@[simp] lemma cc12015 : constantCoeff (12015 : PowerSeries ℚ) = 12015 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12015
lemma cm12015 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12015 : PowerSeries ℚ) * F) = 12015 * coeff m F := by
  have e : (12015 : PowerSeries ℚ) = C (12015 : ℚ) := (map_ofNat C 12015).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn13056 : derivative ℚ (13056 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13056
@[simp] lemma cc13056 : constantCoeff (13056 : PowerSeries ℚ) = 13056 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13056
lemma cm13056 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13056 : PowerSeries ℚ) * F) = 13056 * coeff m F := by
  have e : (13056 : PowerSeries ℚ) = C (13056 : ℚ) := (map_ofNat C 13056).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn13280 : derivative ℚ (13280 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 13280
@[simp] lemma cc13280 : constantCoeff (13280 : PowerSeries ℚ) = 13280 := by simpa using map_natCast (constantCoeff (R := ℚ)) 13280
lemma cm13280 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((13280 : PowerSeries ℚ) * F) = 13280 * coeff m F := by
  have e : (13280 : PowerSeries ℚ) = C (13280 : ℚ) := (map_ofNat C 13280).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14392 : derivative ℚ (14392 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14392
@[simp] lemma cc14392 : constantCoeff (14392 : PowerSeries ℚ) = 14392 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14392
lemma cm14392 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14392 : PowerSeries ℚ) * F) = 14392 * coeff m F := by
  have e : (14392 : PowerSeries ℚ) = C (14392 : ℚ) := (map_ofNat C 14392).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14468 : derivative ℚ (14468 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14468
@[simp] lemma cc14468 : constantCoeff (14468 : PowerSeries ℚ) = 14468 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14468
lemma cm14468 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14468 : PowerSeries ℚ) * F) = 14468 * coeff m F := by
  have e : (14468 : PowerSeries ℚ) = C (14468 : ℚ) := (map_ofNat C 14468).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15360 : derivative ℚ (15360 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15360
@[simp] lemma cc15360 : constantCoeff (15360 : PowerSeries ℚ) = 15360 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15360
lemma cm15360 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15360 : PowerSeries ℚ) * F) = 15360 * coeff m F := by
  have e : (15360 : PowerSeries ℚ) = C (15360 : ℚ) := (map_ofNat C 15360).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15692 : derivative ℚ (15692 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15692
@[simp] lemma cc15692 : constantCoeff (15692 : PowerSeries ℚ) = 15692 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15692
lemma cm15692 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15692 : PowerSeries ℚ) * F) = 15692 * coeff m F := by
  have e : (15692 : PowerSeries ℚ) = C (15692 : ℚ) := (map_ofNat C 15692).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17420 : derivative ℚ (17420 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17420
@[simp] lemma cc17420 : constantCoeff (17420 : PowerSeries ℚ) = 17420 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17420
lemma cm17420 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17420 : PowerSeries ℚ) * F) = 17420 * coeff m F := by
  have e : (17420 : PowerSeries ℚ) = C (17420 : ℚ) := (map_ofNat C 17420).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18312 : derivative ℚ (18312 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18312
@[simp] lemma cc18312 : constantCoeff (18312 : PowerSeries ℚ) = 18312 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18312
lemma cm18312 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18312 : PowerSeries ℚ) * F) = 18312 * coeff m F := by
  have e : (18312 : PowerSeries ℚ) = C (18312 : ℚ) := (map_ofNat C 18312).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18944 : derivative ℚ (18944 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18944
@[simp] lemma cc18944 : constantCoeff (18944 : PowerSeries ℚ) = 18944 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18944
lemma cm18944 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18944 : PowerSeries ℚ) * F) = 18944 * coeff m F := by
  have e : (18944 : PowerSeries ℚ) = C (18944 : ℚ) := (map_ofNat C 18944).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19968 : derivative ℚ (19968 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19968
@[simp] lemma cc19968 : constantCoeff (19968 : PowerSeries ℚ) = 19968 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19968
lemma cm19968 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19968 : PowerSeries ℚ) * F) = 19968 * coeff m F := by
  have e : (19968 : PowerSeries ℚ) = C (19968 : ℚ) := (map_ofNat C 19968).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn20112 : derivative ℚ (20112 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 20112
@[simp] lemma cc20112 : constantCoeff (20112 : PowerSeries ℚ) = 20112 := by simpa using map_natCast (constantCoeff (R := ℚ)) 20112
lemma cm20112 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((20112 : PowerSeries ℚ) * F) = 20112 * coeff m F := by
  have e : (20112 : PowerSeries ℚ) = C (20112 : ℚ) := (map_ofNat C 20112).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn21664 : derivative ℚ (21664 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 21664
@[simp] lemma cc21664 : constantCoeff (21664 : PowerSeries ℚ) = 21664 := by simpa using map_natCast (constantCoeff (R := ℚ)) 21664
lemma cm21664 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((21664 : PowerSeries ℚ) * F) = 21664 * coeff m F := by
  have e : (21664 : PowerSeries ℚ) = C (21664 : ℚ) := (map_ofNat C 21664).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22512 : derivative ℚ (22512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22512
@[simp] lemma cc22512 : constantCoeff (22512 : PowerSeries ℚ) = 22512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22512
lemma cm22512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22512 : PowerSeries ℚ) * F) = 22512 * coeff m F := by
  have e : (22512 : PowerSeries ℚ) = C (22512 : ℚ) := (map_ofNat C 22512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn23040 : derivative ℚ (23040 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 23040
@[simp] lemma cc23040 : constantCoeff (23040 : PowerSeries ℚ) = 23040 := by simpa using map_natCast (constantCoeff (R := ℚ)) 23040
lemma cm23040 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((23040 : PowerSeries ℚ) * F) = 23040 * coeff m F := by
  have e : (23040 : PowerSeries ℚ) = C (23040 : ℚ) := (map_ofNat C 23040).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32400 : derivative ℚ (32400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32400
@[simp] lemma cc32400 : constantCoeff (32400 : PowerSeries ℚ) = 32400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32400
lemma cm32400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32400 : PowerSeries ℚ) * F) = 32400 * coeff m F := by
  have e : (32400 : PowerSeries ℚ) = C (32400 : ℚ) := (map_ofNat C 32400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn34560 : derivative ℚ (34560 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 34560
@[simp] lemma cc34560 : constantCoeff (34560 : PowerSeries ℚ) = 34560 := by simpa using map_natCast (constantCoeff (R := ℚ)) 34560
lemma cm34560 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((34560 : PowerSeries ℚ) * F) = 34560 * coeff m F := by
  have e : (34560 : PowerSeries ℚ) = C (34560 : ℚ) := (map_ofNat C 34560).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn35472 : derivative ℚ (35472 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 35472
@[simp] lemma cc35472 : constantCoeff (35472 : PowerSeries ℚ) = 35472 := by simpa using map_natCast (constantCoeff (R := ℚ)) 35472
lemma cm35472 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((35472 : PowerSeries ℚ) * F) = 35472 * coeff m F := by
  have e : (35472 : PowerSeries ℚ) = C (35472 : ℚ) := (map_ofNat C 35472).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn41760 : derivative ℚ (41760 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 41760
@[simp] lemma cc41760 : constantCoeff (41760 : PowerSeries ℚ) = 41760 := by simpa using map_natCast (constantCoeff (R := ℚ)) 41760
lemma cm41760 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((41760 : PowerSeries ℚ) * F) = 41760 * coeff m F := by
  have e : (41760 : PowerSeries ℚ) = C (41760 : ℚ) := (map_ofNat C 41760).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn42360 : derivative ℚ (42360 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 42360
@[simp] lemma cc42360 : constantCoeff (42360 : PowerSeries ℚ) = 42360 := by simpa using map_natCast (constantCoeff (R := ℚ)) 42360
lemma cm42360 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((42360 : PowerSeries ℚ) * F) = 42360 * coeff m F := by
  have e : (42360 : PowerSeries ℚ) = C (42360 : ℚ) := (map_ofNat C 42360).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn57456 : derivative ℚ (57456 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 57456
@[simp] lemma cc57456 : constantCoeff (57456 : PowerSeries ℚ) = 57456 := by simpa using map_natCast (constantCoeff (R := ℚ)) 57456
lemma cm57456 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((57456 : PowerSeries ℚ) * F) = 57456 * coeff m F := by
  have e : (57456 : PowerSeries ℚ) = C (57456 : ℚ) := (map_ofNat C 57456).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn61456 : derivative ℚ (61456 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 61456
@[simp] lemma cc61456 : constantCoeff (61456 : PowerSeries ℚ) = 61456 := by simpa using map_natCast (constantCoeff (R := ℚ)) 61456
lemma cm61456 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((61456 : PowerSeries ℚ) * F) = 61456 * coeff m F := by
  have e : (61456 : PowerSeries ℚ) = C (61456 : ℚ) := (map_ofNat C 61456).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn62112 : derivative ℚ (62112 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 62112
@[simp] lemma cc62112 : constantCoeff (62112 : PowerSeries ℚ) = 62112 := by simpa using map_natCast (constantCoeff (R := ℚ)) 62112
lemma cm62112 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((62112 : PowerSeries ℚ) * F) = 62112 * coeff m F := by
  have e : (62112 : PowerSeries ℚ) = C (62112 : ℚ) := (map_ofNat C 62112).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn63264 : derivative ℚ (63264 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 63264
@[simp] lemma cc63264 : constantCoeff (63264 : PowerSeries ℚ) = 63264 := by simpa using map_natCast (constantCoeff (R := ℚ)) 63264
lemma cm63264 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((63264 : PowerSeries ℚ) * F) = 63264 * coeff m F := by
  have e : (63264 : PowerSeries ℚ) = C (63264 : ℚ) := (map_ofNat C 63264).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn66408 : derivative ℚ (66408 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 66408
@[simp] lemma cc66408 : constantCoeff (66408 : PowerSeries ℚ) = 66408 := by simpa using map_natCast (constantCoeff (R := ℚ)) 66408
lemma cm66408 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((66408 : PowerSeries ℚ) * F) = 66408 * coeff m F := by
  have e : (66408 : PowerSeries ℚ) = C (66408 : ℚ) := (map_ofNat C 66408).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn74960 : derivative ℚ (74960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 74960
@[simp] lemma cc74960 : constantCoeff (74960 : PowerSeries ℚ) = 74960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 74960
lemma cm74960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((74960 : PowerSeries ℚ) * F) = 74960 * coeff m F := by
  have e : (74960 : PowerSeries ℚ) = C (74960 : ℚ) := (map_ofNat C 74960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn75060 : derivative ℚ (75060 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 75060
@[simp] lemma cc75060 : constantCoeff (75060 : PowerSeries ℚ) = 75060 := by simpa using map_natCast (constantCoeff (R := ℚ)) 75060
lemma cm75060 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((75060 : PowerSeries ℚ) * F) = 75060 * coeff m F := by
  have e : (75060 : PowerSeries ℚ) = C (75060 : ℚ) := (map_ofNat C 75060).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn78504 : derivative ℚ (78504 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 78504
@[simp] lemma cc78504 : constantCoeff (78504 : PowerSeries ℚ) = 78504 := by simpa using map_natCast (constantCoeff (R := ℚ)) 78504
lemma cm78504 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((78504 : PowerSeries ℚ) * F) = 78504 * coeff m F := by
  have e : (78504 : PowerSeries ℚ) = C (78504 : ℚ) := (map_ofNat C 78504).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80592 : derivative ℚ (80592 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80592
@[simp] lemma cc80592 : constantCoeff (80592 : PowerSeries ℚ) = 80592 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80592
lemma cm80592 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80592 : PowerSeries ℚ) * F) = 80592 * coeff m F := by
  have e : (80592 : PowerSeries ℚ) = C (80592 : ℚ) := (map_ofNat C 80592).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn83280 : derivative ℚ (83280 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 83280
@[simp] lemma cc83280 : constantCoeff (83280 : PowerSeries ℚ) = 83280 := by simpa using map_natCast (constantCoeff (R := ℚ)) 83280
lemma cm83280 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((83280 : PowerSeries ℚ) * F) = 83280 * coeff m F := by
  have e : (83280 : PowerSeries ℚ) = C (83280 : ℚ) := (map_ofNat C 83280).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn106080 : derivative ℚ (106080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 106080
@[simp] lemma cc106080 : constantCoeff (106080 : PowerSeries ℚ) = 106080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 106080
lemma cm106080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((106080 : PowerSeries ℚ) * F) = 106080 * coeff m F := by
  have e : (106080 : PowerSeries ℚ) = C (106080 : ℚ) := (map_ofNat C 106080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn133696 : derivative ℚ (133696 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 133696
@[simp] lemma cc133696 : constantCoeff (133696 : PowerSeries ℚ) = 133696 := by simpa using map_natCast (constantCoeff (R := ℚ)) 133696
lemma cm133696 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((133696 : PowerSeries ℚ) * F) = 133696 * coeff m F := by
  have e : (133696 : PowerSeries ℚ) = C (133696 : ℚ) := (map_ofNat C 133696).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn136800 : derivative ℚ (136800 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 136800
@[simp] lemma cc136800 : constantCoeff (136800 : PowerSeries ℚ) = 136800 := by simpa using map_natCast (constantCoeff (R := ℚ)) 136800
lemma cm136800 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((136800 : PowerSeries ℚ) * F) = 136800 * coeff m F := by
  have e : (136800 : PowerSeries ℚ) = C (136800 : ℚ) := (map_ofNat C 136800).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn154800 : derivative ℚ (154800 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 154800
@[simp] lemma cc154800 : constantCoeff (154800 : PowerSeries ℚ) = 154800 := by simpa using map_natCast (constantCoeff (R := ℚ)) 154800
lemma cm154800 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((154800 : PowerSeries ℚ) * F) = 154800 * coeff m F := by
  have e : (154800 : PowerSeries ℚ) = C (154800 : ℚ) := (map_ofNat C 154800).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn161200 : derivative ℚ (161200 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 161200
@[simp] lemma cc161200 : constantCoeff (161200 : PowerSeries ℚ) = 161200 := by simpa using map_natCast (constantCoeff (R := ℚ)) 161200
lemma cm161200 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((161200 : PowerSeries ℚ) * F) = 161200 * coeff m F := by
  have e : (161200 : PowerSeries ℚ) = C (161200 : ℚ) := (map_ofNat C 161200).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn172800 : derivative ℚ (172800 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 172800
@[simp] lemma cc172800 : constantCoeff (172800 : PowerSeries ℚ) = 172800 := by simpa using map_natCast (constantCoeff (R := ℚ)) 172800
lemma cm172800 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((172800 : PowerSeries ℚ) * F) = 172800 * coeff m F := by
  have e : (172800 : PowerSeries ℚ) = C (172800 : ℚ) := (map_ofNat C 172800).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn200808 : derivative ℚ (200808 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 200808
@[simp] lemma cc200808 : constantCoeff (200808 : PowerSeries ℚ) = 200808 := by simpa using map_natCast (constantCoeff (R := ℚ)) 200808
lemma cm200808 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((200808 : PowerSeries ℚ) * F) = 200808 * coeff m F := by
  have e : (200808 : PowerSeries ℚ) = C (200808 : ℚ) := (map_ofNat C 200808).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn203760 : derivative ℚ (203760 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 203760
@[simp] lemma cc203760 : constantCoeff (203760 : PowerSeries ℚ) = 203760 := by simpa using map_natCast (constantCoeff (R := ℚ)) 203760
lemma cm203760 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((203760 : PowerSeries ℚ) * F) = 203760 * coeff m F := by
  have e : (203760 : PowerSeries ℚ) = C (203760 : ℚ) := (map_ofNat C 203760).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn205440 : derivative ℚ (205440 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 205440
@[simp] lemma cc205440 : constantCoeff (205440 : PowerSeries ℚ) = 205440 := by simpa using map_natCast (constantCoeff (R := ℚ)) 205440
lemma cm205440 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((205440 : PowerSeries ℚ) * F) = 205440 * coeff m F := by
  have e : (205440 : PowerSeries ℚ) = C (205440 : ℚ) := (map_ofNat C 205440).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn206400 : derivative ℚ (206400 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 206400
@[simp] lemma cc206400 : constantCoeff (206400 : PowerSeries ℚ) = 206400 := by simpa using map_natCast (constantCoeff (R := ℚ)) 206400
lemma cm206400 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((206400 : PowerSeries ℚ) * F) = 206400 * coeff m F := by
  have e : (206400 : PowerSeries ℚ) = C (206400 : ℚ) := (map_ofNat C 206400).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn208080 : derivative ℚ (208080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 208080
@[simp] lemma cc208080 : constantCoeff (208080 : PowerSeries ℚ) = 208080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 208080
lemma cm208080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((208080 : PowerSeries ℚ) * F) = 208080 * coeff m F := by
  have e : (208080 : PowerSeries ℚ) = C (208080 : ℚ) := (map_ofNat C 208080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn216000 : derivative ℚ (216000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 216000
@[simp] lemma cc216000 : constantCoeff (216000 : PowerSeries ℚ) = 216000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 216000
lemma cm216000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((216000 : PowerSeries ℚ) * F) = 216000 * coeff m F := by
  have e : (216000 : PowerSeries ℚ) = C (216000 : ℚ) := (map_ofNat C 216000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn239640 : derivative ℚ (239640 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 239640
@[simp] lemma cc239640 : constantCoeff (239640 : PowerSeries ℚ) = 239640 := by simpa using map_natCast (constantCoeff (R := ℚ)) 239640
lemma cm239640 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((239640 : PowerSeries ℚ) * F) = 239640 * coeff m F := by
  have e : (239640 : PowerSeries ℚ) = C (239640 : ℚ) := (map_ofNat C 239640).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn264000 : derivative ℚ (264000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 264000
@[simp] lemma cc264000 : constantCoeff (264000 : PowerSeries ℚ) = 264000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 264000
lemma cm264000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((264000 : PowerSeries ℚ) * F) = 264000 * coeff m F := by
  have e : (264000 : PowerSeries ℚ) = C (264000 : ℚ) := (map_ofNat C 264000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn360000 : derivative ℚ (360000 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 360000
@[simp] lemma cc360000 : constantCoeff (360000 : PowerSeries ℚ) = 360000 := by simpa using map_natCast (constantCoeff (R := ℚ)) 360000
lemma cm360000 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((360000 : PowerSeries ℚ) * F) = 360000 * coeff m F := by
  have e : (360000 : PowerSeries ℚ) = C (360000 : ℚ) := (map_ofNat C 360000).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn403200 : derivative ℚ (403200 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 403200
@[simp] lemma cc403200 : constantCoeff (403200 : PowerSeries ℚ) = 403200 := by simpa using map_natCast (constantCoeff (R := ℚ)) 403200
lemma cm403200 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((403200 : PowerSeries ℚ) * F) = 403200 * coeff m F := by
  have e : (403200 : PowerSeries ℚ) = C (403200 : ℚ) := (map_ofNat C 403200).symm
  rw [e, coeff_C_mul]

set_option maxHeartbeats 8000000 in
lemma ode_G (G : PowerSeries ℚ) (hP : ((1) * G ^ 3 + (1) * G ^ 4 + (-2) * X ^ 1 * G ^ 2 + (-4) * X ^ 1 * G ^ 3 + (1) * X ^ 2 * G ^ 1 + (5) * X ^ 2 * G ^ 2 + (-4) * X ^ 3 * G ^ 1 + (1) * X ^ 4 : PowerSeries ℚ) = 0) : ((2) * X ^ 2 * (derivative ℚ (derivative ℚ G)) + (-6) * X ^ 2 * (derivative ℚ G) + (-8) * X ^ 2 * G ^ 1 + (4) * X ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-14) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (-4) * X ^ 3 * (derivative ℚ G) + (80) * X ^ 3 * G ^ 1 + (-47) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (168) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (-212) * X ^ 4 * (derivative ℚ G) + (-400) * X ^ 4 * G ^ 1 + (152) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-488) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (400) * X ^ 5 * (derivative ℚ G) + (-376) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (2080) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (1024) * X ^ 7 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-1728) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (-752) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (5760) * X ^ 8 * (derivative ℚ (derivative ℚ G)) + (1920) * X ^ 9 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = ((-4) * X ^ 2 + (-32) * X ^ 3 + (-32) * X ^ 4 : PowerSeries ℚ) := by
  have d1 : ((-2) * G ^ 2 + (3) * G ^ 2 * (derivative ℚ G) + (-4) * G ^ 3 + (4) * G ^ 3 * (derivative ℚ G) + (2) * X ^ 1 * G ^ 1 + (-4) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (10) * X ^ 1 * G ^ 2 + (-12) * X ^ 1 * G ^ 2 * (derivative ℚ G) + (1) * X ^ 2 * (derivative ℚ G) + (-12) * X ^ 2 * G ^ 1 + (10) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (4) * X ^ 3 + (-4) * X ^ 3 * (derivative ℚ G) : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) hP
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L1 : ((-4) * X ^ 5 * (derivative ℚ G) + (15) * X ^ 6 * (derivative ℚ G) + (-16) * X ^ 7 * (derivative ℚ G) + (60) * X ^ 8 * (derivative ℚ G) : PowerSeries ℚ) = ((-2) * X ^ 3 * G ^ 2 + (-2) * X ^ 3 * G ^ 3 + (-2) * X ^ 4 * G ^ 1 + (18) * X ^ 4 * G ^ 2 + (16) * X ^ 4 * G ^ 3 + (-6) * X ^ 5 * G ^ 1 + (-50) * X ^ 5 * G ^ 2 + (6) * X ^ 6 + (24) * X ^ 6 * G ^ 1 + (-14) * X ^ 7 + (60) * X ^ 7 * G ^ 1 : PowerSeries ℚ) := by
    linear_combination (((-2) * G ^ 2 + (-2) * G ^ 3 + (2) * X ^ 1 * G ^ 1 + (6) * X ^ 1 * G ^ 2 + (3) * X ^ 2 * G ^ 1 + (33) * X ^ 2 * G ^ 2 + (26) * X ^ 2 * G ^ 3 + (-2) * X ^ 3 + (-68) * X ^ 3 * G ^ 1 + (-100) * X ^ 3 * G ^ 2 + (24) * X ^ 4 + (110) * X ^ 4 * G ^ 1 + (-64) * X ^ 5 : PowerSeries ℚ)) * d1 + (((-4) * G ^ 1 + (6) * G ^ 1 * (derivative ℚ G) + (-8) * G ^ 2 + (8) * G ^ 2 * (derivative ℚ G) + (-2) * X ^ 1 * (derivative ℚ G) + (12) * X ^ 1 * G ^ 1 + (-16) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (2) * X ^ 2 + (-17) * X ^ 2 * (derivative ℚ G) + (80) * X ^ 2 * G ^ 1 + (-106) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (104) * X ^ 2 * G ^ 2 + (-104) * X ^ 2 * G ^ 2 * (derivative ℚ G) + (-82) * X ^ 3 + (144) * X ^ 3 * (derivative ℚ G) + (-244) * X ^ 3 * G ^ 1 + (296) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (256) * X ^ 4 + (-196) * X ^ 4 * (derivative ℚ G) : PowerSeries ℚ)) * hP
  have e2 : ((6) * X ^ 2 * G ^ 2 + (6) * X ^ 2 * G ^ 3 + (8) * X ^ 3 * G ^ 1 + (4) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (-72) * X ^ 3 * G ^ 2 + (6) * X ^ 3 * G ^ 2 * (derivative ℚ G) + (-64) * X ^ 3 * G ^ 3 + (-18) * X ^ 4 * (derivative ℚ G) + (30) * X ^ 4 * G ^ 1 + (-36) * X ^ 4 * G ^ 1 * (derivative ℚ G) + (250) * X ^ 4 * G ^ 2 + (-48) * X ^ 4 * G ^ 2 * (derivative ℚ G) + (-36) * X ^ 5 + (-4) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (96) * X ^ 5 * (derivative ℚ G) + (-144) * X ^ 5 * G ^ 1 + (100) * X ^ 5 * G ^ 1 * (derivative ℚ G) + (98) * X ^ 6 + (15) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (-136) * X ^ 6 * (derivative ℚ G) + (-420) * X ^ 6 * G ^ 1 + (-16) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (420) * X ^ 7 * (derivative ℚ G) + (60) * X ^ 8 * (derivative ℚ (derivative ℚ G)) : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) L1
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L2 : ((16) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (-120) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (353) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (-960) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (2056) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (-1920) * X ^ 8 * (derivative ℚ (derivative ℚ G)) + (3600) * X ^ 9 * (derivative ℚ (derivative ℚ G)) : PowerSeries ℚ) = ((12) * G ^ 2 + (12) * G ^ 3 + (-12) * X ^ 1 * G ^ 1 + (-162) * X ^ 1 * G ^ 2 + (-126) * X ^ 1 * G ^ 3 + (192) * X ^ 2 * G ^ 1 + (676) * X ^ 2 * G ^ 2 + (256) * X ^ 2 * G ^ 3 + (-44) * X ^ 3 + (-706) * X ^ 3 * G ^ 1 + (-990) * X ^ 3 * G ^ 2 + (-128) * X ^ 3 * G ^ 3 + (204) * X ^ 4 + (912) * X ^ 4 * G ^ 1 + (760) * X ^ 4 * G ^ 2 + (-290) * X ^ 5 + (-860) * X ^ 5 * G ^ 1 + (232) * X ^ 6 : PowerSeries ℚ) := by
    have hm : ((1) * X ^ 4 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((1) * X ^ 0 : PowerSeries ℚ)) 4 (by ring) (by simp <;> norm_num)
    apply mul_left_cancel₀ hm
    linear_combination (((-4) * X ^ 2 + (15) * X ^ 3 + (-16) * X ^ 4 + (60) * X ^ 5 : PowerSeries ℚ)) * e2 + (((-4) * G ^ 1 + (-6) * G ^ 2 + (18) * X ^ 1 + (36) * X ^ 1 * G ^ 1 + (48) * X ^ 1 * G ^ 2 + (-96) * X ^ 2 + (-100) * X ^ 2 * G ^ 1 + (136) * X ^ 3 + (-420) * X ^ 4 : PowerSeries ℚ)) * L1 + (((8) * X ^ 3 + (12) * X ^ 3 * G ^ 1 + (-100) * X ^ 4 + (-192) * X ^ 4 * G ^ 1 + (404) * X ^ 5 + (768) * X ^ 5 * G ^ 1 + (-928) * X ^ 6 : PowerSeries ℚ)) * hP
  have e3 : ((12) * G ^ 1 + (-24) * G ^ 1 * (derivative ℚ G) + (162) * G ^ 2 + (-36) * G ^ 2 * (derivative ℚ G) + (126) * G ^ 3 + (12) * X ^ 1 * (derivative ℚ G) + (-384) * X ^ 1 * G ^ 1 + (324) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (-1352) * X ^ 1 * G ^ 2 + (378) * X ^ 1 * G ^ 2 * (derivative ℚ G) + (-512) * X ^ 1 * G ^ 3 + (132) * X ^ 2 + (48) * X ^ 2 * (derivative ℚ (derivative ℚ G)) + (-192) * X ^ 2 * (derivative ℚ G) + (2118) * X ^ 2 * G ^ 1 + (-1352) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (2970) * X ^ 2 * G ^ 2 + (-768) * X ^ 2 * G ^ 2 * (derivative ℚ G) + (384) * X ^ 2 * G ^ 3 + (-816) * X ^ 3 + (16) * X ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-480) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (706) * X ^ 3 * (derivative ℚ G) + (-3648) * X ^ 3 * G ^ 1 + (1980) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (-3040) * X ^ 3 * G ^ 2 + (384) * X ^ 3 * G ^ 2 * (derivative ℚ G) + (1450) * X ^ 4 + (-120) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (1765) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (-912) * X ^ 4 * (derivative ℚ G) + (4300) * X ^ 4 * G ^ 1 + (-1520) * X ^ 4 * G ^ 1 * (derivative ℚ G) + (-1392) * X ^ 5 + (353) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-5760) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (860) * X ^ 5 * (derivative ℚ G) + (-960) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (14392) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (2056) * X ^ 7 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-15360) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (-1920) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (32400) * X ^ 8 * (derivative ℚ (derivative ℚ G)) + (3600) * X ^ 9 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) L2
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L3 : ((-64) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (720) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-3468) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12015) * X ^ 7 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-35472) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (75060) * X ^ 9 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-133696) * X ^ 10 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (208080) * X ^ 11 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-172800) * X ^ 12 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (216000) * X ^ 13 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = ((24) * G ^ 2 + (24) * G ^ 3 + (-24) * X ^ 1 * G ^ 1 + (-348) * X ^ 1 * G ^ 2 + (-276) * X ^ 1 * G ^ 3 + (312) * X ^ 2 * G ^ 1 + (3336) * X ^ 2 * G ^ 2 + (2520) * X ^ 2 * G ^ 3 + (-24) * X ^ 3 + (-3648) * X ^ 3 * G ^ 1 + (-19968) * X ^ 3 * G ^ 2 + (-11784) * X ^ 3 * G ^ 3 + (1008) * X ^ 4 + (20112) * X ^ 4 * G ^ 1 + (78504) * X ^ 4 * G ^ 2 + (42360) * X ^ 4 * G ^ 3 + (-5364) * X ^ 5 + (-80592) * X ^ 5 * G ^ 1 + (-203760) * X ^ 5 * G ^ 2 + (-62112) * X ^ 5 * G ^ 3 + (22512) * X ^ 6 + (200808) * X ^ 6 * G ^ 1 + (239640) * X ^ 6 * G ^ 2 + (23040) * X ^ 6 * G ^ 3 + (-63264) * X ^ 7 + (-206400) * X ^ 7 * G ^ 1 + (-136800) * X ^ 7 * G ^ 2 + (66408) * X ^ 8 + (154800) * X ^ 8 * G ^ 1 + (-41760) * X ^ 9 : PowerSeries ℚ) := by
    have hm : ((1) * X ^ 4 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((1) * X ^ 0 : PowerSeries ℚ)) 4 (by ring) (by simp <;> norm_num)
    apply mul_left_cancel₀ hm
    linear_combination (((-4) * X ^ 5 + (15) * X ^ 6 + (-16) * X ^ 7 + (60) * X ^ 8 : PowerSeries ℚ)) * e3 + (((12) * X ^ 4 + (-75) * X ^ 5 + (112) * X ^ 6 + (-540) * X ^ 7 : PowerSeries ℚ)) * L2 + (((24) * G ^ 1 + (36) * G ^ 2 + (-12) * X ^ 1 + (-324) * X ^ 1 * G ^ 1 + (-378) * X ^ 1 * G ^ 2 + (192) * X ^ 2 + (1352) * X ^ 2 * G ^ 1 + (768) * X ^ 2 * G ^ 2 + (-706) * X ^ 3 + (-1980) * X ^ 3 * G ^ 1 + (-384) * X ^ 3 * G ^ 2 + (912) * X ^ 4 + (1520) * X ^ 4 * G ^ 1 + (-860) * X ^ 5 : PowerSeries ℚ)) * L1 + (((-48) * X ^ 3 + (-72) * X ^ 3 * G ^ 1 + (816) * X ^ 4 + (1332) * X ^ 4 * G ^ 1 + (-5116) * X ^ 5 + (-7584) * X ^ 5 * G ^ 1 + (15692) * X ^ 6 + (13056) * X ^ 6 * G ^ 1 + (-21664) * X ^ 7 + (-6144) * X ^ 7 * G ^ 1 + (18944) * X ^ 8 : PowerSeries ℚ)) * hP
  have hm : ((16) * X ^ 3 + (-120) * X ^ 4 + (289) * X ^ 5 + (-480) * X ^ 6 + (900) * X ^ 7 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((16) * X ^ 0 + (-120) * X ^ 1 + (289) * X ^ 2 + (-480) * X ^ 3 + (900) * X ^ 4 : PowerSeries ℚ)) 3 (by ring) (by simp <;> norm_num)
  apply mul_left_cancel₀ hm
  linear_combination (((24) * X ^ 0 + (-74) * X ^ 1 + (788) * X ^ 2 + (-4780) * X ^ 3 + (6000) * X ^ 4 : PowerSeries ℚ)) * L1 + (((2) * X ^ 2 + (-14) * X ^ 3 + (160) * X ^ 4 + (-432) * X ^ 5 + (1440) * X ^ 6 : PowerSeries ℚ)) * L2 + (((-1) * X ^ 2 + (8) * X ^ 3 : PowerSeries ℚ)) * L3 + ((0 : PowerSeries ℚ)) * hP

set_option maxHeartbeats 4000000 in
lemma rec_a (G : PowerSeries ℚ) (hP : ((1) * G ^ 3 + (1) * G ^ 4 + (-2) * X ^ 1 * G ^ 2 + (-4) * X ^ 1 * G ^ 3 + (1) * X ^ 2 * G ^ 1 + (5) * X ^ 2 * G ^ 2 + (-4) * X ^ 3 * G ^ 1 + (1) * X ^ 4 : PowerSeries ℚ) = 0) (k : ℕ) : (4*((k + 6 : ℕ) : ℚ)^3 - 10*((k + 6 : ℕ) : ℚ)^2 + 6*((k + 6 : ℕ) : ℚ)) * coeff (k + 6) G + (-47*((k + 6 : ℕ) : ℚ)^3 + 268*((k + 6 : ℕ) : ℚ)^2 - 481*((k + 6 : ℕ) : ℚ) + 260) * coeff (k + 5) G + (152*((k + 6 : ℕ) : ℚ)^3 - 1200*((k + 6 : ℕ) : ℚ)^2 + 3108*((k + 6 : ℕ) : ℚ) - 2640) * coeff (k + 4) G + (-376*((k + 6 : ℕ) : ℚ)^3 + 4024*((k + 6 : ℕ) : ℚ)^2 - 14468*((k + 6 : ℕ) : ℚ) + 17420) * coeff (k + 3) G + (1024*((k + 6 : ℕ) : ℚ)^3 - 13280*((k + 6 : ℕ) : ℚ)^2 + 57456*((k + 6 : ℕ) : ℚ) - 83280) * coeff (k + 2) G + (-752*((k + 6 : ℕ) : ℚ)^3 + 11808*((k + 6 : ℕ) : ℚ)^2 - 61456*((k + 6 : ℕ) : ℚ) + 106080) * coeff (k + 1) G + (1920*((k + 6 : ℕ) : ℚ)^3 - 34560*((k + 6 : ℕ) : ℚ)^2 + 205440*((k + 6 : ℕ) : ℚ) - 403200) * coeff (k + 0) G = 0 := by
  have h := congrArg (coeff (k + 6)) (ode_G G hP)
  rcases k with _ | _ | _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13, cm14, cm15, cm16, cm17, cm18, cm24, cm26, cm30, cm32, cm33, cm36, cm44, cm47, cm48, cm50, cm60, cm64, cm68, cm72, cm74, cm75, cm80, cm82, cm96, cm98, cm100, cm104, cm106, cm110, cm112, cm120, cm126, cm128, cm132, cm136, cm144, cm152, cm160, cm162, cm168, cm192, cm196, cm204, cm212, cm232, cm244, cm250, cm256, cm260, cm268, cm276, cm289, cm290, cm296, cm312, cm324, cm348, cm353, cm376, cm378, cm384, cm400, cm404, cm420, cm432, cm480, cm481, cm488, cm512, cm540, cm676, cm706, cm720, cm752, cm760, cm768, cm788, cm816, cm860, cm900, cm912, cm928, cm960, cm990, cm1008, cm1024, cm1200, cm1332, cm1352, cm1392, cm1440, cm1450, cm1520, cm1728, cm1765, cm1920, cm1980, cm2056, cm2080, cm2118, cm2240, cm2520, cm2640, cm2970, cm3040, cm3108, cm3336, cm3468, cm3600, cm3648, cm4024, cm4300, cm4780, cm5116, cm5364, cm5760, cm6000, cm6144, cm7584, cm11784, cm11808, cm12015, cm13056, cm13280, cm14392, cm14468, cm15360, cm15692, cm17420, cm18312, cm18944, cm19968, cm20112, cm21664, cm22512, cm23040, cm32400, cm34560, cm35472, cm41760, cm42360, cm57456, cm61456, cm62112, cm63264, cm66408, cm74960, cm75060, cm78504, cm80592, cm83280, cm106080, cm133696, cm136800, cm154800, cm161200, cm172800, cm200808, cm203760, cm205440, cm206400, cm208080, cm216000, cm239640, cm264000, cm360000, cm403200, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h

end OMA.S_oeis_a243816

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a243816.main := by
  intro T U G hT hT0 hU hU0 hG hG0 n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hP : ((1) * G ^ 3 + (1) * G ^ 4 + (-2) * X ^ 1 * G ^ 2 + (-4) * X ^ 1 * G ^ 3 + (1) * X ^ 2 * G ^ 1 + (5) * X ^ 2 * G ^ 2 + (-4) * X ^ 3 * G ^ 1 + (1) * X ^ 4 : PowerSeries ℚ) = 0 := by
    have hx : (256 * X ^ 8 : PowerSeries ℚ) * (X^4 - 4*X^3*G + 5*X^2*G^2 + X^2*G - 4*X*G^3 - 2*X*G^2 + G^4 + G^3) = 0 := by
      linear_combination (32*G^4*U*X^5 - 64*G^4*X^6 - 32*G^4*X^5 - 32*G^3*U*X^7 - 96*G^3*U*X^6 + 288*G^3*X^7 + 32*G^3*X^6 + 32*G^2*U*X^8 + 96*G^2*U*X^7 - 352*G^2*X^8 + 32*G^2*X^7 - 32*G*U*X^8 + 256*G*X^9 - 32*G*X^8 - 64*X^10) * hT + (-16*G^4*T*U*X^5 + 32*G^4*T*X^6 + 16*G^4*T*X^5 - 16*G^4*U^2*X^6 + 32*G^4*U*X^7 + 16*G^4*U*X^5 + 32*G^4*X^7 - 16*G^4*X^6 + 48*G^4*X^5 + 16*G^3*T*U*X^7 + 48*G^3*T*U*X^6 - 144*G^3*T*X^7 - 16*G^3*T*X^6 + 16*G^3*U^2*X^8 + 32*G^3*U^2*X^7 - 96*G^3*U*X^8 - 16*G^3*U*X^7 - 48*G^3*U*X^6 - 48*G^3*X^8 + 48*G^3*X^7 - 112*G^3*X^6 - 16*G^2*T*U*X^8 - 48*G^2*T*U*X^7 + 176*G^2*T*X^8 - 16*G^2*T*X^7 - 16*G^2*U^2*X^8 + 96*G^2*U*X^9 + 16*G^2*U*X^8 + 48*G^2*U*X^7 - 32*G^2*X^9 - 160*G^2*X^8 + 80*G^2*X^7 + 16*G*T*U*X^8 - 128*G*T*X^9 + 16*G*T*X^8 - 32*G*U*X^10 - 16*G*U*X^8 + 32*G*X^10 + 128*G*X^9 - 16*G*X^8 + 32*T*X^10 - 32*X^10) * hU + (16*G^3*U^3*X^6 - 32*G^3*U^2*X^7 + 16*G^3*U^2*X^6 - 64*G^3*U*X^7 - 16*G^3*U*X^6 - 64*G^3*U*X^5 - 32*G^3*X^7 + 112*G^3*X^6 - 64*G^3*X^5 - 16*G^2*U^3*X^8 - 32*G^2*U^3*X^7 + 80*G^2*U^2*X^8 - 32*G^2*U^2*X^7 + 144*G^2*U*X^8 + 96*G^2*U*X^7 + 128*G^2*U*X^6 - 80*G^2*X^8 - 288*G^2*X^7 + 128*G^2*X^6 + 16*G*U^3*X^8 - 96*G*U^2*X^9 + 16*G*U^2*X^8 - 64*G*U*X^9 - 16*G*U*X^8 - 64*G*U*X^7 + 160*G*X^9 + 368*G*X^8 - 64*G*X^7 + 32*U^2*X^10 - 32*X^10 - 128*X^9) * hG
    have hne : (256 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
      intro h0
      have h1 := congrArg PowerSeries.constantCoeff h0
      have h2 : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := by simpa using map_natCast (PowerSeries.constantCoeff (R := ℚ)) 256
      rw [h2] at h1
      norm_num at h1
    have h3 := (mul_eq_zero.1 hx).resolve_left hne
    linear_combination h3
  have h := OMA.S_oeis_a243816.rec_a G hP k
  simp only [show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 6 - 5 = k + 1 from by omega, show k + 6 - 6 = k + 0 from by omega]
  push_cast at h ⊢
  linear_combination h
