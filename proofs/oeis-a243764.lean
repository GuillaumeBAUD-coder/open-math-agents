import OMAStatements.S_oeis_a243764
import Mathlib

namespace OMA.S_oeis_a243764

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
@[simp] lemma dn14 : derivative ℚ (14 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14
@[simp] lemma cc14 : constantCoeff (14 : PowerSeries ℚ) = 14 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14
lemma cm14 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14 : PowerSeries ℚ) * F) = 14 * coeff m F := by
  have e : (14 : PowerSeries ℚ) = C (14 : ℚ) := (map_ofNat C 14).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16 : derivative ℚ (16 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16
@[simp] lemma cc16 : constantCoeff (16 : PowerSeries ℚ) = 16 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16
lemma cm16 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16 : PowerSeries ℚ) * F) = 16 * coeff m F := by
  have e : (16 : PowerSeries ℚ) = C (16 : ℚ) := (map_ofNat C 16).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn21 : derivative ℚ (21 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 21
@[simp] lemma cc21 : constantCoeff (21 : PowerSeries ℚ) = 21 := by simpa using map_natCast (constantCoeff (R := ℚ)) 21
lemma cm21 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((21 : PowerSeries ℚ) * F) = 21 * coeff m F := by
  have e : (21 : PowerSeries ℚ) = C (21 : ℚ) := (map_ofNat C 21).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32 : derivative ℚ (32 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32
@[simp] lemma cc32 : constantCoeff (32 : PowerSeries ℚ) = 32 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32
lemma cm32 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32 : PowerSeries ℚ) * F) = 32 * coeff m F := by
  have e : (32 : PowerSeries ℚ) = C (32 : ℚ) := (map_ofNat C 32).symm
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
@[simp] lemma dn42 : derivative ℚ (42 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 42
@[simp] lemma cc42 : constantCoeff (42 : PowerSeries ℚ) = 42 := by simpa using map_natCast (constantCoeff (R := ℚ)) 42
lemma cm42 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((42 : PowerSeries ℚ) * F) = 42 * coeff m F := by
  have e : (42 : PowerSeries ℚ) = C (42 : ℚ) := (map_ofNat C 42).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn44 : derivative ℚ (44 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 44
@[simp] lemma cc44 : constantCoeff (44 : PowerSeries ℚ) = 44 := by simpa using map_natCast (constantCoeff (R := ℚ)) 44
lemma cm44 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((44 : PowerSeries ℚ) * F) = 44 * coeff m F := by
  have e : (44 : PowerSeries ℚ) = C (44 : ℚ) := (map_ofNat C 44).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn48 : derivative ℚ (48 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 48
@[simp] lemma cc48 : constantCoeff (48 : PowerSeries ℚ) = 48 := by simpa using map_natCast (constantCoeff (R := ℚ)) 48
lemma cm48 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((48 : PowerSeries ℚ) * F) = 48 * coeff m F := by
  have e : (48 : PowerSeries ℚ) = C (48 : ℚ) := (map_ofNat C 48).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn49 : derivative ℚ (49 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 49
@[simp] lemma cc49 : constantCoeff (49 : PowerSeries ℚ) = 49 := by simpa using map_natCast (constantCoeff (R := ℚ)) 49
lemma cm49 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((49 : PowerSeries ℚ) * F) = 49 * coeff m F := by
  have e : (49 : PowerSeries ℚ) = C (49 : ℚ) := (map_ofNat C 49).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn50 : derivative ℚ (50 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 50
@[simp] lemma cc50 : constantCoeff (50 : PowerSeries ℚ) = 50 := by simpa using map_natCast (constantCoeff (R := ℚ)) 50
lemma cm50 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((50 : PowerSeries ℚ) * F) = 50 * coeff m F := by
  have e : (50 : PowerSeries ℚ) = C (50 : ℚ) := (map_ofNat C 50).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn56 : derivative ℚ (56 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 56
@[simp] lemma cc56 : constantCoeff (56 : PowerSeries ℚ) = 56 := by simpa using map_natCast (constantCoeff (R := ℚ)) 56
lemma cm56 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((56 : PowerSeries ℚ) * F) = 56 * coeff m F := by
  have e : (56 : PowerSeries ℚ) = C (56 : ℚ) := (map_ofNat C 56).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn64 : derivative ℚ (64 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 64
@[simp] lemma cc64 : constantCoeff (64 : PowerSeries ℚ) = 64 := by simpa using map_natCast (constantCoeff (R := ℚ)) 64
lemma cm64 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((64 : PowerSeries ℚ) * F) = 64 * coeff m F := by
  have e : (64 : PowerSeries ℚ) = C (64 : ℚ) := (map_ofNat C 64).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn70 : derivative ℚ (70 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 70
@[simp] lemma cc70 : constantCoeff (70 : PowerSeries ℚ) = 70 := by simpa using map_natCast (constantCoeff (R := ℚ)) 70
lemma cm70 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((70 : PowerSeries ℚ) * F) = 70 * coeff m F := by
  have e : (70 : PowerSeries ℚ) = C (70 : ℚ) := (map_ofNat C 70).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80 : derivative ℚ (80 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80
@[simp] lemma cc80 : constantCoeff (80 : PowerSeries ℚ) = 80 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80
lemma cm80 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80 : PowerSeries ℚ) * F) = 80 * coeff m F := by
  have e : (80 : PowerSeries ℚ) = C (80 : ℚ) := (map_ofNat C 80).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn84 : derivative ℚ (84 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 84
@[simp] lemma cc84 : constantCoeff (84 : PowerSeries ℚ) = 84 := by simpa using map_natCast (constantCoeff (R := ℚ)) 84
lemma cm84 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((84 : PowerSeries ℚ) * F) = 84 * coeff m F := by
  have e : (84 : PowerSeries ℚ) = C (84 : ℚ) := (map_ofNat C 84).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn91 : derivative ℚ (91 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 91
@[simp] lemma cc91 : constantCoeff (91 : PowerSeries ℚ) = 91 := by simpa using map_natCast (constantCoeff (R := ℚ)) 91
lemma cm91 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((91 : PowerSeries ℚ) * F) = 91 * coeff m F := by
  have e : (91 : PowerSeries ℚ) = C (91 : ℚ) := (map_ofNat C 91).symm
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
@[simp] lemma dn105 : derivative ℚ (105 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 105
@[simp] lemma cc105 : constantCoeff (105 : PowerSeries ℚ) = 105 := by simpa using map_natCast (constantCoeff (R := ℚ)) 105
lemma cm105 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((105 : PowerSeries ℚ) * F) = 105 * coeff m F := by
  have e : (105 : PowerSeries ℚ) = C (105 : ℚ) := (map_ofNat C 105).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn116 : derivative ℚ (116 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 116
@[simp] lemma cc116 : constantCoeff (116 : PowerSeries ℚ) = 116 := by simpa using map_natCast (constantCoeff (R := ℚ)) 116
lemma cm116 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((116 : PowerSeries ℚ) * F) = 116 * coeff m F := by
  have e : (116 : PowerSeries ℚ) = C (116 : ℚ) := (map_ofNat C 116).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn124 : derivative ℚ (124 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 124
@[simp] lemma cc124 : constantCoeff (124 : PowerSeries ℚ) = 124 := by simpa using map_natCast (constantCoeff (R := ℚ)) 124
lemma cm124 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((124 : PowerSeries ℚ) * F) = 124 * coeff m F := by
  have e : (124 : PowerSeries ℚ) = C (124 : ℚ) := (map_ofNat C 124).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn128 : derivative ℚ (128 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 128
@[simp] lemma cc128 : constantCoeff (128 : PowerSeries ℚ) = 128 := by simpa using map_natCast (constantCoeff (R := ℚ)) 128
lemma cm128 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((128 : PowerSeries ℚ) * F) = 128 * coeff m F := by
  have e : (128 : PowerSeries ℚ) = C (128 : ℚ) := (map_ofNat C 128).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn140 : derivative ℚ (140 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 140
@[simp] lemma cc140 : constantCoeff (140 : PowerSeries ℚ) = 140 := by simpa using map_natCast (constantCoeff (R := ℚ)) 140
lemma cm140 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((140 : PowerSeries ℚ) * F) = 140 * coeff m F := by
  have e : (140 : PowerSeries ℚ) = C (140 : ℚ) := (map_ofNat C 140).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn147 : derivative ℚ (147 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 147
@[simp] lemma cc147 : constantCoeff (147 : PowerSeries ℚ) = 147 := by simpa using map_natCast (constantCoeff (R := ℚ)) 147
lemma cm147 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((147 : PowerSeries ℚ) * F) = 147 * coeff m F := by
  have e : (147 : PowerSeries ℚ) = C (147 : ℚ) := (map_ofNat C 147).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn157 : derivative ℚ (157 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 157
@[simp] lemma cc157 : constantCoeff (157 : PowerSeries ℚ) = 157 := by simpa using map_natCast (constantCoeff (R := ℚ)) 157
lemma cm157 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((157 : PowerSeries ℚ) * F) = 157 * coeff m F := by
  have e : (157 : PowerSeries ℚ) = C (157 : ℚ) := (map_ofNat C 157).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn160 : derivative ℚ (160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 160
@[simp] lemma cc160 : constantCoeff (160 : PowerSeries ℚ) = 160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 160
lemma cm160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((160 : PowerSeries ℚ) * F) = 160 * coeff m F := by
  have e : (160 : PowerSeries ℚ) = C (160 : ℚ) := (map_ofNat C 160).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn164 : derivative ℚ (164 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 164
@[simp] lemma cc164 : constantCoeff (164 : PowerSeries ℚ) = 164 := by simpa using map_natCast (constantCoeff (R := ℚ)) 164
lemma cm164 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((164 : PowerSeries ℚ) * F) = 164 * coeff m F := by
  have e : (164 : PowerSeries ℚ) = C (164 : ℚ) := (map_ofNat C 164).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn168 : derivative ℚ (168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 168
@[simp] lemma cc168 : constantCoeff (168 : PowerSeries ℚ) = 168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 168
lemma cm168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((168 : PowerSeries ℚ) * F) = 168 * coeff m F := by
  have e : (168 : PowerSeries ℚ) = C (168 : ℚ) := (map_ofNat C 168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn186 : derivative ℚ (186 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 186
@[simp] lemma cc186 : constantCoeff (186 : PowerSeries ℚ) = 186 := by simpa using map_natCast (constantCoeff (R := ℚ)) 186
lemma cm186 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((186 : PowerSeries ℚ) * F) = 186 * coeff m F := by
  have e : (186 : PowerSeries ℚ) = C (186 : ℚ) := (map_ofNat C 186).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn196 : derivative ℚ (196 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 196
@[simp] lemma cc196 : constantCoeff (196 : PowerSeries ℚ) = 196 := by simpa using map_natCast (constantCoeff (R := ℚ)) 196
lemma cm196 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((196 : PowerSeries ℚ) * F) = 196 * coeff m F := by
  have e : (196 : PowerSeries ℚ) = C (196 : ℚ) := (map_ofNat C 196).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn200 : derivative ℚ (200 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 200
@[simp] lemma cc200 : constantCoeff (200 : PowerSeries ℚ) = 200 := by simpa using map_natCast (constantCoeff (R := ℚ)) 200
lemma cm200 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((200 : PowerSeries ℚ) * F) = 200 * coeff m F := by
  have e : (200 : PowerSeries ℚ) = C (200 : ℚ) := (map_ofNat C 200).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn210 : derivative ℚ (210 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 210
@[simp] lemma cc210 : constantCoeff (210 : PowerSeries ℚ) = 210 := by simpa using map_natCast (constantCoeff (R := ℚ)) 210
lemma cm210 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((210 : PowerSeries ℚ) * F) = 210 * coeff m F := by
  have e : (210 : PowerSeries ℚ) = C (210 : ℚ) := (map_ofNat C 210).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn238 : derivative ℚ (238 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 238
@[simp] lemma cc238 : constantCoeff (238 : PowerSeries ℚ) = 238 := by simpa using map_natCast (constantCoeff (R := ℚ)) 238
lemma cm238 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((238 : PowerSeries ℚ) * F) = 238 * coeff m F := by
  have e : (238 : PowerSeries ℚ) = C (238 : ℚ) := (map_ofNat C 238).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn245 : derivative ℚ (245 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 245
@[simp] lemma cc245 : constantCoeff (245 : PowerSeries ℚ) = 245 := by simpa using map_natCast (constantCoeff (R := ℚ)) 245
lemma cm245 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((245 : PowerSeries ℚ) * F) = 245 * coeff m F := by
  have e : (245 : PowerSeries ℚ) = C (245 : ℚ) := (map_ofNat C 245).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn256 : derivative ℚ (256 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 256
@[simp] lemma cc256 : constantCoeff (256 : PowerSeries ℚ) = 256 := by simpa using map_natCast (constantCoeff (R := ℚ)) 256
lemma cm256 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((256 : PowerSeries ℚ) * F) = 256 * coeff m F := by
  have e : (256 : PowerSeries ℚ) = C (256 : ℚ) := (map_ofNat C 256).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn268 : derivative ℚ (268 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 268
@[simp] lemma cc268 : constantCoeff (268 : PowerSeries ℚ) = 268 := by simpa using map_natCast (constantCoeff (R := ℚ)) 268
lemma cm268 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((268 : PowerSeries ℚ) * F) = 268 * coeff m F := by
  have e : (268 : PowerSeries ℚ) = C (268 : ℚ) := (map_ofNat C 268).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn272 : derivative ℚ (272 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 272
@[simp] lemma cc272 : constantCoeff (272 : PowerSeries ℚ) = 272 := by simpa using map_natCast (constantCoeff (R := ℚ)) 272
lemma cm272 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((272 : PowerSeries ℚ) * F) = 272 * coeff m F := by
  have e : (272 : PowerSeries ℚ) = C (272 : ℚ) := (map_ofNat C 272).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn294 : derivative ℚ (294 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 294
@[simp] lemma cc294 : constantCoeff (294 : PowerSeries ℚ) = 294 := by simpa using map_natCast (constantCoeff (R := ℚ)) 294
lemma cm294 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((294 : PowerSeries ℚ) * F) = 294 * coeff m F := by
  have e : (294 : PowerSeries ℚ) = C (294 : ℚ) := (map_ofNat C 294).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn320 : derivative ℚ (320 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 320
@[simp] lemma cc320 : constantCoeff (320 : PowerSeries ℚ) = 320 := by simpa using map_natCast (constantCoeff (R := ℚ)) 320
lemma cm320 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((320 : PowerSeries ℚ) * F) = 320 * coeff m F := by
  have e : (320 : PowerSeries ℚ) = C (320 : ℚ) := (map_ofNat C 320).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn343 : derivative ℚ (343 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 343
@[simp] lemma cc343 : constantCoeff (343 : PowerSeries ℚ) = 343 := by simpa using map_natCast (constantCoeff (R := ℚ)) 343
lemma cm343 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((343 : PowerSeries ℚ) * F) = 343 * coeff m F := by
  have e : (343 : PowerSeries ℚ) = C (343 : ℚ) := (map_ofNat C 343).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn352 : derivative ℚ (352 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 352
@[simp] lemma cc352 : constantCoeff (352 : PowerSeries ℚ) = 352 := by simpa using map_natCast (constantCoeff (R := ℚ)) 352
lemma cm352 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((352 : PowerSeries ℚ) * F) = 352 * coeff m F := by
  have e : (352 : PowerSeries ℚ) = C (352 : ℚ) := (map_ofNat C 352).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn376 : derivative ℚ (376 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 376
@[simp] lemma cc376 : constantCoeff (376 : PowerSeries ℚ) = 376 := by simpa using map_natCast (constantCoeff (R := ℚ)) 376
lemma cm376 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((376 : PowerSeries ℚ) * F) = 376 * coeff m F := by
  have e : (376 : PowerSeries ℚ) = C (376 : ℚ) := (map_ofNat C 376).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn384 : derivative ℚ (384 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 384
@[simp] lemma cc384 : constantCoeff (384 : PowerSeries ℚ) = 384 := by simpa using map_natCast (constantCoeff (R := ℚ)) 384
lemma cm384 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((384 : PowerSeries ℚ) * F) = 384 * coeff m F := by
  have e : (384 : PowerSeries ℚ) = C (384 : ℚ) := (map_ofNat C 384).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn392 : derivative ℚ (392 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 392
@[simp] lemma cc392 : constantCoeff (392 : PowerSeries ℚ) = 392 := by simpa using map_natCast (constantCoeff (R := ℚ)) 392
lemma cm392 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((392 : PowerSeries ℚ) * F) = 392 * coeff m F := by
  have e : (392 : PowerSeries ℚ) = C (392 : ℚ) := (map_ofNat C 392).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn420 : derivative ℚ (420 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 420
@[simp] lemma cc420 : constantCoeff (420 : PowerSeries ℚ) = 420 := by simpa using map_natCast (constantCoeff (R := ℚ)) 420
lemma cm420 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((420 : PowerSeries ℚ) * F) = 420 * coeff m F := by
  have e : (420 : PowerSeries ℚ) = C (420 : ℚ) := (map_ofNat C 420).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn424 : derivative ℚ (424 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 424
@[simp] lemma cc424 : constantCoeff (424 : PowerSeries ℚ) = 424 := by simpa using map_natCast (constantCoeff (R := ℚ)) 424
lemma cm424 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((424 : PowerSeries ℚ) * F) = 424 * coeff m F := by
  have e : (424 : PowerSeries ℚ) = C (424 : ℚ) := (map_ofNat C 424).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn464 : derivative ℚ (464 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 464
@[simp] lemma cc464 : constantCoeff (464 : PowerSeries ℚ) = 464 := by simpa using map_natCast (constantCoeff (R := ℚ)) 464
lemma cm464 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((464 : PowerSeries ℚ) * F) = 464 * coeff m F := by
  have e : (464 : PowerSeries ℚ) = C (464 : ℚ) := (map_ofNat C 464).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn480 : derivative ℚ (480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 480
@[simp] lemma cc480 : constantCoeff (480 : PowerSeries ℚ) = 480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 480
lemma cm480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((480 : PowerSeries ℚ) * F) = 480 * coeff m F := by
  have e : (480 : PowerSeries ℚ) = C (480 : ℚ) := (map_ofNat C 480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn490 : derivative ℚ (490 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 490
@[simp] lemma cc490 : constantCoeff (490 : PowerSeries ℚ) = 490 := by simpa using map_natCast (constantCoeff (R := ℚ)) 490
lemma cm490 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((490 : PowerSeries ℚ) * F) = 490 * coeff m F := by
  have e : (490 : PowerSeries ℚ) = C (490 : ℚ) := (map_ofNat C 490).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn496 : derivative ℚ (496 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 496
@[simp] lemma cc496 : constantCoeff (496 : PowerSeries ℚ) = 496 := by simpa using map_natCast (constantCoeff (R := ℚ)) 496
lemma cm496 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((496 : PowerSeries ℚ) * F) = 496 * coeff m F := by
  have e : (496 : PowerSeries ℚ) = C (496 : ℚ) := (map_ofNat C 496).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn504 : derivative ℚ (504 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 504
@[simp] lemma cc504 : constantCoeff (504 : PowerSeries ℚ) = 504 := by simpa using map_natCast (constantCoeff (R := ℚ)) 504
lemma cm504 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((504 : PowerSeries ℚ) * F) = 504 * coeff m F := by
  have e : (504 : PowerSeries ℚ) = C (504 : ℚ) := (map_ofNat C 504).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn512 : derivative ℚ (512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 512
@[simp] lemma cc512 : constantCoeff (512 : PowerSeries ℚ) = 512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 512
lemma cm512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((512 : PowerSeries ℚ) * F) = 512 * coeff m F := by
  have e : (512 : PowerSeries ℚ) = C (512 : ℚ) := (map_ofNat C 512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn536 : derivative ℚ (536 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 536
@[simp] lemma cc536 : constantCoeff (536 : PowerSeries ℚ) = 536 := by simpa using map_natCast (constantCoeff (R := ℚ)) 536
lemma cm536 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((536 : PowerSeries ℚ) * F) = 536 * coeff m F := by
  have e : (536 : PowerSeries ℚ) = C (536 : ℚ) := (map_ofNat C 536).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn544 : derivative ℚ (544 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 544
@[simp] lemma cc544 : constantCoeff (544 : PowerSeries ℚ) = 544 := by simpa using map_natCast (constantCoeff (R := ℚ)) 544
lemma cm544 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((544 : PowerSeries ℚ) * F) = 544 * coeff m F := by
  have e : (544 : PowerSeries ℚ) = C (544 : ℚ) := (map_ofNat C 544).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn592 : derivative ℚ (592 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 592
@[simp] lemma cc592 : constantCoeff (592 : PowerSeries ℚ) = 592 := by simpa using map_natCast (constantCoeff (R := ℚ)) 592
lemma cm592 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((592 : PowerSeries ℚ) * F) = 592 * coeff m F := by
  have e : (592 : PowerSeries ℚ) = C (592 : ℚ) := (map_ofNat C 592).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn610 : derivative ℚ (610 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 610
@[simp] lemma cc610 : constantCoeff (610 : PowerSeries ℚ) = 610 := by simpa using map_natCast (constantCoeff (R := ℚ)) 610
lemma cm610 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((610 : PowerSeries ℚ) * F) = 610 * coeff m F := by
  have e : (610 : PowerSeries ℚ) = C (610 : ℚ) := (map_ofNat C 610).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn616 : derivative ℚ (616 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 616
@[simp] lemma cc616 : constantCoeff (616 : PowerSeries ℚ) = 616 := by simpa using map_natCast (constantCoeff (R := ℚ)) 616
lemma cm616 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((616 : PowerSeries ℚ) * F) = 616 * coeff m F := by
  have e : (616 : PowerSeries ℚ) = C (616 : ℚ) := (map_ofNat C 616).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn624 : derivative ℚ (624 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 624
@[simp] lemma cc624 : constantCoeff (624 : PowerSeries ℚ) = 624 := by simpa using map_natCast (constantCoeff (R := ℚ)) 624
lemma cm624 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((624 : PowerSeries ℚ) * F) = 624 * coeff m F := by
  have e : (624 : PowerSeries ℚ) = C (624 : ℚ) := (map_ofNat C 624).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn640 : derivative ℚ (640 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 640
@[simp] lemma cc640 : constantCoeff (640 : PowerSeries ℚ) = 640 := by simpa using map_natCast (constantCoeff (R := ℚ)) 640
lemma cm640 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((640 : PowerSeries ℚ) * F) = 640 * coeff m F := by
  have e : (640 : PowerSeries ℚ) = C (640 : ℚ) := (map_ofNat C 640).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn656 : derivative ℚ (656 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 656
@[simp] lemma cc656 : constantCoeff (656 : PowerSeries ℚ) = 656 := by simpa using map_natCast (constantCoeff (R := ℚ)) 656
lemma cm656 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((656 : PowerSeries ℚ) * F) = 656 * coeff m F := by
  have e : (656 : PowerSeries ℚ) = C (656 : ℚ) := (map_ofNat C 656).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn672 : derivative ℚ (672 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 672
@[simp] lemma cc672 : constantCoeff (672 : PowerSeries ℚ) = 672 := by simpa using map_natCast (constantCoeff (R := ℚ)) 672
lemma cm672 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((672 : PowerSeries ℚ) * F) = 672 * coeff m F := by
  have e : (672 : PowerSeries ℚ) = C (672 : ℚ) := (map_ofNat C 672).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn735 : derivative ℚ (735 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 735
@[simp] lemma cc735 : constantCoeff (735 : PowerSeries ℚ) = 735 := by simpa using map_natCast (constantCoeff (R := ℚ)) 735
lemma cm735 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((735 : PowerSeries ℚ) * F) = 735 * coeff m F := by
  have e : (735 : PowerSeries ℚ) = C (735 : ℚ) := (map_ofNat C 735).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn768 : derivative ℚ (768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 768
@[simp] lemma cc768 : constantCoeff (768 : PowerSeries ℚ) = 768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 768
lemma cm768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((768 : PowerSeries ℚ) * F) = 768 * coeff m F := by
  have e : (768 : PowerSeries ℚ) = C (768 : ℚ) := (map_ofNat C 768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn824 : derivative ℚ (824 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 824
@[simp] lemma cc824 : constantCoeff (824 : PowerSeries ℚ) = 824 := by simpa using map_natCast (constantCoeff (R := ℚ)) 824
lemma cm824 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((824 : PowerSeries ℚ) * F) = 824 * coeff m F := by
  have e : (824 : PowerSeries ℚ) = C (824 : ℚ) := (map_ofNat C 824).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn832 : derivative ℚ (832 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 832
@[simp] lemma cc832 : constantCoeff (832 : PowerSeries ℚ) = 832 := by simpa using map_natCast (constantCoeff (R := ℚ)) 832
lemma cm832 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((832 : PowerSeries ℚ) * F) = 832 * coeff m F := by
  have e : (832 : PowerSeries ℚ) = C (832 : ℚ) := (map_ofNat C 832).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn840 : derivative ℚ (840 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 840
@[simp] lemma cc840 : constantCoeff (840 : PowerSeries ℚ) = 840 := by simpa using map_natCast (constantCoeff (R := ℚ)) 840
lemma cm840 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((840 : PowerSeries ℚ) * F) = 840 * coeff m F := by
  have e : (840 : PowerSeries ℚ) = C (840 : ℚ) := (map_ofNat C 840).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn924 : derivative ℚ (924 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 924
@[simp] lemma cc924 : constantCoeff (924 : PowerSeries ℚ) = 924 := by simpa using map_natCast (constantCoeff (R := ℚ)) 924
lemma cm924 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((924 : PowerSeries ℚ) * F) = 924 * coeff m F := by
  have e : (924 : PowerSeries ℚ) = C (924 : ℚ) := (map_ofNat C 924).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn936 : derivative ℚ (936 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 936
@[simp] lemma cc936 : constantCoeff (936 : PowerSeries ℚ) = 936 := by simpa using map_natCast (constantCoeff (R := ℚ)) 936
lemma cm936 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((936 : PowerSeries ℚ) * F) = 936 * coeff m F := by
  have e : (936 : PowerSeries ℚ) = C (936 : ℚ) := (map_ofNat C 936).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn960 : derivative ℚ (960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 960
@[simp] lemma cc960 : constantCoeff (960 : PowerSeries ℚ) = 960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 960
lemma cm960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((960 : PowerSeries ℚ) * F) = 960 * coeff m F := by
  have e : (960 : PowerSeries ℚ) = C (960 : ℚ) := (map_ofNat C 960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn980 : derivative ℚ (980 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 980
@[simp] lemma cc980 : constantCoeff (980 : PowerSeries ℚ) = 980 := by simpa using map_natCast (constantCoeff (R := ℚ)) 980
lemma cm980 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((980 : PowerSeries ℚ) * F) = 980 * coeff m F := by
  have e : (980 : PowerSeries ℚ) = C (980 : ℚ) := (map_ofNat C 980).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1024 : derivative ℚ (1024 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1024
@[simp] lemma cc1024 : constantCoeff (1024 : PowerSeries ℚ) = 1024 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1024
lemma cm1024 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1024 : PowerSeries ℚ) * F) = 1024 * coeff m F := by
  have e : (1024 : PowerSeries ℚ) = C (1024 : ℚ) := (map_ofNat C 1024).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1072 : derivative ℚ (1072 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1072
@[simp] lemma cc1072 : constantCoeff (1072 : PowerSeries ℚ) = 1072 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1072
lemma cm1072 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1072 : PowerSeries ℚ) * F) = 1072 * coeff m F := by
  have e : (1072 : PowerSeries ℚ) = C (1072 : ℚ) := (map_ofNat C 1072).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1088 : derivative ℚ (1088 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1088
@[simp] lemma cc1088 : constantCoeff (1088 : PowerSeries ℚ) = 1088 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1088
lemma cm1088 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1088 : PowerSeries ℚ) * F) = 1088 * coeff m F := by
  have e : (1088 : PowerSeries ℚ) = C (1088 : ℚ) := (map_ofNat C 1088).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1120 : derivative ℚ (1120 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1120
@[simp] lemma cc1120 : constantCoeff (1120 : PowerSeries ℚ) = 1120 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1120
lemma cm1120 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1120 : PowerSeries ℚ) * F) = 1120 * coeff m F := by
  have e : (1120 : PowerSeries ℚ) = C (1120 : ℚ) := (map_ofNat C 1120).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1220 : derivative ℚ (1220 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1220
@[simp] lemma cc1220 : constantCoeff (1220 : PowerSeries ℚ) = 1220 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1220
lemma cm1220 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1220 : PowerSeries ℚ) * F) = 1220 * coeff m F := by
  have e : (1220 : PowerSeries ℚ) = C (1220 : ℚ) := (map_ofNat C 1220).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1260 : derivative ℚ (1260 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1260
@[simp] lemma cc1260 : constantCoeff (1260 : PowerSeries ℚ) = 1260 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1260
lemma cm1260 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1260 : PowerSeries ℚ) * F) = 1260 * coeff m F := by
  have e : (1260 : PowerSeries ℚ) = C (1260 : ℚ) := (map_ofNat C 1260).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1280 : derivative ℚ (1280 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1280
@[simp] lemma cc1280 : constantCoeff (1280 : PowerSeries ℚ) = 1280 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1280
lemma cm1280 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1280 : PowerSeries ℚ) * F) = 1280 * coeff m F := by
  have e : (1280 : PowerSeries ℚ) = C (1280 : ℚ) := (map_ofNat C 1280).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1344 : derivative ℚ (1344 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1344
@[simp] lemma cc1344 : constantCoeff (1344 : PowerSeries ℚ) = 1344 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1344
lemma cm1344 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1344 : PowerSeries ℚ) * F) = 1344 * coeff m F := by
  have e : (1344 : PowerSeries ℚ) = C (1344 : ℚ) := (map_ofNat C 1344).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1408 : derivative ℚ (1408 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1408
@[simp] lemma cc1408 : constantCoeff (1408 : PowerSeries ℚ) = 1408 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1408
lemma cm1408 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1408 : PowerSeries ℚ) * F) = 1408 * coeff m F := by
  have e : (1408 : PowerSeries ℚ) = C (1408 : ℚ) := (map_ofNat C 1408).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1456 : derivative ℚ (1456 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1456
@[simp] lemma cc1456 : constantCoeff (1456 : PowerSeries ℚ) = 1456 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1456
lemma cm1456 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1456 : PowerSeries ℚ) * F) = 1456 * coeff m F := by
  have e : (1456 : PowerSeries ℚ) = C (1456 : ℚ) := (map_ofNat C 1456).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1470 : derivative ℚ (1470 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1470
@[simp] lemma cc1470 : constantCoeff (1470 : PowerSeries ℚ) = 1470 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1470
lemma cm1470 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1470 : PowerSeries ℚ) * F) = 1470 * coeff m F := by
  have e : (1470 : PowerSeries ℚ) = C (1470 : ℚ) := (map_ofNat C 1470).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1536 : derivative ℚ (1536 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1536
@[simp] lemma cc1536 : constantCoeff (1536 : PowerSeries ℚ) = 1536 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1536
lemma cm1536 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1536 : PowerSeries ℚ) * F) = 1536 * coeff m F := by
  have e : (1536 : PowerSeries ℚ) = C (1536 : ℚ) := (map_ofNat C 1536).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1584 : derivative ℚ (1584 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1584
@[simp] lemma cc1584 : constantCoeff (1584 : PowerSeries ℚ) = 1584 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1584
lemma cm1584 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1584 : PowerSeries ℚ) * F) = 1584 * coeff m F := by
  have e : (1584 : PowerSeries ℚ) = C (1584 : ℚ) := (map_ofNat C 1584).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1596 : derivative ℚ (1596 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1596
@[simp] lemma cc1596 : constantCoeff (1596 : PowerSeries ℚ) = 1596 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1596
lemma cm1596 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1596 : PowerSeries ℚ) * F) = 1596 * coeff m F := by
  have e : (1596 : PowerSeries ℚ) = C (1596 : ℚ) := (map_ofNat C 1596).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1664 : derivative ℚ (1664 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1664
@[simp] lemma cc1664 : constantCoeff (1664 : PowerSeries ℚ) = 1664 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1664
lemma cm1664 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1664 : PowerSeries ℚ) * F) = 1664 * coeff m F := by
  have e : (1664 : PowerSeries ℚ) = C (1664 : ℚ) := (map_ofNat C 1664).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1708 : derivative ℚ (1708 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1708
@[simp] lemma cc1708 : constantCoeff (1708 : PowerSeries ℚ) = 1708 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1708
lemma cm1708 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1708 : PowerSeries ℚ) * F) = 1708 * coeff m F := by
  have e : (1708 : PowerSeries ℚ) = C (1708 : ℚ) := (map_ofNat C 1708).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1792 : derivative ℚ (1792 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1792
@[simp] lemma cc1792 : constantCoeff (1792 : PowerSeries ℚ) = 1792 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1792
lemma cm1792 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1792 : PowerSeries ℚ) * F) = 1792 * coeff m F := by
  have e : (1792 : PowerSeries ℚ) = C (1792 : ℚ) := (map_ofNat C 1792).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1848 : derivative ℚ (1848 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1848
@[simp] lemma cc1848 : constantCoeff (1848 : PowerSeries ℚ) = 1848 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1848
lemma cm1848 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1848 : PowerSeries ℚ) * F) = 1848 * coeff m F := by
  have e : (1848 : PowerSeries ℚ) = C (1848 : ℚ) := (map_ofNat C 1848).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1872 : derivative ℚ (1872 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1872
@[simp] lemma cc1872 : constantCoeff (1872 : PowerSeries ℚ) = 1872 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1872
lemma cm1872 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1872 : PowerSeries ℚ) * F) = 1872 * coeff m F := by
  have e : (1872 : PowerSeries ℚ) = C (1872 : ℚ) := (map_ofNat C 1872).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1920 : derivative ℚ (1920 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1920
@[simp] lemma cc1920 : constantCoeff (1920 : PowerSeries ℚ) = 1920 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1920
lemma cm1920 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1920 : PowerSeries ℚ) * F) = 1920 * coeff m F := by
  have e : (1920 : PowerSeries ℚ) = C (1920 : ℚ) := (map_ofNat C 1920).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1936 : derivative ℚ (1936 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1936
@[simp] lemma cc1936 : constantCoeff (1936 : PowerSeries ℚ) = 1936 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1936
lemma cm1936 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1936 : PowerSeries ℚ) * F) = 1936 * coeff m F := by
  have e : (1936 : PowerSeries ℚ) = C (1936 : ℚ) := (map_ofNat C 1936).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1984 : derivative ℚ (1984 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1984
@[simp] lemma cc1984 : constantCoeff (1984 : PowerSeries ℚ) = 1984 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1984
lemma cm1984 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1984 : PowerSeries ℚ) * F) = 1984 * coeff m F := by
  have e : (1984 : PowerSeries ℚ) = C (1984 : ℚ) := (map_ofNat C 1984).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2048 : derivative ℚ (2048 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2048
@[simp] lemma cc2048 : constantCoeff (2048 : PowerSeries ℚ) = 2048 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2048
lemma cm2048 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2048 : PowerSeries ℚ) * F) = 2048 * coeff m F := by
  have e : (2048 : PowerSeries ℚ) = C (2048 : ℚ) := (map_ofNat C 2048).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2112 : derivative ℚ (2112 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2112
@[simp] lemma cc2112 : constantCoeff (2112 : PowerSeries ℚ) = 2112 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2112
lemma cm2112 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2112 : PowerSeries ℚ) * F) = 2112 * coeff m F := by
  have e : (2112 : PowerSeries ℚ) = C (2112 : ℚ) := (map_ofNat C 2112).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2480 : derivative ℚ (2480 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2480
@[simp] lemma cc2480 : constantCoeff (2480 : PowerSeries ℚ) = 2480 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2480
lemma cm2480 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2480 : PowerSeries ℚ) * F) = 2480 * coeff m F := by
  have e : (2480 : PowerSeries ℚ) = C (2480 : ℚ) := (map_ofNat C 2480).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2496 : derivative ℚ (2496 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2496
@[simp] lemma cc2496 : constantCoeff (2496 : PowerSeries ℚ) = 2496 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2496
lemma cm2496 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2496 : PowerSeries ℚ) * F) = 2496 * coeff m F := by
  have e : (2496 : PowerSeries ℚ) = C (2496 : ℚ) := (map_ofNat C 2496).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2560 : derivative ℚ (2560 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2560
@[simp] lemma cc2560 : constantCoeff (2560 : PowerSeries ℚ) = 2560 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2560
lemma cm2560 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2560 : PowerSeries ℚ) * F) = 2560 * coeff m F := by
  have e : (2560 : PowerSeries ℚ) = C (2560 : ℚ) := (map_ofNat C 2560).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2960 : derivative ℚ (2960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2960
@[simp] lemma cc2960 : constantCoeff (2960 : PowerSeries ℚ) = 2960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2960
lemma cm2960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2960 : PowerSeries ℚ) * F) = 2960 * coeff m F := by
  have e : (2960 : PowerSeries ℚ) = C (2960 : ℚ) := (map_ofNat C 2960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3048 : derivative ℚ (3048 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3048
@[simp] lemma cc3048 : constantCoeff (3048 : PowerSeries ℚ) = 3048 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3048
lemma cm3048 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3048 : PowerSeries ℚ) * F) = 3048 * coeff m F := by
  have e : (3048 : PowerSeries ℚ) = C (3048 : ℚ) := (map_ofNat C 3048).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3072 : derivative ℚ (3072 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3072
@[simp] lemma cc3072 : constantCoeff (3072 : PowerSeries ℚ) = 3072 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3072
lemma cm3072 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3072 : PowerSeries ℚ) * F) = 3072 * coeff m F := by
  have e : (3072 : PowerSeries ℚ) = C (3072 : ℚ) := (map_ofNat C 3072).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3168 : derivative ℚ (3168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3168
@[simp] lemma cc3168 : constantCoeff (3168 : PowerSeries ℚ) = 3168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3168
lemma cm3168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3168 : PowerSeries ℚ) * F) = 3168 * coeff m F := by
  have e : (3168 : PowerSeries ℚ) = C (3168 : ℚ) := (map_ofNat C 3168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3216 : derivative ℚ (3216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3216
@[simp] lemma cc3216 : constantCoeff (3216 : PowerSeries ℚ) = 3216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3216
lemma cm3216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3216 : PowerSeries ℚ) * F) = 3216 * coeff m F := by
  have e : (3216 : PowerSeries ℚ) = C (3216 : ℚ) := (map_ofNat C 3216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3276 : derivative ℚ (3276 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3276
@[simp] lemma cc3276 : constantCoeff (3276 : PowerSeries ℚ) = 3276 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3276
lemma cm3276 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3276 : PowerSeries ℚ) * F) = 3276 * coeff m F := by
  have e : (3276 : PowerSeries ℚ) = C (3276 : ℚ) := (map_ofNat C 3276).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3328 : derivative ℚ (3328 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3328
@[simp] lemma cc3328 : constantCoeff (3328 : PowerSeries ℚ) = 3328 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3328
lemma cm3328 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3328 : PowerSeries ℚ) * F) = 3328 * coeff m F := by
  have e : (3328 : PowerSeries ℚ) = C (3328 : ℚ) := (map_ofNat C 3328).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3584 : derivative ℚ (3584 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3584
@[simp] lemma cc3584 : constantCoeff (3584 : PowerSeries ℚ) = 3584 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3584
lemma cm3584 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3584 : PowerSeries ℚ) * F) = 3584 * coeff m F := by
  have e : (3584 : PowerSeries ℚ) = C (3584 : ℚ) := (map_ofNat C 3584).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3696 : derivative ℚ (3696 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3696
@[simp] lemma cc3696 : constantCoeff (3696 : PowerSeries ℚ) = 3696 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3696
lemma cm3696 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3696 : PowerSeries ℚ) * F) = 3696 * coeff m F := by
  have e : (3696 : PowerSeries ℚ) = C (3696 : ℚ) := (map_ofNat C 3696).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3872 : derivative ℚ (3872 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3872
@[simp] lemma cc3872 : constantCoeff (3872 : PowerSeries ℚ) = 3872 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3872
lemma cm3872 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3872 : PowerSeries ℚ) * F) = 3872 * coeff m F := by
  have e : (3872 : PowerSeries ℚ) = C (3872 : ℚ) := (map_ofNat C 3872).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3920 : derivative ℚ (3920 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3920
@[simp] lemma cc3920 : constantCoeff (3920 : PowerSeries ℚ) = 3920 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3920
lemma cm3920 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3920 : PowerSeries ℚ) * F) = 3920 * coeff m F := by
  have e : (3920 : PowerSeries ℚ) = C (3920 : ℚ) := (map_ofNat C 3920).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4096 : derivative ℚ (4096 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4096
@[simp] lemma cc4096 : constantCoeff (4096 : PowerSeries ℚ) = 4096 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4096
lemma cm4096 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4096 : PowerSeries ℚ) * F) = 4096 * coeff m F := by
  have e : (4096 : PowerSeries ℚ) = C (4096 : ℚ) := (map_ofNat C 4096).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4116 : derivative ℚ (4116 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4116
@[simp] lemma cc4116 : constantCoeff (4116 : PowerSeries ℚ) = 4116 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4116
lemma cm4116 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4116 : PowerSeries ℚ) * F) = 4116 * coeff m F := by
  have e : (4116 : PowerSeries ℚ) = C (4116 : ℚ) := (map_ofNat C 4116).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4224 : derivative ℚ (4224 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4224
@[simp] lemma cc4224 : constantCoeff (4224 : PowerSeries ℚ) = 4224 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4224
lemma cm4224 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4224 : PowerSeries ℚ) * F) = 4224 * coeff m F := by
  have e : (4224 : PowerSeries ℚ) = C (4224 : ℚ) := (map_ofNat C 4224).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4608 : derivative ℚ (4608 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4608
@[simp] lemma cc4608 : constantCoeff (4608 : PowerSeries ℚ) = 4608 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4608
lemma cm4608 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4608 : PowerSeries ℚ) * F) = 4608 * coeff m F := by
  have e : (4608 : PowerSeries ℚ) = C (4608 : ℚ) := (map_ofNat C 4608).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4896 : derivative ℚ (4896 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4896
@[simp] lemma cc4896 : constantCoeff (4896 : PowerSeries ℚ) = 4896 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4896
lemma cm4896 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4896 : PowerSeries ℚ) * F) = 4896 * coeff m F := by
  have e : (4896 : PowerSeries ℚ) = C (4896 : ℚ) := (map_ofNat C 4896).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4992 : derivative ℚ (4992 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4992
@[simp] lemma cc4992 : constantCoeff (4992 : PowerSeries ℚ) = 4992 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4992
lemma cm4992 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4992 : PowerSeries ℚ) * F) = 4992 * coeff m F := by
  have e : (4992 : PowerSeries ℚ) = C (4992 : ℚ) := (map_ofNat C 4992).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5040 : derivative ℚ (5040 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5040
@[simp] lemma cc5040 : constantCoeff (5040 : PowerSeries ℚ) = 5040 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5040
lemma cm5040 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5040 : PowerSeries ℚ) * F) = 5040 * coeff m F := by
  have e : (5040 : PowerSeries ℚ) = C (5040 : ℚ) := (map_ofNat C 5040).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5120 : derivative ℚ (5120 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5120
@[simp] lemma cc5120 : constantCoeff (5120 : PowerSeries ℚ) = 5120 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5120
lemma cm5120 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5120 : PowerSeries ℚ) * F) = 5120 * coeff m F := by
  have e : (5120 : PowerSeries ℚ) = C (5120 : ℚ) := (map_ofNat C 5120).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5124 : derivative ℚ (5124 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5124
@[simp] lemma cc5124 : constantCoeff (5124 : PowerSeries ℚ) = 5124 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5124
lemma cm5124 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5124 : PowerSeries ℚ) * F) = 5124 * coeff m F := by
  have e : (5124 : PowerSeries ℚ) = C (5124 : ℚ) := (map_ofNat C 5124).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5632 : derivative ℚ (5632 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5632
@[simp] lemma cc5632 : constantCoeff (5632 : PowerSeries ℚ) = 5632 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5632
lemma cm5632 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5632 : PowerSeries ℚ) * F) = 5632 * coeff m F := by
  have e : (5632 : PowerSeries ℚ) = C (5632 : ℚ) := (map_ofNat C 5632).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6048 : derivative ℚ (6048 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6048
@[simp] lemma cc6048 : constantCoeff (6048 : PowerSeries ℚ) = 6048 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6048
lemma cm6048 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6048 : PowerSeries ℚ) * F) = 6048 * coeff m F := by
  have e : (6048 : PowerSeries ℚ) = C (6048 : ℚ) := (map_ofNat C 6048).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6096 : derivative ℚ (6096 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6096
@[simp] lemma cc6096 : constantCoeff (6096 : PowerSeries ℚ) = 6096 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6096
lemma cm6096 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6096 : PowerSeries ℚ) * F) = 6096 * coeff m F := by
  have e : (6096 : PowerSeries ℚ) = C (6096 : ℚ) := (map_ofNat C 6096).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6144 : derivative ℚ (6144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6144
@[simp] lemma cc6144 : constantCoeff (6144 : PowerSeries ℚ) = 6144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6144
lemma cm6144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6144 : PowerSeries ℚ) * F) = 6144 * coeff m F := by
  have e : (6144 : PowerSeries ℚ) = C (6144 : ℚ) := (map_ofNat C 6144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6336 : derivative ℚ (6336 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6336
@[simp] lemma cc6336 : constantCoeff (6336 : PowerSeries ℚ) = 6336 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6336
lemma cm6336 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6336 : PowerSeries ℚ) * F) = 6336 * coeff m F := by
  have e : (6336 : PowerSeries ℚ) = C (6336 : ℚ) := (map_ofNat C 6336).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6468 : derivative ℚ (6468 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6468
@[simp] lemma cc6468 : constantCoeff (6468 : PowerSeries ℚ) = 6468 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6468
lemma cm6468 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6468 : PowerSeries ℚ) * F) = 6468 * coeff m F := by
  have e : (6468 : PowerSeries ℚ) = C (6468 : ℚ) := (map_ofNat C 6468).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6720 : derivative ℚ (6720 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6720
@[simp] lemma cc6720 : constantCoeff (6720 : PowerSeries ℚ) = 6720 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6720
lemma cm6720 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6720 : PowerSeries ℚ) * F) = 6720 * coeff m F := by
  have e : (6720 : PowerSeries ℚ) = C (6720 : ℚ) := (map_ofNat C 6720).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn6852 : derivative ℚ (6852 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 6852
@[simp] lemma cc6852 : constantCoeff (6852 : PowerSeries ℚ) = 6852 := by simpa using map_natCast (constantCoeff (R := ℚ)) 6852
lemma cm6852 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((6852 : PowerSeries ℚ) * F) = 6852 * coeff m F := by
  have e : (6852 : PowerSeries ℚ) = C (6852 : ℚ) := (map_ofNat C 6852).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7168 : derivative ℚ (7168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7168
@[simp] lemma cc7168 : constantCoeff (7168 : PowerSeries ℚ) = 7168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7168
lemma cm7168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7168 : PowerSeries ℚ) * F) = 7168 * coeff m F := by
  have e : (7168 : PowerSeries ℚ) = C (7168 : ℚ) := (map_ofNat C 7168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7744 : derivative ℚ (7744 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7744
@[simp] lemma cc7744 : constantCoeff (7744 : PowerSeries ℚ) = 7744 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7744
lemma cm7744 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7744 : PowerSeries ℚ) * F) = 7744 * coeff m F := by
  have e : (7744 : PowerSeries ℚ) = C (7744 : ℚ) := (map_ofNat C 7744).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8192 : derivative ℚ (8192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8192
@[simp] lemma cc8192 : constantCoeff (8192 : PowerSeries ℚ) = 8192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8192
lemma cm8192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8192 : PowerSeries ℚ) * F) = 8192 * coeff m F := by
  have e : (8192 : PowerSeries ℚ) = C (8192 : ℚ) := (map_ofNat C 8192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8568 : derivative ℚ (8568 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8568
@[simp] lemma cc8568 : constantCoeff (8568 : PowerSeries ℚ) = 8568 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8568
lemma cm8568 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8568 : PowerSeries ℚ) * F) = 8568 * coeff m F := by
  have e : (8568 : PowerSeries ℚ) = C (8568 : ℚ) := (map_ofNat C 8568).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8960 : derivative ℚ (8960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8960
@[simp] lemma cc8960 : constantCoeff (8960 : PowerSeries ℚ) = 8960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8960
lemma cm8960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8960 : PowerSeries ℚ) * F) = 8960 * coeff m F := by
  have e : (8960 : PowerSeries ℚ) = C (8960 : ℚ) := (map_ofNat C 8960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9216 : derivative ℚ (9216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9216
@[simp] lemma cc9216 : constantCoeff (9216 : PowerSeries ℚ) = 9216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9216
lemma cm9216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9216 : PowerSeries ℚ) * F) = 9216 * coeff m F := by
  have e : (9216 : PowerSeries ℚ) = C (9216 : ℚ) := (map_ofNat C 9216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10192 : derivative ℚ (10192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10192
@[simp] lemma cc10192 : constantCoeff (10192 : PowerSeries ℚ) = 10192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10192
lemma cm10192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10192 : PowerSeries ℚ) * F) = 10192 * coeff m F := by
  have e : (10192 : PowerSeries ℚ) = C (10192 : ℚ) := (map_ofNat C 10192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10240 : derivative ℚ (10240 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10240
@[simp] lemma cc10240 : constantCoeff (10240 : PowerSeries ℚ) = 10240 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10240
lemma cm10240 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10240 : PowerSeries ℚ) * F) = 10240 * coeff m F := by
  have e : (10240 : PowerSeries ℚ) = C (10240 : ℚ) := (map_ofNat C 10240).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn11136 : derivative ℚ (11136 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 11136
@[simp] lemma cc11136 : constantCoeff (11136 : PowerSeries ℚ) = 11136 := by simpa using map_natCast (constantCoeff (R := ℚ)) 11136
lemma cm11136 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((11136 : PowerSeries ℚ) * F) = 11136 * coeff m F := by
  have e : (11136 : PowerSeries ℚ) = C (11136 : ℚ) := (map_ofNat C 11136).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn12288 : derivative ℚ (12288 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 12288
@[simp] lemma cc12288 : constantCoeff (12288 : PowerSeries ℚ) = 12288 := by simpa using map_natCast (constantCoeff (R := ℚ)) 12288
lemma cm12288 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((12288 : PowerSeries ℚ) * F) = 12288 * coeff m F := by
  have e : (12288 : PowerSeries ℚ) = C (12288 : ℚ) := (map_ofNat C 12288).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14336 : derivative ℚ (14336 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14336
@[simp] lemma cc14336 : constantCoeff (14336 : PowerSeries ℚ) = 14336 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14336
lemma cm14336 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14336 : PowerSeries ℚ) * F) = 14336 * coeff m F := by
  have e : (14336 : PowerSeries ℚ) = C (14336 : ℚ) := (map_ofNat C 14336).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn15488 : derivative ℚ (15488 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 15488
@[simp] lemma cc15488 : constantCoeff (15488 : PowerSeries ℚ) = 15488 := by simpa using map_natCast (constantCoeff (R := ℚ)) 15488
lemma cm15488 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((15488 : PowerSeries ℚ) * F) = 15488 * coeff m F := by
  have e : (15488 : PowerSeries ℚ) = C (15488 : ℚ) := (map_ofNat C 15488).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16224 : derivative ℚ (16224 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16224
@[simp] lemma cc16224 : constantCoeff (16224 : PowerSeries ℚ) = 16224 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16224
lemma cm16224 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16224 : PowerSeries ℚ) * F) = 16224 * coeff m F := by
  have e : (16224 : PowerSeries ℚ) = C (16224 : ℚ) := (map_ofNat C 16224).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16384 : derivative ℚ (16384 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16384
@[simp] lemma cc16384 : constantCoeff (16384 : PowerSeries ℚ) = 16384 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16384
lemma cm16384 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16384 : PowerSeries ℚ) * F) = 16384 * coeff m F := by
  have e : (16384 : PowerSeries ℚ) = C (16384 : ℚ) := (map_ofNat C 16384).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17640 : derivative ℚ (17640 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17640
@[simp] lemma cc17640 : constantCoeff (17640 : PowerSeries ℚ) = 17640 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17640
lemma cm17640 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17640 : PowerSeries ℚ) * F) = 17640 * coeff m F := by
  have e : (17640 : PowerSeries ℚ) = C (17640 : ℚ) := (map_ofNat C 17640).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn17920 : derivative ℚ (17920 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 17920
@[simp] lemma cc17920 : constantCoeff (17920 : PowerSeries ℚ) = 17920 := by simpa using map_natCast (constantCoeff (R := ℚ)) 17920
lemma cm17920 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((17920 : PowerSeries ℚ) * F) = 17920 * coeff m F := by
  have e : (17920 : PowerSeries ℚ) = C (17920 : ℚ) := (map_ofNat C 17920).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn18560 : derivative ℚ (18560 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 18560
@[simp] lemma cc18560 : constantCoeff (18560 : PowerSeries ℚ) = 18560 := by simpa using map_natCast (constantCoeff (R := ℚ)) 18560
lemma cm18560 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((18560 : PowerSeries ℚ) * F) = 18560 * coeff m F := by
  have e : (18560 : PowerSeries ℚ) = C (18560 : ℚ) := (map_ofNat C 18560).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19456 : derivative ℚ (19456 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19456
@[simp] lemma cc19456 : constantCoeff (19456 : PowerSeries ℚ) = 19456 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19456
lemma cm19456 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19456 : PowerSeries ℚ) * F) = 19456 * coeff m F := by
  have e : (19456 : PowerSeries ℚ) = C (19456 : ℚ) := (map_ofNat C 19456).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19968 : derivative ℚ (19968 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19968
@[simp] lemma cc19968 : constantCoeff (19968 : PowerSeries ℚ) = 19968 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19968
lemma cm19968 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19968 : PowerSeries ℚ) * F) = 19968 * coeff m F := by
  have e : (19968 : PowerSeries ℚ) = C (19968 : ℚ) := (map_ofNat C 19968).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22528 : derivative ℚ (22528 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22528
@[simp] lemma cc22528 : constantCoeff (22528 : PowerSeries ℚ) = 22528 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22528
lemma cm22528 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22528 : PowerSeries ℚ) * F) = 22528 * coeff m F := by
  have e : (22528 : PowerSeries ℚ) = C (22528 : ℚ) := (map_ofNat C 22528).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22680 : derivative ℚ (22680 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22680
@[simp] lemma cc22680 : constantCoeff (22680 : PowerSeries ℚ) = 22680 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22680
lemma cm22680 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22680 : PowerSeries ℚ) * F) = 22680 * coeff m F := by
  have e : (22680 : PowerSeries ℚ) = C (22680 : ℚ) := (map_ofNat C 22680).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn23100 : derivative ℚ (23100 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 23100
@[simp] lemma cc23100 : constantCoeff (23100 : PowerSeries ℚ) = 23100 := by simpa using map_natCast (constantCoeff (R := ℚ)) 23100
lemma cm23100 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((23100 : PowerSeries ℚ) * F) = 23100 * coeff m F := by
  have e : (23100 : PowerSeries ℚ) = C (23100 : ℚ) := (map_ofNat C 23100).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn23248 : derivative ℚ (23248 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 23248
@[simp] lemma cc23248 : constantCoeff (23248 : PowerSeries ℚ) = 23248 := by simpa using map_natCast (constantCoeff (R := ℚ)) 23248
lemma cm23248 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((23248 : PowerSeries ℚ) * F) = 23248 * coeff m F := by
  have e : (23248 : PowerSeries ℚ) = C (23248 : ℚ) := (map_ofNat C 23248).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn24576 : derivative ℚ (24576 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 24576
@[simp] lemma cc24576 : constantCoeff (24576 : PowerSeries ℚ) = 24576 := by simpa using map_natCast (constantCoeff (R := ℚ)) 24576
lemma cm24576 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((24576 : PowerSeries ℚ) * F) = 24576 * coeff m F := by
  have e : (24576 : PowerSeries ℚ) = C (24576 : ℚ) := (map_ofNat C 24576).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25600 : derivative ℚ (25600 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25600
@[simp] lemma cc25600 : constantCoeff (25600 : PowerSeries ℚ) = 25600 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25600
lemma cm25600 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25600 : PowerSeries ℚ) * F) = 25600 * coeff m F := by
  have e : (25600 : PowerSeries ℚ) = C (25600 : ℚ) := (map_ofNat C 25600).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn28672 : derivative ℚ (28672 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 28672
@[simp] lemma cc28672 : constantCoeff (28672 : PowerSeries ℚ) = 28672 := by simpa using map_natCast (constantCoeff (R := ℚ)) 28672
lemma cm28672 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((28672 : PowerSeries ℚ) * F) = 28672 * coeff m F := by
  have e : (28672 : PowerSeries ℚ) = C (28672 : ℚ) := (map_ofNat C 28672).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn32768 : derivative ℚ (32768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 32768
@[simp] lemma cc32768 : constantCoeff (32768 : PowerSeries ℚ) = 32768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 32768
lemma cm32768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((32768 : PowerSeries ℚ) * F) = 32768 * coeff m F := by
  have e : (32768 : PowerSeries ℚ) = C (32768 : ℚ) := (map_ofNat C 32768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn36096 : derivative ℚ (36096 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36096
@[simp] lemma cc36096 : constantCoeff (36096 : PowerSeries ℚ) = 36096 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36096
lemma cm36096 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36096 : PowerSeries ℚ) * F) = 36096 * coeff m F := by
  have e : (36096 : PowerSeries ℚ) = C (36096 : ℚ) := (map_ofNat C 36096).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40656 : derivative ℚ (40656 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40656
@[simp] lemma cc40656 : constantCoeff (40656 : PowerSeries ℚ) = 40656 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40656
lemma cm40656 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40656 : PowerSeries ℚ) * F) = 40656 * coeff m F := by
  have e : (40656 : PowerSeries ℚ) = C (40656 : ℚ) := (map_ofNat C 40656).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn40960 : derivative ℚ (40960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 40960
@[simp] lemma cc40960 : constantCoeff (40960 : PowerSeries ℚ) = 40960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 40960
lemma cm40960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((40960 : PowerSeries ℚ) * F) = 40960 * coeff m F := by
  have e : (40960 : PowerSeries ℚ) = C (40960 : ℚ) := (map_ofNat C 40960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn41860 : derivative ℚ (41860 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 41860
@[simp] lemma cc41860 : constantCoeff (41860 : PowerSeries ℚ) = 41860 := by simpa using map_natCast (constantCoeff (R := ℚ)) 41860
lemma cm41860 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((41860 : PowerSeries ℚ) * F) = 41860 * coeff m F := by
  have e : (41860 : PowerSeries ℚ) = C (41860 : ℚ) := (map_ofNat C 41860).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn46080 : derivative ℚ (46080 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 46080
@[simp] lemma cc46080 : constantCoeff (46080 : PowerSeries ℚ) = 46080 := by simpa using map_natCast (constantCoeff (R := ℚ)) 46080
lemma cm46080 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((46080 : PowerSeries ℚ) * F) = 46080 * coeff m F := by
  have e : (46080 : PowerSeries ℚ) = C (46080 : ℚ) := (map_ofNat C 46080).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn47552 : derivative ℚ (47552 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 47552
@[simp] lemma cc47552 : constantCoeff (47552 : PowerSeries ℚ) = 47552 := by simpa using map_natCast (constantCoeff (R := ℚ)) 47552
lemma cm47552 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((47552 : PowerSeries ℚ) * F) = 47552 * coeff m F := by
  have e : (47552 : PowerSeries ℚ) = C (47552 : ℚ) := (map_ofNat C 47552).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn49152 : derivative ℚ (49152 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 49152
@[simp] lemma cc49152 : constantCoeff (49152 : PowerSeries ℚ) = 49152 := by simpa using map_natCast (constantCoeff (R := ℚ)) 49152
lemma cm49152 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((49152 : PowerSeries ℚ) * F) = 49152 * coeff m F := by
  have e : (49152 : PowerSeries ℚ) = C (49152 : ℚ) := (map_ofNat C 49152).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn53376 : derivative ℚ (53376 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 53376
@[simp] lemma cc53376 : constantCoeff (53376 : PowerSeries ℚ) = 53376 := by simpa using map_natCast (constantCoeff (R := ℚ)) 53376
lemma cm53376 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((53376 : PowerSeries ℚ) * F) = 53376 * coeff m F := by
  have e : (53376 : PowerSeries ℚ) = C (53376 : ℚ) := (map_ofNat C 53376).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn53888 : derivative ℚ (53888 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 53888
@[simp] lemma cc53888 : constantCoeff (53888 : PowerSeries ℚ) = 53888 := by simpa using map_natCast (constantCoeff (R := ℚ)) 53888
lemma cm53888 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((53888 : PowerSeries ℚ) * F) = 53888 * coeff m F := by
  have e : (53888 : PowerSeries ℚ) = C (53888 : ℚ) := (map_ofNat C 53888).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn56064 : derivative ℚ (56064 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 56064
@[simp] lemma cc56064 : constantCoeff (56064 : PowerSeries ℚ) = 56064 := by simpa using map_natCast (constantCoeff (R := ℚ)) 56064
lemma cm56064 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((56064 : PowerSeries ℚ) * F) = 56064 * coeff m F := by
  have e : (56064 : PowerSeries ℚ) = C (56064 : ℚ) := (map_ofNat C 56064).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn56320 : derivative ℚ (56320 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 56320
@[simp] lemma cc56320 : constantCoeff (56320 : PowerSeries ℚ) = 56320 := by simpa using map_natCast (constantCoeff (R := ℚ)) 56320
lemma cm56320 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((56320 : PowerSeries ℚ) * F) = 56320 * coeff m F := by
  have e : (56320 : PowerSeries ℚ) = C (56320 : ℚ) := (map_ofNat C 56320).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn61440 : derivative ℚ (61440 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 61440
@[simp] lemma cc61440 : constantCoeff (61440 : PowerSeries ℚ) = 61440 := by simpa using map_natCast (constantCoeff (R := ℚ)) 61440
lemma cm61440 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((61440 : PowerSeries ℚ) * F) = 61440 * coeff m F := by
  have e : (61440 : PowerSeries ℚ) = C (61440 : ℚ) := (map_ofNat C 61440).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn64512 : derivative ℚ (64512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 64512
@[simp] lemma cc64512 : constantCoeff (64512 : PowerSeries ℚ) = 64512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 64512
lemma cm64512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((64512 : PowerSeries ℚ) * F) = 64512 * coeff m F := by
  have e : (64512 : PowerSeries ℚ) = C (64512 : ℚ) := (map_ofNat C 64512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn64896 : derivative ℚ (64896 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 64896
@[simp] lemma cc64896 : constantCoeff (64896 : PowerSeries ℚ) = 64896 := by simpa using map_natCast (constantCoeff (R := ℚ)) 64896
lemma cm64896 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((64896 : PowerSeries ℚ) * F) = 64896 * coeff m F := by
  have e : (64896 : PowerSeries ℚ) = C (64896 : ℚ) := (map_ofNat C 64896).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn65536 : derivative ℚ (65536 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 65536
@[simp] lemma cc65536 : constantCoeff (65536 : PowerSeries ℚ) = 65536 := by simpa using map_natCast (constantCoeff (R := ℚ)) 65536
lemma cm65536 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((65536 : PowerSeries ℚ) * F) = 65536 * coeff m F := by
  have e : (65536 : PowerSeries ℚ) = C (65536 : ℚ) := (map_ofNat C 65536).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn66816 : derivative ℚ (66816 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 66816
@[simp] lemma cc66816 : constantCoeff (66816 : PowerSeries ℚ) = 66816 := by simpa using map_natCast (constantCoeff (R := ℚ)) 66816
lemma cm66816 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((66816 : PowerSeries ℚ) * F) = 66816 * coeff m F := by
  have e : (66816 : PowerSeries ℚ) = C (66816 : ℚ) := (map_ofNat C 66816).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn72192 : derivative ℚ (72192 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 72192
@[simp] lemma cc72192 : constantCoeff (72192 : PowerSeries ℚ) = 72192 := by simpa using map_natCast (constantCoeff (R := ℚ)) 72192
lemma cm72192 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((72192 : PowerSeries ℚ) * F) = 72192 * coeff m F := by
  have e : (72192 : PowerSeries ℚ) = C (72192 : ℚ) := (map_ofNat C 72192).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn73728 : derivative ℚ (73728 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 73728
@[simp] lemma cc73728 : constantCoeff (73728 : PowerSeries ℚ) = 73728 := by simpa using map_natCast (constantCoeff (R := ℚ)) 73728
lemma cm73728 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((73728 : PowerSeries ℚ) * F) = 73728 * coeff m F := by
  have e : (73728 : PowerSeries ℚ) = C (73728 : ℚ) := (map_ofNat C 73728).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn75648 : derivative ℚ (75648 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 75648
@[simp] lemma cc75648 : constantCoeff (75648 : PowerSeries ℚ) = 75648 := by simpa using map_natCast (constantCoeff (R := ℚ)) 75648
lemma cm75648 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((75648 : PowerSeries ℚ) * F) = 75648 * coeff m F := by
  have e : (75648 : PowerSeries ℚ) = C (75648 : ℚ) := (map_ofNat C 75648).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn83392 : derivative ℚ (83392 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 83392
@[simp] lemma cc83392 : constantCoeff (83392 : PowerSeries ℚ) = 83392 := by simpa using map_natCast (constantCoeff (R := ℚ)) 83392
lemma cm83392 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((83392 : PowerSeries ℚ) * F) = 83392 * coeff m F := by
  have e : (83392 : PowerSeries ℚ) = C (83392 : ℚ) := (map_ofNat C 83392).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn95232 : derivative ℚ (95232 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 95232
@[simp] lemma cc95232 : constantCoeff (95232 : PowerSeries ℚ) = 95232 := by simpa using map_natCast (constantCoeff (R := ℚ)) 95232
lemma cm95232 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((95232 : PowerSeries ℚ) * F) = 95232 * coeff m F := by
  have e : (95232 : PowerSeries ℚ) = C (95232 : ℚ) := (map_ofNat C 95232).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn98304 : derivative ℚ (98304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 98304
@[simp] lemma cc98304 : constantCoeff (98304 : PowerSeries ℚ) = 98304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 98304
lemma cm98304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((98304 : PowerSeries ℚ) * F) = 98304 * coeff m F := by
  have e : (98304 : PowerSeries ℚ) = C (98304 : ℚ) := (map_ofNat C 98304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn121344 : derivative ℚ (121344 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 121344
@[simp] lemma cc121344 : constantCoeff (121344 : PowerSeries ℚ) = 121344 := by simpa using map_natCast (constantCoeff (R := ℚ)) 121344
lemma cm121344 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((121344 : PowerSeries ℚ) * F) = 121344 * coeff m F := by
  have e : (121344 : PowerSeries ℚ) = C (121344 : ℚ) := (map_ofNat C 121344).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn131072 : derivative ℚ (131072 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 131072
@[simp] lemma cc131072 : constantCoeff (131072 : PowerSeries ℚ) = 131072 := by simpa using map_natCast (constantCoeff (R := ℚ)) 131072
lemma cm131072 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((131072 : PowerSeries ℚ) * F) = 131072 * coeff m F := by
  have e : (131072 : PowerSeries ℚ) = C (131072 : ℚ) := (map_ofNat C 131072).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn132768 : derivative ℚ (132768 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 132768
@[simp] lemma cc132768 : constantCoeff (132768 : PowerSeries ℚ) = 132768 := by simpa using map_natCast (constantCoeff (R := ℚ)) 132768
lemma cm132768 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((132768 : PowerSeries ℚ) * F) = 132768 * coeff m F := by
  have e : (132768 : PowerSeries ℚ) = C (132768 : ℚ) := (map_ofNat C 132768).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn135168 : derivative ℚ (135168 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 135168
@[simp] lemma cc135168 : constantCoeff (135168 : PowerSeries ℚ) = 135168 := by simpa using map_natCast (constantCoeff (R := ℚ)) 135168
lemma cm135168 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((135168 : PowerSeries ℚ) * F) = 135168 * coeff m F := by
  have e : (135168 : PowerSeries ℚ) = C (135168 : ℚ) := (map_ofNat C 135168).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn137664 : derivative ℚ (137664 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 137664
@[simp] lemma cc137664 : constantCoeff (137664 : PowerSeries ℚ) = 137664 := by simpa using map_natCast (constantCoeff (R := ℚ)) 137664
lemma cm137664 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((137664 : PowerSeries ℚ) * F) = 137664 * coeff m F := by
  have e : (137664 : PowerSeries ℚ) = C (137664 : ℚ) := (map_ofNat C 137664).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn165888 : derivative ℚ (165888 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 165888
@[simp] lemma cc165888 : constantCoeff (165888 : PowerSeries ℚ) = 165888 := by simpa using map_natCast (constantCoeff (R := ℚ)) 165888
lemma cm165888 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((165888 : PowerSeries ℚ) * F) = 165888 * coeff m F := by
  have e : (165888 : PowerSeries ℚ) = C (165888 : ℚ) := (map_ofNat C 165888).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn190464 : derivative ℚ (190464 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 190464
@[simp] lemma cc190464 : constantCoeff (190464 : PowerSeries ℚ) = 190464 := by simpa using map_natCast (constantCoeff (R := ℚ)) 190464
lemma cm190464 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((190464 : PowerSeries ℚ) * F) = 190464 * coeff m F := by
  have e : (190464 : PowerSeries ℚ) = C (190464 : ℚ) := (map_ofNat C 190464).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn196608 : derivative ℚ (196608 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 196608
@[simp] lemma cc196608 : constantCoeff (196608 : PowerSeries ℚ) = 196608 := by simpa using map_natCast (constantCoeff (R := ℚ)) 196608
lemma cm196608 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((196608 : PowerSeries ℚ) * F) = 196608 * coeff m F := by
  have e : (196608 : PowerSeries ℚ) = C (196608 : ℚ) := (map_ofNat C 196608).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn212448 : derivative ℚ (212448 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 212448
@[simp] lemma cc212448 : constantCoeff (212448 : PowerSeries ℚ) = 212448 := by simpa using map_natCast (constantCoeff (R := ℚ)) 212448
lemma cm212448 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((212448 : PowerSeries ℚ) * F) = 212448 * coeff m F := by
  have e : (212448 : PowerSeries ℚ) = C (212448 : ℚ) := (map_ofNat C 212448).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn229376 : derivative ℚ (229376 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 229376
@[simp] lemma cc229376 : constantCoeff (229376 : PowerSeries ℚ) = 229376 := by simpa using map_natCast (constantCoeff (R := ℚ)) 229376
lemma cm229376 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((229376 : PowerSeries ℚ) * F) = 229376 * coeff m F := by
  have e : (229376 : PowerSeries ℚ) = C (229376 : ℚ) := (map_ofNat C 229376).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn244608 : derivative ℚ (244608 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 244608
@[simp] lemma cc244608 : constantCoeff (244608 : PowerSeries ℚ) = 244608 := by simpa using map_natCast (constantCoeff (R := ℚ)) 244608
lemma cm244608 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((244608 : PowerSeries ℚ) * F) = 244608 * coeff m F := by
  have e : (244608 : PowerSeries ℚ) = C (244608 : ℚ) := (map_ofNat C 244608).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn246960 : derivative ℚ (246960 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 246960
@[simp] lemma cc246960 : constantCoeff (246960 : PowerSeries ℚ) = 246960 := by simpa using map_natCast (constantCoeff (R := ℚ)) 246960
lemma cm246960 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((246960 : PowerSeries ℚ) * F) = 246960 * coeff m F := by
  have e : (246960 : PowerSeries ℚ) = C (246960 : ℚ) := (map_ofNat C 246960).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn253952 : derivative ℚ (253952 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 253952
@[simp] lemma cc253952 : constantCoeff (253952 : PowerSeries ℚ) = 253952 := by simpa using map_natCast (constantCoeff (R := ℚ)) 253952
lemma cm253952 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((253952 : PowerSeries ℚ) * F) = 253952 * coeff m F := by
  have e : (253952 : PowerSeries ℚ) = C (253952 : ℚ) := (map_ofNat C 253952).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn295296 : derivative ℚ (295296 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 295296
@[simp] lemma cc295296 : constantCoeff (295296 : PowerSeries ℚ) = 295296 := by simpa using map_natCast (constantCoeff (R := ℚ)) 295296
lemma cm295296 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((295296 : PowerSeries ℚ) * F) = 295296 * coeff m F := by
  have e : (295296 : PowerSeries ℚ) = C (295296 : ℚ) := (map_ofNat C 295296).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn303104 : derivative ℚ (303104 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 303104
@[simp] lemma cc303104 : constantCoeff (303104 : PowerSeries ℚ) = 303104 := by simpa using map_natCast (constantCoeff (R := ℚ)) 303104
lemma cm303104 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((303104 : PowerSeries ℚ) * F) = 303104 * coeff m F := by
  have e : (303104 : PowerSeries ℚ) = C (303104 : ℚ) := (map_ofNat C 303104).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn327680 : derivative ℚ (327680 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 327680
@[simp] lemma cc327680 : constantCoeff (327680 : PowerSeries ℚ) = 327680 := by simpa using map_natCast (constantCoeff (R := ℚ)) 327680
lemma cm327680 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((327680 : PowerSeries ℚ) * F) = 327680 * coeff m F := by
  have e : (327680 : PowerSeries ℚ) = C (327680 : ℚ) := (map_ofNat C 327680).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn390144 : derivative ℚ (390144 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 390144
@[simp] lemma cc390144 : constantCoeff (390144 : PowerSeries ℚ) = 390144 := by simpa using map_natCast (constantCoeff (R := ℚ)) 390144
lemma cm390144 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((390144 : PowerSeries ℚ) * F) = 390144 * coeff m F := by
  have e : (390144 : PowerSeries ℚ) = C (390144 : ℚ) := (map_ofNat C 390144).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn393216 : derivative ℚ (393216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 393216
@[simp] lemma cc393216 : constantCoeff (393216 : PowerSeries ℚ) = 393216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 393216
lemma cm393216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((393216 : PowerSeries ℚ) * F) = 393216 * coeff m F := by
  have e : (393216 : PowerSeries ℚ) = C (393216 : ℚ) := (map_ofNat C 393216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn407040 : derivative ℚ (407040 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 407040
@[simp] lemma cc407040 : constantCoeff (407040 : PowerSeries ℚ) = 407040 := by simpa using map_natCast (constantCoeff (R := ℚ)) 407040
lemma cm407040 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((407040 : PowerSeries ℚ) * F) = 407040 * coeff m F := by
  have e : (407040 : PowerSeries ℚ) = C (407040 : ℚ) := (map_ofNat C 407040).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn473088 : derivative ℚ (473088 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 473088
@[simp] lemma cc473088 : constantCoeff (473088 : PowerSeries ℚ) = 473088 := by simpa using map_natCast (constantCoeff (R := ℚ)) 473088
lemma cm473088 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((473088 : PowerSeries ℚ) * F) = 473088 * coeff m F := by
  have e : (473088 : PowerSeries ℚ) = C (473088 : ℚ) := (map_ofNat C 473088).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn524288 : derivative ℚ (524288 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 524288
@[simp] lemma cc524288 : constantCoeff (524288 : PowerSeries ℚ) = 524288 := by simpa using map_natCast (constantCoeff (R := ℚ)) 524288
lemma cm524288 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((524288 : PowerSeries ℚ) * F) = 524288 * coeff m F := by
  have e : (524288 : PowerSeries ℚ) = C (524288 : ℚ) := (map_ofNat C 524288).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn546816 : derivative ℚ (546816 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 546816
@[simp] lemma cc546816 : constantCoeff (546816 : PowerSeries ℚ) = 546816 := by simpa using map_natCast (constantCoeff (R := ℚ)) 546816
lemma cm546816 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((546816 : PowerSeries ℚ) * F) = 546816 * coeff m F := by
  have e : (546816 : PowerSeries ℚ) = C (546816 : ℚ) := (map_ofNat C 546816).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn562176 : derivative ℚ (562176 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 562176
@[simp] lemma cc562176 : constantCoeff (562176 : PowerSeries ℚ) = 562176 := by simpa using map_natCast (constantCoeff (R := ℚ)) 562176
lemma cm562176 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((562176 : PowerSeries ℚ) * F) = 562176 * coeff m F := by
  have e : (562176 : PowerSeries ℚ) = C (562176 : ℚ) := (map_ofNat C 562176).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn570624 : derivative ℚ (570624 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 570624
@[simp] lemma cc570624 : constantCoeff (570624 : PowerSeries ℚ) = 570624 := by simpa using map_natCast (constantCoeff (R := ℚ)) 570624
lemma cm570624 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((570624 : PowerSeries ℚ) * F) = 570624 * coeff m F := by
  have e : (570624 : PowerSeries ℚ) = C (570624 : ℚ) := (map_ofNat C 570624).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn578088 : derivative ℚ (578088 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 578088
@[simp] lemma cc578088 : constantCoeff (578088 : PowerSeries ℚ) = 578088 := by simpa using map_natCast (constantCoeff (R := ℚ)) 578088
lemma cm578088 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((578088 : PowerSeries ℚ) * F) = 578088 * coeff m F := by
  have e : (578088 : PowerSeries ℚ) = C (578088 : ℚ) := (map_ofNat C 578088).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn620948 : derivative ℚ (620948 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 620948
@[simp] lemma cc620948 : constantCoeff (620948 : PowerSeries ℚ) = 620948 := by simpa using map_natCast (constantCoeff (R := ℚ)) 620948
lemma cm620948 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((620948 : PowerSeries ℚ) * F) = 620948 * coeff m F := by
  have e : (620948 : PowerSeries ℚ) = C (620948 : ℚ) := (map_ofNat C 620948).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn632832 : derivative ℚ (632832 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 632832
@[simp] lemma cc632832 : constantCoeff (632832 : PowerSeries ℚ) = 632832 := by simpa using map_natCast (constantCoeff (R := ℚ)) 632832
lemma cm632832 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((632832 : PowerSeries ℚ) * F) = 632832 * coeff m F := by
  have e : (632832 : PowerSeries ℚ) = C (632832 : ℚ) := (map_ofNat C 632832).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn722304 : derivative ℚ (722304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 722304
@[simp] lemma cc722304 : constantCoeff (722304 : PowerSeries ℚ) = 722304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 722304
lemma cm722304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((722304 : PowerSeries ℚ) * F) = 722304 * coeff m F := by
  have e : (722304 : PowerSeries ℚ) = C (722304 : ℚ) := (map_ofNat C 722304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn786432 : derivative ℚ (786432 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 786432
@[simp] lemma cc786432 : constantCoeff (786432 : PowerSeries ℚ) = 786432 := by simpa using map_natCast (constantCoeff (R := ℚ)) 786432
lemma cm786432 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((786432 : PowerSeries ℚ) * F) = 786432 * coeff m F := by
  have e : (786432 : PowerSeries ℚ) = C (786432 : ℚ) := (map_ofNat C 786432).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn860160 : derivative ℚ (860160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 860160
@[simp] lemma cc860160 : constantCoeff (860160 : PowerSeries ℚ) = 860160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 860160
lemma cm860160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((860160 : PowerSeries ℚ) * F) = 860160 * coeff m F := by
  have e : (860160 : PowerSeries ℚ) = C (860160 : ℚ) := (map_ofNat C 860160).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1021440 : derivative ℚ (1021440 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1021440
@[simp] lemma cc1021440 : constantCoeff (1021440 : PowerSeries ℚ) = 1021440 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1021440
lemma cm1021440 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1021440 : PowerSeries ℚ) * F) = 1021440 * coeff m F := by
  have e : (1021440 : PowerSeries ℚ) = C (1021440 : ℚ) := (map_ofNat C 1021440).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1179648 : derivative ℚ (1179648 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1179648
@[simp] lemma cc1179648 : constantCoeff (1179648 : PowerSeries ℚ) = 1179648 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1179648
lemma cm1179648 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1179648 : PowerSeries ℚ) * F) = 1179648 * coeff m F := by
  have e : (1179648 : PowerSeries ℚ) = C (1179648 : ℚ) := (map_ofNat C 1179648).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1257216 : derivative ℚ (1257216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1257216
@[simp] lemma cc1257216 : constantCoeff (1257216 : PowerSeries ℚ) = 1257216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1257216
lemma cm1257216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1257216 : PowerSeries ℚ) * F) = 1257216 * coeff m F := by
  have e : (1257216 : PowerSeries ℚ) = C (1257216 : ℚ) := (map_ofNat C 1257216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1277952 : derivative ℚ (1277952 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1277952
@[simp] lemma cc1277952 : constantCoeff (1277952 : PowerSeries ℚ) = 1277952 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1277952
lemma cm1277952 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1277952 : PowerSeries ℚ) * F) = 1277952 * coeff m F := by
  have e : (1277952 : PowerSeries ℚ) = C (1277952 : ℚ) := (map_ofNat C 1277952).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1302528 : derivative ℚ (1302528 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1302528
@[simp] lemma cc1302528 : constantCoeff (1302528 : PowerSeries ℚ) = 1302528 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1302528
lemma cm1302528 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1302528 : PowerSeries ℚ) * F) = 1302528 * coeff m F := by
  have e : (1302528 : PowerSeries ℚ) = C (1302528 : ℚ) := (map_ofNat C 1302528).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1376256 : derivative ℚ (1376256 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1376256
@[simp] lemma cc1376256 : constantCoeff (1376256 : PowerSeries ℚ) = 1376256 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1376256
lemma cm1376256 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1376256 : PowerSeries ℚ) * F) = 1376256 * coeff m F := by
  have e : (1376256 : PowerSeries ℚ) = C (1376256 : ℚ) := (map_ofNat C 1376256).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1441792 : derivative ℚ (1441792 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1441792
@[simp] lemma cc1441792 : constantCoeff (1441792 : PowerSeries ℚ) = 1441792 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1441792
lemma cm1441792 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1441792 : PowerSeries ℚ) * F) = 1441792 * coeff m F := by
  have e : (1441792 : PowerSeries ℚ) = C (1441792 : ℚ) := (map_ofNat C 1441792).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1486848 : derivative ℚ (1486848 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1486848
@[simp] lemma cc1486848 : constantCoeff (1486848 : PowerSeries ℚ) = 1486848 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1486848
lemma cm1486848 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1486848 : PowerSeries ℚ) * F) = 1486848 * coeff m F := by
  have e : (1486848 : PowerSeries ℚ) = C (1486848 : ℚ) := (map_ofNat C 1486848).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1572864 : derivative ℚ (1572864 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1572864
@[simp] lemma cc1572864 : constantCoeff (1572864 : PowerSeries ℚ) = 1572864 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1572864
lemma cm1572864 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1572864 : PowerSeries ℚ) * F) = 1572864 * coeff m F := by
  have e : (1572864 : PowerSeries ℚ) = C (1572864 : ℚ) := (map_ofNat C 1572864).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1709568 : derivative ℚ (1709568 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1709568
@[simp] lemma cc1709568 : constantCoeff (1709568 : PowerSeries ℚ) = 1709568 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1709568
lemma cm1709568 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1709568 : PowerSeries ℚ) * F) = 1709568 * coeff m F := by
  have e : (1709568 : PowerSeries ℚ) = C (1709568 : ℚ) := (map_ofNat C 1709568).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2143744 : derivative ℚ (2143744 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2143744
@[simp] lemma cc2143744 : constantCoeff (2143744 : PowerSeries ℚ) = 2143744 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2143744
lemma cm2143744 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2143744 : PowerSeries ℚ) * F) = 2143744 * coeff m F := by
  have e : (2143744 : PowerSeries ℚ) = C (2143744 : ℚ) := (map_ofNat C 2143744).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2242560 : derivative ℚ (2242560 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2242560
@[simp] lemma cc2242560 : constantCoeff (2242560 : PowerSeries ℚ) = 2242560 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2242560
lemma cm2242560 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2242560 : PowerSeries ℚ) * F) = 2242560 * coeff m F := by
  have e : (2242560 : PowerSeries ℚ) = C (2242560 : ℚ) := (map_ofNat C 2242560).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2273280 : derivative ℚ (2273280 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2273280
@[simp] lemma cc2273280 : constantCoeff (2273280 : PowerSeries ℚ) = 2273280 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2273280
lemma cm2273280 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2273280 : PowerSeries ℚ) * F) = 2273280 * coeff m F := by
  have e : (2273280 : PowerSeries ℚ) = C (2273280 : ℚ) := (map_ofNat C 2273280).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2752512 : derivative ℚ (2752512 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2752512
@[simp] lemma cc2752512 : constantCoeff (2752512 : PowerSeries ℚ) = 2752512 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2752512
lemma cm2752512 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2752512 : PowerSeries ℚ) * F) = 2752512 * coeff m F := by
  have e : (2752512 : PowerSeries ℚ) = C (2752512 : ℚ) := (map_ofNat C 2752512).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2883584 : derivative ℚ (2883584 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2883584
@[simp] lemma cc2883584 : constantCoeff (2883584 : PowerSeries ℚ) = 2883584 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2883584
lemma cm2883584 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2883584 : PowerSeries ℚ) * F) = 2883584 * coeff m F := by
  have e : (2883584 : PowerSeries ℚ) = C (2883584 : ℚ) := (map_ofNat C 2883584).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3071488 : derivative ℚ (3071488 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3071488
@[simp] lemma cc3071488 : constantCoeff (3071488 : PowerSeries ℚ) = 3071488 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3071488
lemma cm3071488 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3071488 : PowerSeries ℚ) * F) = 3071488 * coeff m F := by
  have e : (3071488 : PowerSeries ℚ) = C (3071488 : ℚ) := (map_ofNat C 3071488).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3145728 : derivative ℚ (3145728 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3145728
@[simp] lemma cc3145728 : constantCoeff (3145728 : PowerSeries ℚ) = 3145728 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3145728
lemma cm3145728 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3145728 : PowerSeries ℚ) * F) = 3145728 * coeff m F := by
  have e : (3145728 : PowerSeries ℚ) = C (3145728 : ℚ) := (map_ofNat C 3145728).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3538944 : derivative ℚ (3538944 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3538944
@[simp] lemma cc3538944 : constantCoeff (3538944 : PowerSeries ℚ) = 3538944 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3538944
lemma cm3538944 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3538944 : PowerSeries ℚ) * F) = 3538944 * coeff m F := by
  have e : (3538944 : PowerSeries ℚ) = C (3538944 : ℚ) := (map_ofNat C 3538944).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3784704 : derivative ℚ (3784704 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3784704
@[simp] lemma cc3784704 : constantCoeff (3784704 : PowerSeries ℚ) = 3784704 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3784704
lemma cm3784704 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3784704 : PowerSeries ℚ) * F) = 3784704 * coeff m F := by
  have e : (3784704 : PowerSeries ℚ) = C (3784704 : ℚ) := (map_ofNat C 3784704).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn3932160 : derivative ℚ (3932160 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 3932160
@[simp] lemma cc3932160 : constantCoeff (3932160 : PowerSeries ℚ) = 3932160 := by simpa using map_natCast (constantCoeff (R := ℚ)) 3932160
lemma cm3932160 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((3932160 : PowerSeries ℚ) * F) = 3932160 * coeff m F := by
  have e : (3932160 : PowerSeries ℚ) = C (3932160 : ℚ) := (map_ofNat C 3932160).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4173744 : derivative ℚ (4173744 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4173744
@[simp] lemma cc4173744 : constantCoeff (4173744 : PowerSeries ℚ) = 4173744 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4173744
lemma cm4173744 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4173744 : PowerSeries ℚ) * F) = 4173744 * coeff m F := by
  have e : (4173744 : PowerSeries ℚ) = C (4173744 : ℚ) := (map_ofNat C 4173744).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn4595712 : derivative ℚ (4595712 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 4595712
@[simp] lemma cc4595712 : constantCoeff (4595712 : PowerSeries ℚ) = 4595712 := by simpa using map_natCast (constantCoeff (R := ℚ)) 4595712
lemma cm4595712 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((4595712 : PowerSeries ℚ) * F) = 4595712 * coeff m F := by
  have e : (4595712 : PowerSeries ℚ) = C (4595712 : ℚ) := (map_ofNat C 4595712).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5296704 : derivative ℚ (5296704 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5296704
@[simp] lemma cc5296704 : constantCoeff (5296704 : PowerSeries ℚ) = 5296704 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5296704
lemma cm5296704 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5296704 : PowerSeries ℚ) * F) = 5296704 * coeff m F := by
  have e : (5296704 : PowerSeries ℚ) = C (5296704 : ℚ) := (map_ofNat C 5296704).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5505024 : derivative ℚ (5505024 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5505024
@[simp] lemma cc5505024 : constantCoeff (5505024 : PowerSeries ℚ) = 5505024 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5505024
lemma cm5505024 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5505024 : PowerSeries ℚ) * F) = 5505024 * coeff m F := by
  have e : (5505024 : PowerSeries ℚ) = C (5505024 : ℚ) := (map_ofNat C 5505024).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn5821824 : derivative ℚ (5821824 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 5821824
@[simp] lemma cc5821824 : constantCoeff (5821824 : PowerSeries ℚ) = 5821824 := by simpa using map_natCast (constantCoeff (R := ℚ)) 5821824
lemma cm5821824 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((5821824 : PowerSeries ℚ) * F) = 5821824 * coeff m F := by
  have e : (5821824 : PowerSeries ℚ) = C (5821824 : ℚ) := (map_ofNat C 5821824).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn7471104 : derivative ℚ (7471104 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 7471104
@[simp] lemma cc7471104 : constantCoeff (7471104 : PowerSeries ℚ) = 7471104 := by simpa using map_natCast (constantCoeff (R := ℚ)) 7471104
lemma cm7471104 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((7471104 : PowerSeries ℚ) * F) = 7471104 * coeff m F := by
  have e : (7471104 : PowerSeries ℚ) = C (7471104 : ℚ) := (map_ofNat C 7471104).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn8650752 : derivative ℚ (8650752 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 8650752
@[simp] lemma cc8650752 : constantCoeff (8650752 : PowerSeries ℚ) = 8650752 := by simpa using map_natCast (constantCoeff (R := ℚ)) 8650752
lemma cm8650752 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((8650752 : PowerSeries ℚ) * F) = 8650752 * coeff m F := by
  have e : (8650752 : PowerSeries ℚ) = C (8650752 : ℚ) := (map_ofNat C 8650752).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn9437184 : derivative ℚ (9437184 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 9437184
@[simp] lemma cc9437184 : constantCoeff (9437184 : PowerSeries ℚ) = 9437184 := by simpa using map_natCast (constantCoeff (R := ℚ)) 9437184
lemma cm9437184 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((9437184 : PowerSeries ℚ) * F) = 9437184 * coeff m F := by
  have e : (9437184 : PowerSeries ℚ) = C (9437184 : ℚ) := (map_ofNat C 9437184).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn10485760 : derivative ℚ (10485760 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 10485760
@[simp] lemma cc10485760 : constantCoeff (10485760 : PowerSeries ℚ) = 10485760 := by simpa using map_natCast (constantCoeff (R := ℚ)) 10485760
lemma cm10485760 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((10485760 : PowerSeries ℚ) * F) = 10485760 * coeff m F := by
  have e : (10485760 : PowerSeries ℚ) = C (10485760 : ℚ) := (map_ofNat C 10485760).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn14942208 : derivative ℚ (14942208 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 14942208
@[simp] lemma cc14942208 : constantCoeff (14942208 : PowerSeries ℚ) = 14942208 := by simpa using map_natCast (constantCoeff (R := ℚ)) 14942208
lemma cm14942208 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((14942208 : PowerSeries ℚ) * F) = 14942208 * coeff m F := by
  have e : (14942208 : PowerSeries ℚ) = C (14942208 : ℚ) := (map_ofNat C 14942208).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn16777216 : derivative ℚ (16777216 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 16777216
@[simp] lemma cc16777216 : constantCoeff (16777216 : PowerSeries ℚ) = 16777216 := by simpa using map_natCast (constantCoeff (R := ℚ)) 16777216
lemma cm16777216 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((16777216 : PowerSeries ℚ) * F) = 16777216 * coeff m F := by
  have e : (16777216 : PowerSeries ℚ) = C (16777216 : ℚ) := (map_ofNat C 16777216).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn19660800 : derivative ℚ (19660800 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 19660800
@[simp] lemma cc19660800 : constantCoeff (19660800 : PowerSeries ℚ) = 19660800 := by simpa using map_natCast (constantCoeff (R := ℚ)) 19660800
lemma cm19660800 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((19660800 : PowerSeries ℚ) * F) = 19660800 * coeff m F := by
  have e : (19660800 : PowerSeries ℚ) = C (19660800 : ℚ) := (map_ofNat C 19660800).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn22779904 : derivative ℚ (22779904 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 22779904
@[simp] lemma cc22779904 : constantCoeff (22779904 : PowerSeries ℚ) = 22779904 := by simpa using map_natCast (constantCoeff (R := ℚ)) 22779904
lemma cm22779904 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((22779904 : PowerSeries ℚ) * F) = 22779904 * coeff m F := by
  have e : (22779904 : PowerSeries ℚ) = C (22779904 : ℚ) := (map_ofNat C 22779904).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn25165824 : derivative ℚ (25165824 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 25165824
@[simp] lemma cc25165824 : constantCoeff (25165824 : PowerSeries ℚ) = 25165824 := by simpa using map_natCast (constantCoeff (R := ℚ)) 25165824
lemma cm25165824 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((25165824 : PowerSeries ℚ) * F) = 25165824 * coeff m F := by
  have e : (25165824 : PowerSeries ℚ) = C (25165824 : ℚ) := (map_ofNat C 25165824).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn36698112 : derivative ℚ (36698112 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 36698112
@[simp] lemma cc36698112 : constantCoeff (36698112 : PowerSeries ℚ) = 36698112 := by simpa using map_natCast (constantCoeff (R := ℚ)) 36698112
lemma cm36698112 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((36698112 : PowerSeries ℚ) * F) = 36698112 * coeff m F := by
  have e : (36698112 : PowerSeries ℚ) = C (36698112 : ℚ) := (map_ofNat C 36698112).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn38180352 : derivative ℚ (38180352 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 38180352
@[simp] lemma cc38180352 : constantCoeff (38180352 : PowerSeries ℚ) = 38180352 := by simpa using map_natCast (constantCoeff (R := ℚ)) 38180352
lemma cm38180352 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((38180352 : PowerSeries ℚ) * F) = 38180352 * coeff m F := by
  have e : (38180352 : PowerSeries ℚ) = C (38180352 : ℚ) := (map_ofNat C 38180352).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn47087616 : derivative ℚ (47087616 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 47087616
@[simp] lemma cc47087616 : constantCoeff (47087616 : PowerSeries ℚ) = 47087616 := by simpa using map_natCast (constantCoeff (R := ℚ)) 47087616
lemma cm47087616 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((47087616 : PowerSeries ℚ) * F) = 47087616 * coeff m F := by
  have e : (47087616 : PowerSeries ℚ) = C (47087616 : ℚ) := (map_ofNat C 47087616).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn80781312 : derivative ℚ (80781312 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 80781312
@[simp] lemma cc80781312 : constantCoeff (80781312 : PowerSeries ℚ) = 80781312 := by simpa using map_natCast (constantCoeff (R := ℚ)) 80781312
lemma cm80781312 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((80781312 : PowerSeries ℚ) * F) = 80781312 * coeff m F := by
  have e : (80781312 : PowerSeries ℚ) = C (80781312 : ℚ) := (map_ofNat C 80781312).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn98402304 : derivative ℚ (98402304 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 98402304
@[simp] lemma cc98402304 : constantCoeff (98402304 : PowerSeries ℚ) = 98402304 := by simpa using map_natCast (constantCoeff (R := ℚ)) 98402304
lemma cm98402304 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((98402304 : PowerSeries ℚ) * F) = 98402304 * coeff m F := by
  have e : (98402304 : PowerSeries ℚ) = C (98402304 : ℚ) := (map_ofNat C 98402304).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn195035136 : derivative ℚ (195035136 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 195035136
@[simp] lemma cc195035136 : constantCoeff (195035136 : PowerSeries ℚ) = 195035136 := by simpa using map_natCast (constantCoeff (R := ℚ)) 195035136
lemma cm195035136 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((195035136 : PowerSeries ℚ) * F) = 195035136 * coeff m F := by
  have e : (195035136 : PowerSeries ℚ) = C (195035136 : ℚ) := (map_ofNat C 195035136).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn228065280 : derivative ℚ (228065280 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 228065280
@[simp] lemma cc228065280 : constantCoeff (228065280 : PowerSeries ℚ) = 228065280 := by simpa using map_natCast (constantCoeff (R := ℚ)) 228065280
lemma cm228065280 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((228065280 : PowerSeries ℚ) * F) = 228065280 * coeff m F := by
  have e : (228065280 : PowerSeries ℚ) = C (228065280 : ℚ) := (map_ofNat C 228065280).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1064042496 : derivative ℚ (1064042496 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1064042496
@[simp] lemma cc1064042496 : constantCoeff (1064042496 : PowerSeries ℚ) = 1064042496 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1064042496
lemma cm1064042496 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1064042496 : PowerSeries ℚ) * F) = 1064042496 * coeff m F := by
  have e : (1064042496 : PowerSeries ℚ) = C (1064042496 : ℚ) := (map_ofNat C 1064042496).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn1610612736 : derivative ℚ (1610612736 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 1610612736
@[simp] lemma cc1610612736 : constantCoeff (1610612736 : PowerSeries ℚ) = 1610612736 := by simpa using map_natCast (constantCoeff (R := ℚ)) 1610612736
lemma cm1610612736 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((1610612736 : PowerSeries ℚ) * F) = 1610612736 * coeff m F := by
  have e : (1610612736 : PowerSeries ℚ) = C (1610612736 : ℚ) := (map_ofNat C 1610612736).symm
  rw [e, coeff_C_mul]
@[simp] lemma dn2818572288 : derivative ℚ (2818572288 : PowerSeries ℚ) = 0 := by simpa using Derivation.map_natCast (derivative ℚ) 2818572288
@[simp] lemma cc2818572288 : constantCoeff (2818572288 : PowerSeries ℚ) = 2818572288 := by simpa using map_natCast (constantCoeff (R := ℚ)) 2818572288
lemma cm2818572288 (F : PowerSeries ℚ) (m : ℕ) : coeff m ((2818572288 : PowerSeries ℚ) * F) = 2818572288 * coeff m F := by
  have e : (2818572288 : PowerSeries ℚ) = C (2818572288 : ℚ) := (map_ofNat C 2818572288).symm
  rw [e, coeff_C_mul]

set_option maxHeartbeats 8000000 in
lemma ode_G (G : PowerSeries ℚ) (hP : ((1) * G ^ 3 + (1) * G ^ 4 + (1) * X ^ 1 * G ^ 2 + (2) * X ^ 2 * G ^ 1 + (4) * X ^ 2 * G ^ 2 + (4) * X ^ 4 : PowerSeries ℚ) = 0) : ((245) * X ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-420) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (420) * X ^ 3 * (derivative ℚ G) + (5040) * X ^ 3 * G ^ 1 + (-3920) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-3216) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (-9216) * X ^ 4 * (derivative ℚ G) + (-64896) * X ^ 4 * G ^ 1 + (23248) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (75648) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (72192) * X ^ 5 * (derivative ℚ G) + (196608) * X ^ 5 * G ^ 1 + (-53888) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-390144) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (-190464) * X ^ 6 * (derivative ℚ G) + (-98304) * X ^ 6 * G ^ 1 + (-19456) * X ^ 7 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (860160) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (98304) * X ^ 7 * (derivative ℚ G) + (303104) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-786432) * X ^ 8 * (derivative ℚ (derivative ℚ G)) + (-393216) * X ^ 9 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = ((-1260) * X ^ 3 + (16224) * X ^ 4 + (-49152) * X ^ 5 + (24576) * X ^ 6 : PowerSeries ℚ) := by
  have d1 : ((1) * G ^ 2 + (3) * G ^ 2 * (derivative ℚ G) + (4) * G ^ 3 * (derivative ℚ G) + (4) * X ^ 1 * G ^ 1 + (2) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (8) * X ^ 1 * G ^ 2 + (2) * X ^ 2 * (derivative ℚ G) + (8) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (16) * X ^ 3 : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) hP
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L1 : ((-98) * X ^ 4 * (derivative ℚ G) + (840) * X ^ 5 * (derivative ℚ G) + (-512) * X ^ 6 * (derivative ℚ G) + (-9216) * X ^ 7 * (derivative ℚ G) + (8192) * X ^ 8 * (derivative ℚ G) + (32768) * X ^ 9 * (derivative ℚ G) : PowerSeries ℚ) = ((-98) * X ^ 3 * G ^ 1 + (70) * X ^ 3 * G ^ 2 + (168) * X ^ 3 * G ^ 3 + (924) * X ^ 4 * G ^ 1 + (-272) * X ^ 4 * G ^ 2 + (-832) * X ^ 4 * G ^ 3 + (196) * X ^ 5 + (-592) * X ^ 5 * G ^ 1 + (-384) * X ^ 5 * G ^ 2 + (-512) * X ^ 5 * G ^ 3 + (-1120) * X ^ 6 + (-11136) * X ^ 6 * G ^ 1 + (1024) * X ^ 6 * G ^ 2 + (4096) * X ^ 6 * G ^ 3 + (-256) * X ^ 7 + (9216) * X ^ 7 * G ^ 1 + (6144) * X ^ 8 + (40960) * X ^ 8 * G ^ 1 : PowerSeries ℚ) := by
    linear_combination (((-35) * G ^ 2 + (-35) * G ^ 3 + (-42) * X ^ 1 * G ^ 1 + (157) * X ^ 1 * G ^ 2 + (164) * X ^ 1 * G ^ 3 + (-49) * X ^ 2 + (124) * X ^ 2 * G ^ 1 + (424) * X ^ 2 * G ^ 2 + (352) * X ^ 2 * G ^ 3 + (238) * X ^ 3 + (824) * X ^ 3 * G ^ 1 + (-1344) * X ^ 3 * G ^ 2 + (-1280) * X ^ 3 * G ^ 3 + (496) * X ^ 4 + (-960) * X ^ 4 * G ^ 1 + (-2560) * X ^ 4 * G ^ 2 + (-2048) * X ^ 4 * G ^ 3 + (-1920) * X ^ 5 + (-5632) * X ^ 5 * G ^ 1 + (-3072) * X ^ 6 + (-4096) * X ^ 6 * G ^ 1 : PowerSeries ℚ)) * d1 + (((35) * G ^ 1 + (105) * G ^ 1 * (derivative ℚ G) + (140) * G ^ 2 * (derivative ℚ G) + (147) * X ^ 1 + (91) * X ^ 1 * (derivative ℚ G) + (116) * X ^ 1 * G ^ 1 + (-464) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (-656) * X ^ 1 * G ^ 2 * (derivative ℚ G) + (-672) * X ^ 2 + (-376) * X ^ 2 * (derivative ℚ G) + (-1664) * X ^ 2 * G ^ 1 + (-1344) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (-1408) * X ^ 2 * G ^ 2 * (derivative ℚ G) + (-1920) * X ^ 3 + (-1344) * X ^ 3 * (derivative ℚ G) + (-1536) * X ^ 3 * G ^ 1 + (4096) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (5120) * X ^ 3 * G ^ 2 * (derivative ℚ G) + (6144) * X ^ 4 + (3584) * X ^ 4 * (derivative ℚ G) + (12288) * X ^ 4 * G ^ 1 + (8192) * X ^ 4 * G ^ 1 * (derivative ℚ G) + (8192) * X ^ 4 * G ^ 2 * (derivative ℚ G) + (12288) * X ^ 5 + (8192) * X ^ 5 * (derivative ℚ G) + (16384) * X ^ 5 * G ^ 1 : PowerSeries ℚ)) * hP
  have e2 : ((294) * X ^ 2 * G ^ 1 + (-210) * X ^ 2 * G ^ 2 + (-504) * X ^ 2 * G ^ 3 + (-294) * X ^ 3 * (derivative ℚ G) + (-3696) * X ^ 3 * G ^ 1 + (-140) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (1088) * X ^ 3 * G ^ 2 + (-504) * X ^ 3 * G ^ 2 * (derivative ℚ G) + (3328) * X ^ 3 * G ^ 3 + (-980) * X ^ 4 + (-98) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (3276) * X ^ 4 * (derivative ℚ G) + (2960) * X ^ 4 * G ^ 1 + (544) * X ^ 4 * G ^ 1 * (derivative ℚ G) + (1920) * X ^ 4 * G ^ 2 + (2496) * X ^ 4 * G ^ 2 * (derivative ℚ G) + (2560) * X ^ 4 * G ^ 3 + (6720) * X ^ 5 + (840) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (-2480) * X ^ 5 * (derivative ℚ G) + (66816) * X ^ 5 * G ^ 1 + (768) * X ^ 5 * G ^ 1 * (derivative ℚ G) + (-6144) * X ^ 5 * G ^ 2 + (1536) * X ^ 5 * G ^ 2 * (derivative ℚ G) + (-24576) * X ^ 5 * G ^ 3 + (1792) * X ^ 6 + (-512) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (-53376) * X ^ 6 * (derivative ℚ G) + (-64512) * X ^ 6 * G ^ 1 + (-2048) * X ^ 6 * G ^ 1 * (derivative ℚ G) + (-12288) * X ^ 6 * G ^ 2 * (derivative ℚ G) + (-49152) * X ^ 7 + (-9216) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (56320) * X ^ 7 * (derivative ℚ G) + (-327680) * X ^ 7 * G ^ 1 + (8192) * X ^ 8 * (derivative ℚ (derivative ℚ G)) + (253952) * X ^ 8 * (derivative ℚ G) + (32768) * X ^ 9 * (derivative ℚ (derivative ℚ G)) : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) L1
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L2 : ((49) * X ^ 2 * (derivative ℚ (derivative ℚ G)) + (-616) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (1936) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (3584) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (-22528) * X ^ 6 * (derivative ℚ (derivative ℚ G)) + (65536) * X ^ 8 * (derivative ℚ (derivative ℚ G)) : PowerSeries ℚ) = ((-70) * G ^ 2 + (-70) * G ^ 3 + (-84) * X ^ 1 * G ^ 1 + (610) * X ^ 1 * G ^ 2 + (624) * X ^ 1 * G ^ 3 + (-196) * X ^ 2 + (536) * X ^ 2 * G ^ 1 + (-1584) * X ^ 2 * G ^ 2 + (-2112) * X ^ 2 * G ^ 3 + (1708) * X ^ 3 + (-160) * X ^ 3 * G ^ 1 + (-640) * X ^ 3 * G ^ 2 + (2048) * X ^ 3 * G ^ 3 + (-3872) * X ^ 4 + (-4992) * X ^ 4 * G ^ 1 + (7168) * X ^ 4 * G ^ 2 + (4096) * X ^ 4 * G ^ 3 + (-1792) * X ^ 5 + (8192) * X ^ 5 * G ^ 1 + (10240) * X ^ 6 + (8192) * X ^ 6 * G ^ 1 : PowerSeries ℚ) := by
    have hm : ((-14) * X ^ 3 + (32) * X ^ 4 + (128) * X ^ 5 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((-14) * X ^ 0 + (32) * X ^ 1 + (128) * X ^ 2 : PowerSeries ℚ)) 3 (by ring) (by simp <;> norm_num)
    apply mul_left_cancel₀ hm
    linear_combination (((7) * X ^ 1 + (-44) * X ^ 2 + (256) * X ^ 4 : PowerSeries ℚ)) * e2 + (((-21) * X ^ 0 + (-10) * G ^ 1 + (-36) * G ^ 2 + (186) * X ^ 1 + (16) * X ^ 1 * G ^ 1 + (96) * X ^ 1 * G ^ 2 + (56) * X ^ 2 + (-1984) * X ^ 3 : PowerSeries ℚ)) * L1 + (((1848) * X ^ 3 + (-6048) * X ^ 3 * G ^ 1 + (-18560) * X ^ 4 + (46080) * X ^ 4 * G ^ 1 + (40960) * X ^ 5 + (-61440) * X ^ 5 * G ^ 1 + (73728) * X ^ 6 + (-196608) * X ^ 6 * G ^ 1 + (-229376) * X ^ 7 + (393216) * X ^ 7 * G ^ 1 : PowerSeries ℚ)) * hP
  have e3 : ((84) * G ^ 1 + (140) * G ^ 1 * (derivative ℚ G) + (-610) * G ^ 2 + (210) * G ^ 2 * (derivative ℚ G) + (-624) * G ^ 3 + (392) * X ^ 1 + (98) * X ^ 1 * (derivative ℚ (derivative ℚ G)) + (84) * X ^ 1 * (derivative ℚ G) + (-1072) * X ^ 1 * G ^ 1 + (-1220) * X ^ 1 * G ^ 1 * (derivative ℚ G) + (3168) * X ^ 1 * G ^ 2 + (-1872) * X ^ 1 * G ^ 2 * (derivative ℚ G) + (4224) * X ^ 1 * G ^ 3 + (-5124) * X ^ 2 + (49) * X ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-1848) * X ^ 2 * (derivative ℚ (derivative ℚ G)) + (-536) * X ^ 2 * (derivative ℚ G) + (480) * X ^ 2 * G ^ 1 + (3168) * X ^ 2 * G ^ 1 * (derivative ℚ G) + (1920) * X ^ 2 * G ^ 2 + (6336) * X ^ 2 * G ^ 2 * (derivative ℚ G) + (-6144) * X ^ 2 * G ^ 3 + (15488) * X ^ 3 + (-616) * X ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (7744) * X ^ 3 * (derivative ℚ (derivative ℚ G)) + (160) * X ^ 3 * (derivative ℚ G) + (19968) * X ^ 3 * G ^ 1 + (1280) * X ^ 3 * G ^ 1 * (derivative ℚ G) + (-28672) * X ^ 3 * G ^ 2 + (-6144) * X ^ 3 * G ^ 2 * (derivative ℚ G) + (-16384) * X ^ 3 * G ^ 3 + (8960) * X ^ 4 + (1936) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (17920) * X ^ 4 * (derivative ℚ (derivative ℚ G)) + (4992) * X ^ 4 * (derivative ℚ G) + (-40960) * X ^ 4 * G ^ 1 + (-14336) * X ^ 4 * G ^ 1 * (derivative ℚ G) + (-12288) * X ^ 4 * G ^ 2 * (derivative ℚ G) + (-61440) * X ^ 5 + (3584) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-135168) * X ^ 5 * (derivative ℚ (derivative ℚ G)) + (-8192) * X ^ 5 * (derivative ℚ G) + (-49152) * X ^ 5 * G ^ 1 + (-22528) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-8192) * X ^ 6 * (derivative ℚ G) + (524288) * X ^ 7 * (derivative ℚ (derivative ℚ G)) + (65536) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = 0 := by
    have h := congrArg (derivative ℚ) L2
    simp [Derivation.leibniz, Derivation.leibniz_pow] at h
    linear_combination h
  have L3 : ((343) * X ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6468) * X ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (40656) * X ^ 4 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-47552) * X ^ 5 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-473088) * X ^ 6 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (1486848) * X ^ 7 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (1376256) * X ^ 8 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-8650752) * X ^ 9 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (16777216) * X ^ 11 * (derivative ℚ (derivative ℚ (derivative ℚ G))) : PowerSeries ℚ) = ((-840) * G ^ 2 + (-840) * G ^ 3 + (-1596) * X ^ 1 * G ^ 1 + (-6852) * X ^ 1 * G ^ 2 + (-6096) * X ^ 1 * G ^ 3 + (-4116) * X ^ 2 + (-3048) * X ^ 2 * G ^ 1 + (137664) * X ^ 2 * G ^ 2 + (121344) * X ^ 2 * G ^ 3 + (8568) * X ^ 3 + (132768) * X ^ 3 * G ^ 1 + (-570624) * X ^ 3 * G ^ 2 + (-562176) * X ^ 3 * G ^ 3 + (295296) * X ^ 4 + (-407040) * X ^ 4 * G ^ 1 + (632832) * X ^ 4 * G ^ 2 + (1302528) * X ^ 4 * G ^ 3 + (-1709568) * X ^ 5 + (-546816) * X ^ 5 * G ^ 1 + (1277952) * X ^ 5 * G ^ 2 + (-1179648) * X ^ 5 * G ^ 3 + (2273280) * X ^ 6 + (3784704) * X ^ 6 * G ^ 1 + (-3538944) * X ^ 6 * G ^ 2 + (-1572864) * X ^ 6 * G ^ 3 + (2752512) * X ^ 7 + (-3932160) * X ^ 7 * G ^ 1 + (-5505024) * X ^ 8 + (-3145728) * X ^ 8 * G ^ 1 : PowerSeries ℚ) := by
    have hm : ((-7) * X ^ 4 + (16) * X ^ 5 + (64) * X ^ 6 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((-7) * X ^ 0 + (16) * X ^ 1 + (64) * X ^ 2 : PowerSeries ℚ)) 4 (by ring) (by simp <;> norm_num)
    apply mul_left_cancel₀ hm
    linear_combination (((-49) * X ^ 4 + (420) * X ^ 5 + (-256) * X ^ 6 + (-4608) * X ^ 7 + (4096) * X ^ 8 + (16384) * X ^ 9 : PowerSeries ℚ)) * e3 + (((98) * X ^ 3 + (-1456) * X ^ 4 + (1920) * X ^ 5 + (25600) * X ^ 6 + (-32768) * X ^ 7 + (-131072) * X ^ 8 : PowerSeries ℚ)) * L2 + (((-70) * G ^ 1 + (-105) * G ^ 2 + (-42) * X ^ 1 + (610) * X ^ 1 * G ^ 1 + (936) * X ^ 1 * G ^ 2 + (268) * X ^ 2 + (-1584) * X ^ 2 * G ^ 1 + (-3168) * X ^ 2 * G ^ 2 + (-80) * X ^ 3 + (-640) * X ^ 3 * G ^ 1 + (3072) * X ^ 3 * G ^ 2 + (-2496) * X ^ 4 + (7168) * X ^ 4 * G ^ 1 + (6144) * X ^ 4 * G ^ 2 + (4096) * X ^ 5 + (4096) * X ^ 6 : PowerSeries ℚ)) * L1 + (((-1470) * X ^ 3 + (-17640) * X ^ 3 * G ^ 1 + (10192) * X ^ 4 + (244608) * X ^ 4 * G ^ 1 + (83392) * X ^ 5 + (-1257216) * X ^ 5 * G ^ 1 + (-1021440) * X ^ 6 + (2242560) * X ^ 6 * G ^ 1 + (2883584) * X ^ 7 + (3932160) * X ^ 7 * G ^ 1 + (1441792) * X ^ 8 + (-19660800) * X ^ 8 * G ^ 1 + (-14942208) * X ^ 9 + (9437184) * X ^ 9 * G ^ 1 + (10485760) * X ^ 10 + (25165824) * X ^ 10 * G ^ 1 : PowerSeries ℚ)) * hP
  have hm : ((-49) * X ^ 1 + (420) * X ^ 2 + (-256) * X ^ 3 + (-4608) * X ^ 4 + (4096) * X ^ 5 + (16384) * X ^ 6 : PowerSeries ℚ) ≠ 0 := ne_zero_of _ (((-49) * X ^ 0 + (420) * X ^ 1 + (-256) * X ^ 2 + (-4608) * X ^ 3 + (4096) * X ^ 4 + (16384) * X ^ 5 : PowerSeries ℚ)) 1 (by ring) (by simp <;> norm_num)
  apply mul_left_cancel₀ hm
  linear_combination (((210) * X ^ 0 + (-4608) * X ^ 1 + (36096) * X ^ 2 + (-95232) * X ^ 3 + (49152) * X ^ 4 : PowerSeries ℚ)) * L1 + (((420) * X ^ 2 + (4896) * X ^ 3 + (-56064) * X ^ 4 + (165888) * X ^ 5 + (-196608) * X ^ 6 : PowerSeries ℚ)) * L2 + (((-35) * X ^ 2 + (200) * X ^ 3 + (-384) * X ^ 4 : PowerSeries ℚ)) * L3 + ((0 : PowerSeries ℚ)) * hP

set_option maxHeartbeats 4000000 in
lemma rec_a (G : PowerSeries ℚ) (hP : ((1) * G ^ 3 + (1) * G ^ 4 + (1) * X ^ 1 * G ^ 2 + (2) * X ^ 2 * G ^ 1 + (4) * X ^ 2 * G ^ 2 + (4) * X ^ 4 : PowerSeries ℚ) = 0) (k : ℕ) : (245*((k + 7 : ℕ) : ℚ)^3 - 735*((k + 7 : ℕ) : ℚ)^2 + 490*((k + 7 : ℕ) : ℚ)) * coeff (k + 7) G + (-3920*((k + 7 : ℕ) : ℚ)^3 + 23100*((k + 7 : ℕ) : ℚ)^2 - 41860*((k + 7 : ℕ) : ℚ) + 22680) * coeff (k + 6) G + (23248*((k + 7 : ℕ) : ℚ)^3 - 212448*((k + 7 : ℕ) : ℚ)^2 + 620948*((k + 7 : ℕ) : ℚ) - 578088) * coeff (k + 5) G + (-53888*((k + 7 : ℕ) : ℚ)^3 + 722304*((k + 7 : ℕ) : ℚ)^2 - 3071488*((k + 7 : ℕ) : ℚ) + 4173744) * coeff (k + 4) G + (-19456*((k + 7 : ℕ) : ℚ)^3 - 98304*((k + 7 : ℕ) : ℚ)^2 + 2143744*((k + 7 : ℕ) : ℚ) - 5821824) * coeff (k + 3) G + (303104*((k + 7 : ℕ) : ℚ)^3 - 4595712*((k + 7 : ℕ) : ℚ)^2 + 22779904*((k + 7 : ℕ) : ℚ) - 36698112) * coeff (k + 2) G + (-393216*((k + 7 : ℕ) : ℚ)^3 + 7471104*((k + 7 : ℕ) : ℚ)^2 - 47087616*((k + 7 : ℕ) : ℚ) + 98402304) * coeff (k + 1) G = 0 := by
  have h := congrArg (coeff (k + 7)) (ode_G G hP)
  rcases k with _ | _ | k
  all_goals
    simp only [add_mul, sub_mul, neg_mul, one_mul, map_add, map_sub, map_neg, mul_assoc, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm14, cm16, cm21, cm32, cm35, cm36, cm42, cm44, cm48, cm49, cm50, cm56, cm64, cm70, cm80, cm84, cm91, cm96, cm98, cm105, cm116, cm124, cm128, cm140, cm147, cm157, cm160, cm164, cm168, cm186, cm196, cm200, cm210, cm238, cm245, cm256, cm268, cm272, cm294, cm320, cm343, cm352, cm376, cm384, cm392, cm420, cm424, cm464, cm480, cm490, cm496, cm504, cm512, cm536, cm544, cm592, cm610, cm616, cm624, cm640, cm656, cm672, cm735, cm768, cm824, cm832, cm840, cm924, cm936, cm960, cm980, cm1024, cm1072, cm1088, cm1120, cm1220, cm1260, cm1280, cm1344, cm1408, cm1456, cm1470, cm1536, cm1584, cm1596, cm1664, cm1708, cm1792, cm1848, cm1872, cm1920, cm1936, cm1984, cm2048, cm2112, cm2480, cm2496, cm2560, cm2960, cm3048, cm3072, cm3168, cm3216, cm3276, cm3328, cm3584, cm3696, cm3872, cm3920, cm4096, cm4116, cm4224, cm4608, cm4896, cm4992, cm5040, cm5120, cm5124, cm5632, cm6048, cm6096, cm6144, cm6336, cm6468, cm6720, cm6852, cm7168, cm7744, cm8192, cm8568, cm8960, cm9216, cm10192, cm10240, cm11136, cm12288, cm14336, cm15488, cm16224, cm16384, cm17640, cm17920, cm18560, cm19456, cm19968, cm22528, cm22680, cm23100, cm23248, cm24576, cm25600, cm28672, cm32768, cm36096, cm40656, cm40960, cm41860, cm46080, cm47552, cm49152, cm53376, cm53888, cm56064, cm56320, cm61440, cm64512, cm64896, cm65536, cm66816, cm72192, cm73728, cm75648, cm83392, cm95232, cm98304, cm121344, cm131072, cm132768, cm135168, cm137664, cm165888, cm190464, cm196608, cm212448, cm229376, cm244608, cm246960, cm253952, cm295296, cm303104, cm327680, cm390144, cm393216, cm407040, cm473088, cm524288, cm546816, cm562176, cm570624, cm578088, cm620948, cm632832, cm722304, cm786432, cm860160, cm1021440, cm1179648, cm1257216, cm1277952, cm1302528, cm1376256, cm1441792, cm1486848, cm1572864, cm1709568, cm2143744, cm2242560, cm2273280, cm2752512, cm2883584, cm3071488, cm3145728, cm3538944, cm3784704, cm3932160, cm4173744, cm4595712, cm5296704, cm5505024, cm5821824, cm7471104, cm8650752, cm9437184, cm10485760, cm14942208, cm16777216, cm19660800, cm22779904, cm25165824, cm36698112, cm38180352, cm47087616, cm80781312, cm98402304, cm195035136, cm228065280, cm1064042496, cm1610612736, cm2818572288, coeff_X_pow_mul', coeff_derivative] at h
    simp [PowerSeries.coeff_X] at h
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at h ⊢
    push_cast at h ⊢
    try simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
    linear_combination h

end OMA.S_oeis_a243764

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a243764.main := by
  intro T W G hT hT0 hW hW0 hG hG0 n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  have hP : ((1) * G ^ 3 + (1) * G ^ 4 + (1) * X ^ 1 * G ^ 2 + (2) * X ^ 2 * G ^ 1 + (4) * X ^ 2 * G ^ 2 + (4) * X ^ 4 : PowerSeries ℚ) = 0 := by
    have hx : (256 * X ^ 4 : PowerSeries ℚ) * (4*X^4 + 4*X^2*G^2 + 2*X^2*G + X*G^2 + G^4 + G^3) = 0 := by
      linear_combination (64*W*X^5*G + 32*W*X^4*G^2 + 32*W*X^3*G^3 + 256*X^7 + 128*X^5*G^2 + 64*X^5*G + 160*X^4*G^2 + 96*X^3*G^3 + 64*X^2*G^4) * hT + (-16*W*X^3*G^3 - 8*W*X^2*G^4 - 8*W*X*G^5 - 64*X^5*G^2 + 64*X^4*G^2 - 32*X^3*G^4 + 48*X^3*G^3 + 40*X^2*G^4 + 8*X*G^5) * hW + (-32*T*W*X^4*G - 16*T*W*X^3*G^2 - 16*T*W*X^2*G^3 - 128*T*X^6 - 64*T*X^4*G^2 - 32*T*X^4*G - 80*T*X^3*G^2 - 48*T*X^2*G^3 - 32*T*X*G^4 + 16*W^2*X^3*G^2 + 8*W^2*X^2*G^3 + 8*W^2*X*G^4 + 64*W*X^5*G - 32*W*X^4*G + 32*W*X^3*G^3 - 16*W*X^3*G^2 - 16*W*X^2*G^3 - 128*X^6 - 64*X^5*G - 192*X^4*G^2 - 32*X^4*G - 32*X^3*G^3 + 32*X^3*G^2 - 64*X^2*G^4 + 8*X^2*G^3 + 24*X*G^4) * hG
    have hne : (256 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
      intro h0
      have h1 := congrArg PowerSeries.constantCoeff h0
      have h2 : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := by simpa using map_natCast (PowerSeries.constantCoeff (R := ℚ)) 256
      rw [h2] at h1
      norm_num at h1
    have h3 := (mul_eq_zero.1 hx).resolve_left hne
    linear_combination h3
  have h := OMA.S_oeis_a243764.rec_a G hP k
  simp only [show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 7 - 5 = k + 2 from by omega, show k + 7 - 6 = k + 1 from by omega]
  push_cast at h ⊢
  linear_combination h
