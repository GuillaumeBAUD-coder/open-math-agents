import OMAStatements.S_oeis_a003185
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.Cusps

/-! # A003185 from the geometric dimension formula and the level-96 counts -/

namespace OMA.R_oeis_a003185_R1

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

-- The torsion-free dimension formula in Euler-characteristic form.
def H1 : Prop :=
  ∀ N : ℕ, 0 < N →
    (∀ A : SL(2, ℤ), A ∈ Gamma0 N → ∀ z : UpperHalfPlane,
      mapGL ℝ A • z = z → mapGL ℝ A ∈ Subgroup.center (GL (Fin 2) ℝ)) →
    ∀ w : ℕ, 4 ≤ w → Even w →
      12 * Module.finrank ℂ (CuspForm (Gamma0 N) (w : ℤ)) +
        6 * Nat.card (CuspOrbits (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) =
      (w - 1) * (Gamma0 N).index

def H2 : Prop := (Gamma0 96).index = 192

def H3 : Prop := Nat.card (CuspOrbits (Gamma0 96 : Subgroup (GL (Fin 2) ℝ))) = 16

lemma trace_mod_four {N : ℕ} (hN : 4 ∣ N)
    (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) :
    ((A 0 0 + A 1 1 : ℤ) : ZMod 4) = 2 := by
  have hN' : (4 : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN
  have hc : (A 1 0 : ZMod 4) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 <|
    hN'.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.mp hA))
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have hd := A.property
    rwa [Matrix.det_fin_two] at hd
  have hp := congrArg (fun z : ℤ => (z : ZMod 4)) hdet
  push_cast at hp
  have hsmall : ∀ a b : ZMod 4, a * b = 1 → a + b = 2 := by decide
  push_cast
  exact hsmall _ _ (by simpa only [hc, mul_zero, sub_zero] using hp)

lemma no_elliptic_gamma0 {N : ℕ} (hN : 4 ∣ N)
    (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) :
    ¬ (mapGL ℝ A).IsElliptic := by
  have hs := trace_mod_four hN A hA
  have hdiv : (4 : ℤ) ∣ 2 - (A 0 0 + A 1 1) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp (by simpa using hs)
  have ha : A 0 0 + A 1 1 ≤ -2 ∨ 2 ≤ A 0 0 + A 1 1 := by omega
  have hlift : (A 0 0 : ℝ) + (A 1 1 : ℝ) ≤ -2 ∨
      2 ≤ (A 0 0 : ℝ) + (A 1 1 : ℝ) := by exact_mod_cast ha
  intro hell
  change ((mapGL ℝ A : Matrix (Fin 2) (Fin 2) ℝ)).discr < 0 at hell
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two] at hell
  have hd : (mapGL ℝ A : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    exact congrArg Units.val (det_mapGL (S := ℝ) A)
  rw [hd] at hell
  rw [mapGL_coe_matrix] at hell
  change ((A 0 0 : ℝ) + (A 1 1 : ℝ)) ^ 2 - 4 * 1 < 0 at hell
  rcases hlift with h | h <;> nlinarith

lemma fixed_point_is_central {N : ℕ} (hN : 4 ∣ N)
    (A : SL(2, ℤ)) (hA : A ∈ Gamma0 N) {z : UpperHalfPlane}
    (hz : mapGL ℝ A • z = z) :
    mapGL ℝ A ∈ Subgroup.center (GL (Fin 2) ℝ) := by
  by_contra hcenter
  apply no_elliptic_gamma0 hN A hA
  apply UpperHalfPlane.isElliptic_of_exists_smul_eq_self _ hcenter ⟨z, hz⟩
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL]
  norm_num

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a003185.main := by
  intro formula index_count cusp_count n
  have h := formula 96 (by decide)
    (fun A hA z hz => fixed_point_is_central (by decide) A hA hz)
    (2 * (n + 2)) (by omega) ⟨n + 2, by omega⟩
  rw [index_count, cusp_count] at h
  have hdim : Module.finrank ℂ (CuspForm (Gamma0 96) ((2 * (n + 2) : ℕ) : ℤ)) =
      32 * n + 40 := by omega
  have hw : ((2 * (n + 2) : ℕ) : ℤ) = 2 * ((n : ℤ) + 2) := by
    push_cast
    ring
  rw [hw] at hdim
  rw [hdim]
  unfold OMA.S_oeis_a003185.a
  push_cast
  ring

end OMA.R_oeis_a003185_R1
