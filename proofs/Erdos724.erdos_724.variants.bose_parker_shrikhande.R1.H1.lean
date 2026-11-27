import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1
import Mathlib.Data.ZMod.Basic

/-! The affine squares with slopes one and two over the odd cyclic group. -/

open Erdos724 Fin.CommRing

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1.H1 := by
  intro n hn h3
  cases n with
  | zero => omega
  | succ k =>
    have unit : IsUnit (2 : ZMod (k+1)) := by
      simpa using (ZMod.isUnit_iff_coprime 2 (k+1)).mpr hn.coprime_two_left
    have unitFin : IsUnit (2 : Fin (k+1)) := by
      let φ : ZMod (k+1) →+* Fin (k+1) := (ZMod.finEquiv (k+1)).symm.toRingHom
      have h : IsUnit (φ (2 : ZMod (k+1))) := unit.map φ
      simpa only [map_ofNat] using h
    let L : LatinSquare (k+1) :=
      { mat := fun i j => i+j
        row_injective := fun _ _ _ h => add_left_cancel h
        col_injective := fun _ _ _ h => add_right_cancel h }
    let M : LatinSquare (k+1) :=
      { mat := fun i j => i+2*j
        row_injective := by
          intro i a b h
          change i + 2*a = i + 2*b at h
          exact unitFin.mul_right_injective (add_left_cancel h)
        col_injective := by
          intro j a b h
          change a + 2*j = b + 2*j at h
          exact add_right_cancel h }
    refine ⟨L,M,?_,?_⟩
    · intro eqn
      have h := congrArg (fun S : LatinSquare (k+1) => (S.mat 0 1).val) eqn
      change ((0+1 : Fin (k+1))).val = ((0+2*1 : Fin (k+1))).val at h
      simp only [zero_add,mul_one] at h
      change 1 % (k+1) = 2 % (k+1) at h
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
      contradiction
    · rintro ⟨i,j⟩ ⟨u,v⟩ h
      have a : i+j = u+v := congrArg Prod.fst h
      have b : i+2*j = u+2*v := congrArg Prod.snd h
      have eqj : j = v := by linear_combination b-a
      exact Prod.ext (add_right_cancel (eqj ▸ a)) eqj

