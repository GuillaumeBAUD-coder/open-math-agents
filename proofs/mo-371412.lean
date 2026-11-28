import OMAStatements.S_mo_371412
import Mathlib

open OMA.S_mo_371412

lemma mo371412_perm_eq_det {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    N.permanent = N.det := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, ZMod.neg_eq_self_mod_two]

theorem OMA.solution : type_of% @OMA.S_mo_371412.main := by
  intro n M k hk hMk hp
  have hdet : IsUnit M.det := by
    have h : M.det ^ k = 1 := by rw [← Matrix.det_pow, hMk, Matrix.det_one]
    exact IsUnit.of_pow_eq_one h (by omega)
  have hpm : (M.map (Int.castRingHom (ZMod 2))).permanent =
      Int.castRingHom (ZMod 2) M.permanent := by
    simp [Matrix.permanent, map_sum, map_prod]
  have hdm : (M.map (Int.castRingHom (ZMod 2))).det = Int.castRingHom (ZMod 2) M.det :=
    (RingHom.map_det _ _).symm
  have key := mo371412_perm_eq_det (M.map (Int.castRingHom (ZMod 2)))
  rw [hpm, hdm, hp] at key
  rcases Int.isUnit_iff.mp hdet with h | h
  · rw [h] at key; simp at key
  · rw [h] at key; revert key; decide
