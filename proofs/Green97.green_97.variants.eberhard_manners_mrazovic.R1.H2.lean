import OMAReductions.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1
import Mathlib

open Green97

theorem OMA.solution : OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1.H2 := by
  classical
  intro n hn
  letI : NeZero n := ⟨hn.ne'⟩
  let A := {π : (Fin n ≃ ZMod n) × (Fin n ≃ ZMod n) //
    Function.Bijective fun i ↦ π.1 i + π.2 i}
  let B := {σ : Equiv.Perm (ZMod n) // Function.Bijective fun x ↦ x + σ x}
  let e : A ≃ ((Fin n ≃ ZMod n) × B) :=
    { toFun := fun π ↦ ⟨π.val.1,⟨π.val.1.symm.trans π.val.2, by
        have h := π.property.comp π.val.1.symm.bijective
        simpa [Function.comp_def] using h⟩⟩
      invFun := fun ⟨p,σ⟩ ↦ ⟨(p,p.trans σ.val),by
        simpa [Function.comp_def] using σ.property.comp p.bijective⟩
      left_inv := by
        rintro ⟨⟨p,q⟩,h⟩
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rfl
        ext i
        simp
      right_inv := by
        rintro ⟨p,σ⟩
        refine Prod.ext ?_ ?_
        · rfl
        apply Subtype.ext
        ext i
        simp }
  change Nat.card A = n.factorial * Nat.card B
  rw [Nat.card_congr e, Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_equiv (ZMod.finEquiv n).toEquiv, Fintype.card_fin]

