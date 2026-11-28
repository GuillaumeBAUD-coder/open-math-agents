import OMAStatements.S_mo_429021
import Mathlib

open OMA.S_mo_429021

theorem OMA.solution : type_of% @OMA.S_mo_429021.main := by
  intro a b c h
  let e : {p : (Fin a → Fin b) × (Fin b → Fin c) // p.2 ∘ p.1 = h} ≃
      Σ g : Fin b → Fin c, {f : Fin a → Fin b // g ∘ f = h} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro g _
  have e2 : {f : Fin a → Fin b // g ∘ f = h} ≃ ((x : Fin a) → {y : Fin b // g y = h x}) :=
    (Equiv.subtypeEquivRight (fun f => by rw [funext_iff]; rfl)).trans Equiv.subtypePiEquivPi
  rw [Fintype.card_congr e2, Fintype.card_pi]
  rw [← Fintype.prod_fiberwise' h (fun j => Fintype.card {y : Fin b // g y = j})]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_const, Finset.card_univ]
