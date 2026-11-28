import OMAStatements.S_mo_429021
import Mathlib

-- Problem mo-429021: for h : [a] -> [c], the number of pairs (f, g) with f : [a] -> [b], g : [b] -> [c] and
-- g o f = h equals the sum over all g of the product over j in [c] of |g^-1(j)| ^ |h^-1(j)|.
-- Upstream: statements/mo-429021.lean (declaration OMA.S_mo_429021.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: group the pairs by g. For a fixed g, a map f satisfies g o f = h exactly when f(x) lies in the fibre
-- g^-1(h(x)) for every x, so the number of such f is the product over x of |g^-1(h(x))|. Grouping the factors
-- of this product by the value j = h(x) gives the product over j of |g^-1(j)| ^ |h^-1(j)|.

theorem OMA.solution : type_of% @OMA.S_mo_429021.main := by
  intro a b c h
  have e1 : {p : (Fin a → Fin b) × (Fin b → Fin c) // p.2 ∘ p.1 = h} ≃
      Σ g : Fin b → Fin c, {f : Fin a → Fin b // g ∘ f = h} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have e2 : ∀ g : Fin b → Fin c,
      {f : Fin a → Fin b // g ∘ f = h} ≃ ((x : Fin a) → {y : Fin b // g y = h x}) :=
    fun g =>
    { toFun := fun f x => ⟨f.1 x, congrFun f.2 x⟩
      invFun := fun φ => ⟨fun x => (φ x).1, funext fun x => (φ x).2⟩
      left_inv := fun f => rfl
      right_inv := fun φ => rfl }
  rw [Fintype.card_congr e1, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.card_congr (e2 g), Fintype.card_pi]
  have h3 := Fintype.prod_fiberwise' h (fun j => Fintype.card {y : Fin b // g y = j})
  calc ∏ x : Fin a, Fintype.card {y : Fin b // g y = h x}
      = ∏ j : Fin c, ∏ _i : {i : Fin a // h i = j}, Fintype.card {y : Fin b // g y = j} := h3.symm
    _ = ∏ j : Fin c, Fintype.card {y : Fin b // g y = j} ^ Fintype.card {x : Fin a // h x = j} := by
        apply Finset.prod_congr rfl
        intro j _
        rw [Finset.prod_const, Finset.card_univ]
