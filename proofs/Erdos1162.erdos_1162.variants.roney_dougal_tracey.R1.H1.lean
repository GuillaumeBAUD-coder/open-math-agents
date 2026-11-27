import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1

-- Step Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H1: hypothesis H1 of reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1
-- Credit: @tamoghnokandar
-- H1 := ∀ n : ℕ, 2 ^ ((n / 2 / 2) * (n / 2 - n / 2 / 2)) ≤ Erdos1162.f n  /-- Upper bound (Roney-Dougal and Tracey 2025): for every `ε > 0`, `log₂ f(n) ≤ (1/16 + ε) n²` for all large `n`. -/

namespace OMA.E1162

open Classical

/-- The elementary abelian 2-group `(ℤ/2)^I` acting on `I × ℤ/2` by translating the fibres. -/
def act (I : Type) : Multiplicative (I → ZMod 2) →* Equiv.Perm (I × ZMod 2) where
  toFun v :=
    { toFun := fun p => (p.1, p.2 + Multiplicative.toAdd v p.1)
      invFun := fun p => (p.1, p.2 - Multiplicative.toAdd v p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  map_one' := by
    ext p <;> simp
  map_mul' v w := by
    ext p
    · simp
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.coe_fn_mk, toAdd_mul,
        Pi.add_apply]
      ring

lemma act_injective (I : Type) : Function.Injective (act I) := by
  intro v w h
  have h2 : Multiplicative.toAdd v = Multiplicative.toAdd w := by
    funext i
    have h1 := congrArg (fun e : Equiv.Perm (I × ZMod 2) => (e (i, 0)).2) h
    simpa [act] using h1
  exact Multiplicative.toAdd.injective h2

/-- The graph of the linear map `𝔽₂^a → 𝔽₂^b` with matrix `M`. -/
def graph (a b : ℕ) (M : Fin a → Fin b → ZMod 2) :
    AddSubgroup (Fin a ⊕ Fin b → ZMod 2) where
  carrier := {u | ∀ j, u (Sum.inr j) = ∑ i, u (Sum.inl i) * M i j}
  zero_mem' := by
    intro j
    simp
  add_mem' := by
    intro u v hu hv j
    simp only [Pi.add_apply, hu j, hv j, add_mul, Finset.sum_add_distrib]
  neg_mem' := by
    intro u hu j
    simp only [Pi.neg_apply, hu j, neg_mul, Finset.sum_neg_distrib]

lemma graph_injective (a b : ℕ) : Function.Injective (graph a b) := by
  intro M M' h
  funext i j
  have hmem : (Sum.elim (Pi.single i (1 : ZMod 2)) (fun j => M i j) :
      Fin a ⊕ Fin b → ZMod 2) ∈ graph a b M := by
    intro j
    simp [Pi.single_apply]
  rw [h] at hmem
  have := hmem j
  simpa [Pi.single_apply] using this

lemma card_le (a b n : ℕ) (hab : 2 * (a + b) ≤ n) :
    2 ^ (a * b) ≤ Nat.card (Subgroup (Equiv.Perm (Fin n))) := by
  have hcard : Fintype.card ((Fin a ⊕ Fin b) × ZMod 2) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ext := Equiv.Perm.extendDomainHom (Equiv.ofInjective e e.injective)
  have hext : Function.Injective ext :=
    Equiv.Perm.extendDomainHom_injective (Equiv.ofInjective e e.injective)
  let Φ : (Fin a → Fin b → ZMod 2) → Subgroup (Equiv.Perm (Fin n)) := fun M =>
    Subgroup.map (ext.comp (act (Fin a ⊕ Fin b))) (AddSubgroup.toSubgroup (graph a b M))
  have hΦ : Function.Injective Φ := by
    intro M M' h
    have hinj : Function.Injective (ext.comp (act (Fin a ⊕ Fin b))) := by
      intro x y hxy
      exact act_injective _ (hext hxy)
    have h1 := Subgroup.map_injective hinj h
    exact graph_injective a b (AddSubgroup.toSubgroup.injective h1)
  have h2 := Nat.card_le_card_of_injective Φ hΦ
  have h3 : Nat.card (Fin a → Fin b → ZMod 2) = 2 ^ (a * b) := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ZMod.card]
    rw [← pow_mul, mul_comm]
  rw [h3] at h2
  exact h2

end OMA.E1162

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1.H1 := by
  intro n
  unfold Erdos1162.f
  apply OMA.E1162.card_le
  have h : n / 2 / 2 ≤ n / 2 := Nat.div_le_self _ _
  omega
