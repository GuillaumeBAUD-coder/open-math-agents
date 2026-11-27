import FormalConjectures.Kourovka.«19_25»

-- The witnesses and their numerical invariants are from van Doorn, Judin,
-- Monticone and Morrison, Theorem 4.1 (arXiv:2607.17477).
namespace OMA.R_Kourovka_19_25_kourovka_19_25_R1

def H1 : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G), IsSimpleGroup G ∧
    Fintype.card G = 6048 ∧ ∑ g : G, Nat.totient (orderOf g) = 23984

def H2 : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Fintype K), Fintype.card K = 42 ∧
    ∑ h : Multiplicative (ZMod 6) × Equiv.Perm (Fin 4) × K, Nat.totient (orderOf h) = 23984

lemma not_simple_product (K : Type) [Group K] :
    ¬ IsSimpleGroup (Multiplicative (ZMod 6) × Equiv.Perm (Fin 4) × K) := by
  intro hsH
  let H := Multiplicative (ZMod 6) × Equiv.Perm (Fin 4) × K
  let π : H →* Multiplicative (ZMod 6) := MonoidHom.fst _ _
  rcases hsH.eq_bot_or_eq_top_of_normal π.ker inferInstance with h | h
  · let e : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    have hm : ((1, e, 1) : H) ∈ π.ker := rfl
    rw [h, Subgroup.mem_bot] at hm
    have he := congrArg (fun x : H => x.2.1 0) hm
    change e 0 = 0 at he
    simp [e] at he
  · have hm : ((Multiplicative.ofAdd (1 : ZMod 6), 1, 1) : H) ∈ π.ker := by rw [h]; trivial
    change (1 : ZMod 6) = 0 at hm
    exact (by decide : (1 : ZMod 6) ≠ 0) hm

theorem main : H1 → H2 → type_of% @Kourovka.«19.25».kourovka_19_25 := by
  rintro ⟨G, gG, fG, hs, hc, ht⟩ ⟨K, gK, fK, hk, hu⟩ hall
  letI : Group K := gK
  letI : Group G := gG
  letI : Fintype K := fK
  letI : Fintype G := fG
  have hcH : Fintype.card (Multiplicative (ZMod 6) × Equiv.Perm (Fin 4) × K) = 6048 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_multiplicative, ZMod.card, Fintype.card_perm, Fintype.card_fin, hk]
    decide
  exact not_simple_product K (hall G _ (hc.trans hcH.symm) (ht.trans hu.symm) hs)

end OMA.R_Kourovka_19_25_kourovka_19_25_R1
