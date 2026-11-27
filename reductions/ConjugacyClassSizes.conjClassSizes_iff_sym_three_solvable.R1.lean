import FormalConjectures.Paper.ConjugacyClassSizes

-- Reduction ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable.R1 of The $S_3$-conjecture (conjugacy classes of distinct sizes)
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1

open ConjugacyClassSizes ConjClasses Subgroup

-- Gow's restriction on the prime divisors of a finite solvable rational group.
def H1 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Group.IsSolvable G],
    (∀ (x : G) (n : ℕ), (Nat.card G).Coprime n → IsConj x (x ^ n)) →
    ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 ∨ p = 5

-- Order consequence of the classification of anti-homogeneous {2,3,5}-groups
-- (Zhou and Gorshkov, arXiv:2606.22244). Solvability is not assumed here.
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [Nontrivial G],
    (∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3 ∨ p = 5) →
    HasDistinctConjClassSizes G → Nat.card G = 6

lemma rational_of_distinct {G : Type*} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (x : G) (n : ℕ)
    (hn : (Nat.card G).Coprime n) : IsConj x (x ^ n) := by
  apply mk_eq_mk_iff_isConj.mp
  apply h
  apply Nat.card_congr
  apply (powCoprime hn).subtypeEquiv
  intro y
  change IsConj x y ↔ IsConj (x ^ n) (y ^ n)
  refine ⟨IsConj.pow n, ?_⟩
  intro hy
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  apply isConj_iff.mpr
  exact ⟨c, (powCoprime hn).injective (by change (c * x * c⁻¹) ^ n = y ^ n; rwa [conj_pow])⟩

lemma perm_three_of_card_six {G : Type} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (h6 : Nat.card G = 6) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [h6]; decide)
  let H := zpowers x
  have hc : Nat.card H = 2 := (Nat.card_zpowers x).trans hx
  have hcore : H.normalCore = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    by_contra hne
    have hz : a ∈ Subgroup.center G := by
      apply Subgroup.mem_center_iff.mpr
      intro b
      have hb : b * a * b⁻¹ ≠ 1 := by
        simpa [mul_inv_eq_one, mul_eq_left] using hne
      have hu := (Nat.card_eq_two_iff' (1 : H)).mp hc
      have he := hu.unique (y₁ := (⟨a,H.normalCore_le ha⟩ : H))
          (y₂ := (⟨b*a*b⁻¹,ha b⟩ : H)) (fun he => hne (congrArg Subtype.val he))
          (fun he => hb (congrArg Subtype.val he))
      have he' : a = b*a*b⁻¹ := congrArg Subtype.val he
      calc
        b*a = (b*a*b⁻¹)*b := by group
        _ = a*b := by rw [← he']
    rw [trivial_center_of_hasDistinctConjClassSizes h] at hz
    exact hne hz
  let f := MulAction.toPermHom G (G ⧸ H)
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp
    ((Subgroup.normalCore_eq_ker H).symm.trans hcore)
  have hd := H.index_mul_card
  rw [hc,h6] at hd
  have hcard : Nat.card (G ⧸ H) = 3 := by change H.index = 3; omega
  let e := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card] : Fintype.card (G ⧸ H) = 3)
  let g := e.permCongrHom.toMonoidHom.comp f
  apply Nonempty.intro (MulEquiv.ofBijective g ?_)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨e.permCongrHom.injective.comp hi, by rw [← Nat.card_eq_fintype_card, h6]; decide⟩

theorem main : H1 → H2 → type_of% @ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable := by
  intro h₁ h₂ G _ _ _ _ h
  exact perm_three_of_card_six h (h₂ G (h₁ G (rational_of_distinct h)) h)

end OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1
