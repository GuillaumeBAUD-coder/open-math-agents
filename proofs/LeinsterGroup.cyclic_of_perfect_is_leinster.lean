import FormalConjectures.Wikipedia.LeinsterGroup

-- Problem: Leinster Groups — cyclic of perfect is leinster
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LeinsterGroup.lean:74 (declaration LeinsterGroup.cyclic_of_perfect_is_leinster)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped IsMulCommutative

namespace OMA.P6

theorem subset_pow_eq_one {G : Type*} [Group G] (H : Subgroup G) [Finite H] :
    ((H : Set G)) ⊆ {a : G | a ^ Nat.card H = 1} := by
  intro x hx
  show x ^ Nat.card H = 1
  have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h1

theorem card_pow_set_le {G : Type*} [Group G] [Fintype G] [IsCyclic G] {n : ℕ} (hn : 0 < n) :
    Set.ncard {a : G | a ^ n = 1} ≤ n := by
  classical
  have e : {a : G | a ^ n = 1} = ↑(Finset.univ.filter (fun a : G => a ^ n = 1)) := by
    ext a
    simp
  rw [e, Set.ncard_coe_finset]
  exact IsCyclic.card_pow_eq_one_le hn

theorem eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G] (H K : Subgroup G)
    (h : Nat.card H = Nat.card K) : H = K := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hS : ∀ L : Subgroup G, Nat.card L = Nat.card H →
      (L : Set G) = {a : G | a ^ Nat.card H = 1} := by
    intro L hL
    have hsub : (L : Set G) ⊆ {a : G | a ^ Nat.card H = 1} := by
      rw [← hL]
      exact subset_pow_eq_one L
    apply Set.eq_of_subset_of_ncard_le hsub
    have e : (L : Set G).ncard = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
    rw [e, hL]
    exact card_pow_set_le hpos
  apply SetLike.coe_injective
  rw [hS H rfl, hS K h.symm]

end OMA.P6

theorem OMA.solution : type_of% @LeinsterGroup.cyclic_of_perfect_is_leinster := by
  intro G _ _ _ hp
  classical
  obtain ⟨hsum, hpos⟩ : (∑ i ∈ Nat.properDivisors (Fintype.card G), i = Fintype.card G) ∧
      0 < Fintype.card G := hp
  have hdiv : ∑ i ∈ Nat.divisors (Fintype.card G), i = 2 * Fintype.card G := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, hsum]
    omega
  unfold LeinsterGroup.IsLeinster
  rw [← hdiv]
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    refine Nat.mem_divisors.2 ⟨?_, hpos.ne'⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H₁ _ H₂ _ h
    exact Subtype.ext (OMA.P6.eq_of_card_eq H₁.1 H₂.1 h)
  · intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.1 hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hpos
    have htot : 0 < Nat.totient d := Nat.totient_pos.2 hdpos
    have hcard := IsCyclic.card_orderOf_eq_totient hdvd
    have hne : 0 < (Finset.univ.filter (fun a : G => orderOf a = d)).card := by
      rw [hcard]
      exact htot
    obtain ⟨a, ha⟩ := Finset.card_pos.1 hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hnorm : (Subgroup.zpowers a).Normal := inferInstance
    refine ⟨⟨Subgroup.zpowers a, hnorm⟩, Finset.mem_univ _, ?_⟩
    show Nat.card (Subgroup.zpowers a) = d
    rw [Nat.card_zpowers, ha]
  · intro H _
    rfl
