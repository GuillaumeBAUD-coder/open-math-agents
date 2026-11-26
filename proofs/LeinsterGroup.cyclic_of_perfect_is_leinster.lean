import FormalConjectures.Wikipedia.LeinsterGroup

-- Problem: Leinster Groups — cyclic of perfect is leinster
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LeinsterGroup.lean:74 (declaration LeinsterGroup.cyclic_of_perfect_is_leinster)
-- Credit: @eitanteperman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

variable {G : Type*} [Group G] [Fintype G] [IsCyclic G]

/-- In a finite cyclic group, a subgroup is determined by its order. -/
lemma subgroup_eq_of_card_eq (H K : Subgroup G) (h : Nat.card H = Nat.card K) : H = K := by
  classical
  have key : ∀ L : Subgroup G, (L : Set G).toFinset =
      Finset.univ.filter (fun x : G => x ^ Nat.card L = 1) := by
    intro L
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Set.mem_toFinset] at hx
      have h1 := congrArg Subtype.val (pow_card_eq_one' (G := L) (x := ⟨x, hx⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
      simpa using h1
    · rw [← Nat.card_eq_card_toFinset]
      convert IsCyclic.card_pow_eq_one_le (α := G) (Nat.card_pos (α := L)) using 2
      exact SetLike.coe_sort_coe L
  have := key H
  rw [h, ← key K] at this
  exact SetLike.coe_injective (Set.toFinset_inj.1 this)

/-- In a finite cyclic group, every divisor of the order is the order of some subgroup. -/
lemma exists_subgroup_card {d : ℕ} (hd : d ∣ Fintype.card G) :
    ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  obtain ⟨k, hk⟩ := hd
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  refine ⟨Subgroup.zpowers (g ^ k), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow' g (by rintro rfl; simp at hk), hg,
    Nat.card_eq_fintype_card, hk]
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  rw [Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hk0]

omit [Fintype G] in
lemma normal (H : Subgroup G) : H.Normal := by
  let := IsCyclic.commGroup (α := G)
  exact ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

end OMA

theorem OMA.solution : type_of% @LeinsterGroup.cyclic_of_perfect_is_leinster := by
  intro G _ _ _ h_perfect
  classical
  unfold LeinsterGroup.IsLeinster
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [← (Nat.perfect_iff_sum_divisors_eq_two_mul hn).1 h_perfect]
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    rw [Nat.mem_divisors]
    refine ⟨?_, hn.ne'⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H _ K _ h
    exact Subtype.ext (OMA.subgroup_eq_of_card_eq H.1 K.1 h)
  · intro d hd
    obtain ⟨H, hH⟩ := OMA.exists_subgroup_card (Nat.dvd_of_mem_divisors hd)
    exact ⟨⟨H, OMA.normal H⟩, Finset.mem_univ _, hH⟩
  · intro H _
    rfl
