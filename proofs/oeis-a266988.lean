import OMAStatements.S_oeis_a266988

open OMA.S_oeis_a266988 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a266988.main := by
  intro p hp hlt
  by_contra h3
  have := Fact.mk hp
  have hs : ∀ g ∈ primRoots p, p - g ∈ primRoots p ∧ g ≤ p := by
    simp only [primRoots, mem_filter, mem_Icc]
    rintro g ⟨⟨h1, h2⟩, h⟩
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rcases hp.eq_two_or_odd with rfl | h4
    · rwa [ZMod.neg_eq_self_mod_two]
    obtain ⟨t, ht⟩ : ∃ t, p - 1 = 4 * t := ⟨(p - 1) / 4, by omega⟩
    have hx := IsPrimitiveRoot.orderOf (g : ZMod p)
    rw [h, ht] at hx
    rw [show -(g : ZMod p) = g ^ (2 * t + 1) by
      rw [pow_succ, (hx.pow (by omega) (by ring : 4 * t = 2 * t * 2)).eq_neg_one_of_two_right]; ring,
      Nat.Coprime.orderOf_pow, h]
    rw [h, ht, show 4 * t = 2 * (2 * t) by ring]
    exact .mul_left (Nat.coprime_two_left.2 (odd_two_mul_add_one t)) (by simp)
  have e : ∑ g ∈ primRoots p, (g : ℚ) = ∑ g ∈ primRoots p, ((p : ℚ) - g) :=
    sum_nbij' (p - ·) (p - ·) (fun g h => (hs g h).1) (fun g h => (hs g h).1)
      (fun g h => by have := (hs g h).2; omega) (fun g h => by have := (hs g h).2; omega)
      (fun g h => by push_cast [(hs g h).2]; ring)
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hu
  have hm : (u : ZMod p).val ∈ primRoots p := by
    simp only [primRoots, mem_filter, mem_Icc, ZMod.natCast_zmod_val, orderOf_units, hu, and_true]
    have := ZMod.val_lt (u : ZMod p)
    have := ZMod.val_pos.2 u.ne_zero
    omega
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at e
  rw [avg, div_lt_iff₀ (by exact_mod_cast card_pos.2 ⟨_, hm⟩)] at hlt
  linarith
