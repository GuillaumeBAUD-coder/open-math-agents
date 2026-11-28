import OMAStatements.S_oeis_a214123

lemma L {n p} (hp : p.Prime) (h : n + 1 * (n - 1) = p) : OMA.S_oeis_a214123.a n = 1 :=
  le_antisymm (Nat.sInf_le ⟨one_pos, h ▸ hp⟩) (le_csInf ⟨1, one_pos, h ▸ hp⟩ fun _ h => h.1)

theorem OMA.solution : type_of% @OMA.S_oeis_a214123.main :=
  ⟨fun _ _ hp => L hp (by omega), fun _ hp _ => L hp (by have := hp.eq_two_or_odd; omega),
    fun h => Set.infinite_of_forall_exists_gt fun N => by
      obtain ⟨p, ⟨hp, hq⟩, _⟩ := h.exists_gt (2 * N + 3)
      have := hp.eq_two_or_odd
      exact ⟨(p + 1) / 2, ⟨by omega, L hp (by omega), L hq (by omega)⟩, by omega⟩⟩
