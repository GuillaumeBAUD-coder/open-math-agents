import OMAStatements.S_oeis_a076771

theorem OMA.solution : type_of% @OMA.S_oeis_a076771.main := by
  rintro ⟨N, h⟩
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes (N+1)
  obtain ⟨a,b,ha,-,hc,-,hb,-,hab,hs⟩ := h (2*p) (by omega) ⟨p, by omega⟩
  exact hab (Nat.coprime_self_add_right.1 (hs ▸ ha.coprime_two_right.mul_right (hp.coprime_iff_not_dvd.2 fun hd => hc (Nat.eq_of_dvd_of_lt_two_mul ha.pos.ne' hd (by omega) ▸ hp)).symm))
