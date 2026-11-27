import OMAStatements.S_oeis_a343901
theorem OMA.solution : type_of% @OMA.S_oeis_a343901.main := by
  intro n hn
  refine (Set.ncard_pos ((Set.finite_Iic (n.totient + 1)).subset fun p hp => ?_)).2 ⟨2, Nat.prime_two, one_dvd _⟩
  have := Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) hp.2
  simp only [Set.mem_Iic]
  omega
