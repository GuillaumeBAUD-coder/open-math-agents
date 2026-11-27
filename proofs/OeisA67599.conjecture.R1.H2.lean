import OMAReductions.R_OeisA67599_conjecture_R1

/-! The encoding of a prime factorization appends each prime and then its multiplicity.
For 2401 times a prime greater than seven, these four entries are 7, 4, q, 1. -/

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hprime
  have hne : q ≠ 7 := by omega
  have hne' : 7 ≠ q := Ne.symm hne
  have hf : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    apply List.Perm.eq_of_pairwise' (Nat.primeFactorsList_sorted _).pairwise
    · simp [List.pairwise_cons, Nat.le_of_lt hq]
    · apply List.Perm.symm
      apply Nat.primeFactorsList_unique
      · simp [List.prod_cons]
        ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self_left] at hp
        rcases hp with rfl | rfl
        · decide
        · exact hprime
  have hlarge : ¬ 2401 * q < 2 := by omega
  simp [OeisA67599.a, hlarge, hf, List.dedup_cons_of_mem,
    List.dedup_cons_of_notMem, hne, hne', List.count_cons,
    OeisA67599.concatenateNats, List.foldl]
  ring
