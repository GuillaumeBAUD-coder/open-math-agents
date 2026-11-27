import OMAReductions.R_OeisA67599_conjecture_R1

/-! # Decimal encoding of four sevens and a larger prime -/

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have hle : 7 ≤ q := hq.le
  have hne : 7 ≠ q := hq.ne
  have hprod : 2 ≤ 2401 * q := by omega
  have hfactors : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    apply List.Perm.eq_of_sortedLE (Nat.primeFactorsList_sorted _)
    · rw [List.sortedLE_iff_pairwise]
      simp [hle]
    · symm
      apply Nat.primeFactorsList_unique
      · simp
        ring
      · intro p hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl
        all_goals first | exact hp | decide
  unfold OeisA67599.a
  rw [if_neg (not_lt_of_ge hprod), hfactors]
  simp [List.count_cons, hne, hne.symm, OeisA67599.concatenateNats]
  ring
