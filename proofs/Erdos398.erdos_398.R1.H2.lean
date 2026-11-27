import OMAReductions.R_Erdos398_erdos_398_R1

-- Step Erdos398.erdos_398.R1.H2
-- Credit: @caa1982

private def checkRow (n : ℕ) : Bool :=
  decide (Nat.sqrt (n.factorial + 1) ^ 2 = n.factorial + 1) == (n == 4 || n == 5 || n == 7)

private lemma hcheck128 : (List.range 128).all checkRow = true := by decide +kernel

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H2 := by
  intro n hn
  have hrow : checkRow n = true :=
    List.all_eq_true.mp hcheck128 n (List.mem_range.mpr hn)
  have hiff : Nat.sqrt (n.factorial + 1) ^ 2 = n.factorial + 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 := by
    simp only [checkRow, beq_iff_eq] at hrow
    constructor
    · intro h
      have h1 : decide (Nat.sqrt (n.factorial + 1) ^ 2 = n.factorial + 1) = true := decide_eq_true h
      rw [hrow] at h1
      simpa [Bool.or_eq_true, or_assoc] using h1
    · intro h
      refine of_decide_eq_true ?_
      rw [hrow]
      simpa [Bool.or_eq_true, or_assoc] using h
  have hsq : (∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔ Nat.sqrt (n.factorial + 1) ^ 2 = n.factorial + 1 := by
    constructor
    · rintro ⟨m, hm⟩
      rw [hm, Nat.sqrt_eq']
    · intro h
      exact ⟨Nat.sqrt (n.factorial + 1), h.symm⟩
  rw [hsq, hiff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
