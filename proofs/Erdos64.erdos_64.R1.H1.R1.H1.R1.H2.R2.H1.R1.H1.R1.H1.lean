import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1.H1 := by
  intro X _ _ p q hc _ hdens _ _
  exfalso
  have hempty : {x : X | p (q x) ≠ q (p x)} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact (congrArg (fun g : Equiv.Perm X => g x) hc.eq :)
  rw [hempty, Set.ncard_empty] at hdens
  have := Fintype.card_pos (α := X)
  omega
