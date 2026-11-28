import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1.H1 := by
  intro X _ _ p q hcomm _ hdensity _ _
  have hpoint (x : X) : p (q x) = q (p x) :=
    congrArg (fun f : Equiv.Perm X => f x) hcomm.eq
  have hempty : {x : X | p (q x) ≠ q (p x)} = ∅ := by
    ext x
    simp [hpoint x]
  rw [hempty, Set.ncard_empty, Nat.mul_zero] at hdensity
  exact (Nat.not_le_of_gt Fintype.card_pos hdensity).elim