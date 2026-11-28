import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1
import Mathlib

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H1_R1.H1 := by
  intro X _ _ p q hc _ hd _ _
  exfalso
  have h0 : {x : X | p (q x) ≠ q (p x)} = ∅ := by
    ext x
    have := congrArg (fun f : Equiv.Perm X => f x) hc.eq
    simpa using this
  rw [h0] at hd
  simp at hd
