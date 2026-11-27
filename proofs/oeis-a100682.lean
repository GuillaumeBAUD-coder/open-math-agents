import OMAStatements.S_oeis_a100682
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a100682.main) := by
  intro h
  have h2 := h 2 (by decide)
  have e1 : OMA.S_oeis_a100682.estimate 2 = 0 := by
    simp [OMA.S_oeis_a100682.estimate, OMA.S_oeis_a100682.fourthRoot]
  have e2 : OMA.S_oeis_a100682.pentatope 2 = 5 := by
    simp [OMA.S_oeis_a100682.pentatope]
  rw [e1, e2] at h2
  unfold OMA.S_oeis_a100682.fourthRoot at h2
  rw [Nat.sqrt_eq_zero, Nat.sqrt_eq_zero] at h2
  omega
