import OMAReductions.R_oeis_a088112_R1
import Mathlib

theorem OMA.solution : OMA.R_oeis_a088112_R1.H1 := by
  have h : OMA.S_oeis_a088112.rev (4 ^ 2) = 61 := by
    first
      | (norm_num [OMA.S_oeis_a088112.rev, Nat.ofDigits]; done)
      | (simp [OMA.S_oeis_a088112.rev, Nat.ofDigits]; done)
      | decide
  refine ⟨4, by norm_num, ?_⟩
  rw [h]
  norm_num
