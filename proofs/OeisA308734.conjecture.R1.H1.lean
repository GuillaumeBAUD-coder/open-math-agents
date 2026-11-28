import OMAReductions.R_OeisA308734_conjecture_R1

/-!
The Fermat-Euler two-square theorem (Mathlib, Nat.eq_sq_add_sq_iff) turns
the prime-factor criterion on the residual into two squares x^2 + y^2.
-/

theorem OMA.solution : OMA.R_OeisA308734_conjecture_R1.H1 := by
  intro n a b c d hle hcrit
  obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_iff.mpr hcrit
  exact ⟨a, b, c, d, x, y, by omega⟩
