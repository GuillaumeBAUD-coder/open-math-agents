import OMAReductions.R_OeisA135508_conjecture_R1

/-! # Divisibility by three from the fourth term on

Each term of the recurrence divides the next one, and `x 4 = 60` is divisible by `3`.
Hence every later term is divisible by `3`. -/
-- Credit: @amarkowski999

open OeisA135508

namespace OMA.R_OeisA135508_conjecture_R1

/-- From index four onward, `x 4` divides `x n`. -/
lemma x_four_dvd (n : ℕ) (hn : 4 ≤ n) : x 4 ∣ x n := by
  induction n, hn using Nat.le_induction with
  | base => exact dvd_refl _
  | succ k hk ih => exact ih.trans (x_dvd_succ k (by omega))

end OMA.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  have h4 : (3 : ℕ) ∣ x 4 := by decide
  exact h4.trans (OMA.R_OeisA135508_conjecture_R1.x_four_dvd n hn)
