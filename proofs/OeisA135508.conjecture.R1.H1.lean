import OMAReductions.R_OeisA135508_conjecture_R1

-- Step OeisA135508.conjecture.R1.H1: hypothesis H1 of reduction OeisA135508.conjecture.R1
-- Credit: @JamesSlash
-- H1 := ∀ n : ℕ, 4 ≤ n → 3 ∣ x n
--
-- Proof: x (n + 1) = 2 * x n + lcm (x n) (n + 1) is a multiple of x n for n ≥ 1,
-- so x 4 = 60 divides every later term, and 3 divides 60.

namespace OMA.OeisA135508H1

open OeisA135508

theorem x_dvd_succ (n : ℕ) (hn : 1 ≤ n) : x n ∣ x (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  change x (k + 1) ∣ 2 * x (k + 1) + Nat.lcm (x (k + 1)) (k + 1 + 1)
  exact dvd_add (dvd_mul_left _ _) (Nat.dvd_lcm_left _ _)

theorem x_four : x 4 = 60 := by decide

theorem three_dvd (n : ℕ) (hn : 4 ≤ n) : 3 ∣ x n := by
  induction n, hn using Nat.le_induction with
  | base => rw [x_four]; norm_num
  | succ n hn ih => exact ih.trans (x_dvd_succ n (by omega))

end OMA.OeisA135508H1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  exact OMA.OeisA135508H1.three_dvd n hn
