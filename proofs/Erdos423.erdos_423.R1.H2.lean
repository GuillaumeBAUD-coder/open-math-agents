import OMAReductions.R_Erdos423_erdos_423_R1
import Mathlib.Tactic

-- Step Erdos423.erdos_423.R1.H2: hypothesis H2 of reduction Erdos423.erdos_423.R1
-- Credit: @keiichisince1986-bot
-- Prove that for any Hofstadter sequence a, the gap a n - n is nondecreasing for 1 ≤ n ≤ m.

theorem OMA.solution : OMA.R_Erdos423_erdos_423_R1.H2 := by
  intro a ⟨ha1, ha2, hk⟩ n m hn hnm
  have step : ∀ k, 1 ≤ k → a k + 1 ≤ a (k + 1) := by
    intro k hk1
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      rw [ha1, ha2]
    · simpa using (hk (k + 1) (by omega)).2.1
  have ge : ∀ k, 1 ≤ k → k ≤ a k := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => omega
    | succ j hj ih =>
      have h1 := step j hj
      omega
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    have h1 := step j (le_trans hn hj)
    have h2 := ge j (le_trans hn hj)
    omega
