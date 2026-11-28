import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2

-- Credit: first proof by @xlh1551; shorter proof by @conormcfarland

/-! `f b k x` checks that the Collatz orbit of `x` drops below `b` within `k` steps. The kernel
evaluates it for every start in [1000, 10000), as a 90 × 100 grid, with cutoff 132. -/

open CollatzConjecture

def f (b : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (x < b)
  | k + 1, x => decide (x < b) || f b k (collatzStep x)

theorem f_ok (b k x) (h : f b k x) : ∃ i, collatzStep^[i] x < b := by
  induction k generalizing x with
  | zero => exact ⟨0, of_decide_eq_true h⟩
  | succ k ih =>
    simp only [f, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := ih _ h
      exact ⟨i + 1, hi⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem rows : (List.range 90).all fun q =>
    (List.range 100).all fun r => f (1000 + 100 * q + r) 132 (1000 + 100 * q + r) := by
  decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2.H1 := by
  intro n h1 h2 _
  have := List.all_eq_true.mp (List.all_eq_true.mp rows ((n - 1000) / 100)
    (List.mem_range.2 (by omega))) ((n - 1000) % 100) (List.mem_range.2 (by omega))
  rw [show 1000 + 100 * ((n - 1000) / 100) + (n - 1000) % 100 = n by omega] at this
  exact f_ok _ _ _ this
