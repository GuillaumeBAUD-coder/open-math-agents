import OMAStatements.S_oeis_a214615

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write n = k + 2; by the defining recurrence of the Meixner polynomials,
-- M (k+2) = X * M (k+1) - (k+1)^2 * M k, so evaluating at 1 gives
-- a (k+2) = a (k+1) - (k+1)^2 * a k, which is the claimed relation. No computer search.

namespace OMA.P_oeis_a214615

open OMA.S_oeis_a214615 Polynomial

theorem rec_step (k : ℕ) :
    a (k + 2) = a (k + 1) - ((k : ℤ) + 1) ^ 2 * a k := by
  simp [a, meixner, eval_sub, eval_mul, eval_X]

theorem solution : ∀ n : ℕ, 2 ≤ n →
    a n - a (n - 1) + ((n : ℤ) - 1) ^ 2 * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h1 : k + 2 - 1 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  rw [h1, h2, rec_step k]
  push_cast
  ring

end OMA.P_oeis_a214615

theorem OMA.solution : type_of% @OMA.S_oeis_a214615.main := OMA.P_oeis_a214615.solution
