import OMAStatements.S_oeis_a217447
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: write a(k+3) with explicit factorial sums, peel the sums with sum_range_succ down to
-- common base sums, expand factorials; the recurrence then holds by ring (n = 7 by decide). No computer search.

namespace OMA.A217447Proof

open OMA.S_oeis_a217447
open scoped BigOperators

theorem a3 (k : ℕ) : a (k + 3) = 4 * (∑ i ∈ Finset.range (k + 1), ((i+1).factorial : ℤ))
    - 2 * ((k : ℤ) + 1) * (∑ i ∈ Finset.range k, (i.factorial : ℤ))
    + 2 * (∑ i ∈ Finset.range k, ((i+1).factorial : ℤ)) + 2 := by
  unfold a
  rw [show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  push_cast; ring

theorem mainP : ∀ n : ℕ, 7 ≤ n →
    2*a n + 2*(-(n : ℤ)-1)*a (n-1) + (6*(n : ℤ)-11)*a (n-2) +
    (-5*(n : ℤ)+14)*a (n-3) + 3*a (n-4) + ((n : ℤ)-6)*a (n-5) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rcases m with _ | j
  · decide
  · rw [show j + 1 + 7 - 1 = (j + 4) + 3 by omega, show j + 1 + 7 - 2 = (j + 3) + 3 by omega,
      show j + 1 + 7 - 3 = (j + 2) + 3 by omega, show j + 1 + 7 - 4 = (j + 1) + 3 by omega,
      show j + 1 + 7 - 5 = j + 3 by omega, show j + 1 + 7 = (j + 5) + 3 by omega]
    simp only [a3, Finset.sum_range_succ, Nat.factorial_succ]
    push_cast
    ring

end OMA.A217447Proof

open OMA.A217447Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a217447.main := mainP
