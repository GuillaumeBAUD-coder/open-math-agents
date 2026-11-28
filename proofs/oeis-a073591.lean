import OMAStatements.S_oeis_a073591

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: b(n) = A000522(n) satisfies b(n+1) = (n+1) b(n) + 1, since (n+1)!/k! = (n+1) (n!/k!)
-- for k <= n. With a = b + 1 the four-term recurrence is a linear combination of three such steps.

open OMA.S_oeis_a073591

namespace P_oeis_a073591

lemma b_succ (n : ℕ) : A000522 (n + 1) = (n + 1) * A000522 n + 1 := by
  unfold A000522
  rw [Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos _), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hk')]

lemma a_succ (n : ℕ) : a (n + 1) = ((n : ℤ) + 1) * a n - n + 1 := by
  unfold a
  rw [b_succ]
  push_cast
  ring

theorem main_proved : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 2) * a (n - 1) + (2 * (n : ℤ) - 1) * a (n - 2) +
      (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have h0 := a_succ m
  have h1 := a_succ (m + 1)
  have h2 := a_succ (m + 2)
  push_cast at h0 h1 h2 ⊢
  linear_combination h2 - 2 * h1 + h0

end P_oeis_a073591

theorem OMA.solution : type_of% @OMA.S_oeis_a073591.main := P_oeis_a073591.main_proved
