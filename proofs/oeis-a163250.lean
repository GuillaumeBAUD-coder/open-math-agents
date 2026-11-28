import OMAStatements.S_oeis_a163250
import Mathlib

/-!
# A163250: the conjectured recurrence

Since F(n+6) ≥ n² + 4n + 8 for every n (two-step induction), the natural subtraction in a(n) never
truncates. Using F(n+6) = F(n+5) + F(n+4),
a(n) − a(n−1) − a(n−2) = −(n² + 4n + 8) + ((n−1)² + 4(n−1) + 8) + ((n−2)² + 4(n−2) + 8) = (n − 1)².
-/


namespace PA163250

theorem fib_bound (n : ℕ) :
    n ^ 2 + 4 * n + 8 ≤ Nat.fib (n + 6) ∧ (n + 1) ^ 2 + 4 * (n + 1) + 8 ≤ Nat.fib (n + 7) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 7 = (n + 6) + 2 by ring, Nat.fib_add_two, show n + 6 + 1 = n + 7 by ring]
    nlinarith

end PA163250

theorem OMA.solution : type_of% @OMA.S_oeis_a163250.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  unfold OMA.S_oeis_a163250.a
  have b3 := (PA163250.fib_bound (m + 3)).1
  have b2 := (PA163250.fib_bound (m + 2)).1
  have b1 := (PA163250.fib_bound (m + 1)).1
  have hf : Nat.fib (m + 3 + 6) = Nat.fib (m + 1 + 6) + Nat.fib (m + 2 + 6) := by
    rw [show m + 3 + 6 = (m + 1 + 6) + 2 by ring, Nat.fib_add_two]
  zify [b3, b2, b1]
  rw [hf]
  push_cast
  ring
