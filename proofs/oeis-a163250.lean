import OMAStatements.S_oeis_a163250
import Mathlib

/-!
# A163250

With `a n = fib (n+6) - (n^2 + 4n + 8)` in the naturals, the Fibonacci part never truncates
(both terms stay below `fib (n+6)`, by a two-step induction), so the recurrence for `fib` and
the telescoping of the quadratic give the conjecture.
-/

namespace A163250

/-- Two-step lower bound: the quadratic stays below `fib (n+6)` and `fib (n+7)`. -/
theorem fib_ge_sq (n : Nat) :
    n ^ 2 + 4 * n + 8 <= Nat.fib (n + 6) /\ (n + 1) ^ 2 + 4 * (n + 1) + 8 <= Nat.fib (n + 7) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by simpa using h2, ?_⟩
    have hfib : Nat.fib (n + 1 + 7) = Nat.fib (n + 6) + Nat.fib (n + 7) := by
      rw [show n + 1 + 7 = n + 6 + 2 by ring, Nat.fib_add_two, show n + 6 + 1 = n + 7 by ring]
    rw [hfib]
    nlinarith

end A163250

theorem OMA.solution : type_of% @OMA.S_oeis_a163250.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have b3 : (m + 3) ^ 2 + 4 * (m + 3) + 8 <= Nat.fib (m + 3 + 6) := (A163250.fib_ge_sq (m + 3)).1
  have b2 : (m + 2) ^ 2 + 4 * (m + 2) + 8 <= Nat.fib (m + 2 + 6) := (A163250.fib_ge_sq (m + 2)).1
  have b1 : (m + 1) ^ 2 + 4 * (m + 1) + 8 <= Nat.fib (m + 1 + 6) := (A163250.fib_ge_sq (m + 1)).1
  have hf : Nat.fib (m + 3 + 6) = Nat.fib (m + 2 + 6) + Nat.fib (m + 1 + 6) := by
    rw [show m + 3 + 6 = m + 7 + 2 by ring, Nat.fib_add_two,
      show m + 7 = m + 1 + 6 by ring, show m + 7 + 1 = m + 2 + 6 by ring]
    ring
  unfold OMA.S_oeis_a163250.a
  zify [b1, b2, b3]
  rw [hf]
  push_cast
  ring
