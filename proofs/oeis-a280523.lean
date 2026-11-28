import OMAStatements.S_oeis_a280523
import Mathlib

namespace OMA.S_oeis_a280523

private theorem shifted_fib (n : ℕ) :
    b n = (Nat.fib (n + 3) : ℤ) - ((n + 3) / 2 : ℕ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        change b (n + 2) = (Nat.fib (n + 5) : ℤ) - ((n + 5) / 2 : ℕ)
        rw [b, ih (n + 1) (by omega), ih n (by omega),
          Nat.fib_add_two (n := n + 3), Nat.cast_add,
          show n + 1 + 3 = n + 3 + 1 by omega]
        omega

end OMA.S_oeis_a280523

theorem OMA.solution : type_of% @OMA.S_oeis_a280523.main := by
  intro n hn
  rw [OMA.S_oeis_a280523.a, OMA.S_oeis_a280523.shifted_fib]
  have hIndex : 2 * n - 2 + 3 = 2 * n + 1 := by omega
  rw [hIndex]
  have hHalf : (2 * n + 1) / 2 = n := by omega
  rw [hHalf]