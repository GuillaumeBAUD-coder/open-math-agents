import OMAStatements.S_oeis_a111942
import Mathlib

open OMA.S_oeis_a111942

namespace P111942

theorem a_odd (j : ℕ) : a (2 * j + 1) = ((j.factorial : ℤ)) ^ 2 := by
  rw [a, if_neg (by omega), show 2 * j + 1 - 1 = 2 * j by omega, show 2 * j / 2 = j by omega,
    show (2 * j + 1) / 2 = j by omega, pow_mul]
  norm_num
  ring

theorem a_even (j : ℕ) : a (2 * j + 2) = -((j.factorial : ℤ) * ((j + 1).factorial : ℤ)) := by
  rw [a, if_neg (by omega), show 2 * j + 2 - 1 = 2 * j + 1 by omega, show (2 * j + 1) / 2 = j by omega,
    show (2 * j + 2) / 2 = j + 1 by omega, pow_succ, pow_mul]
  norm_num

end P111942

open P111942 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111942.main := by
  intro n hn
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 3 ∨ n = 2 * j + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * j + 3 - 1 = 2 * j + 2 by omega, show 2 * j + 3 - 2 = 2 * j + 1 by omega,
      show 2 * j + 3 = 2 * (j + 1) + 1 by ring, a_odd, a_even, a_odd, Nat.factorial_succ]
    push_cast
    ring
  · rw [show 2 * j + 4 - 1 = 2 * (j + 1) + 1 by omega, show 2 * j + 4 - 2 = 2 * j + 2 by omega,
      show 2 * j + 4 = 2 * (j + 1) + 2 by ring, a_odd, a_even, a_even, Nat.factorial_succ (j + 1),
      Nat.factorial_succ j]
    push_cast
    ring
