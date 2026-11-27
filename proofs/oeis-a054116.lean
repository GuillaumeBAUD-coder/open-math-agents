import OMAStatements.S_oeis_a054116
import Mathlib

-- Problem: oeis-a054116
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P054116
open OMA.S_oeis_a054116

lemma step (m : ℕ) (hm : 2 ≤ m) : a (m + 1) = a m + ((m + 1).factorial : ℤ) := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega), Finset.sum_Icc_succ_top (by omega)]

theorem sol : type_of% @OMA.S_oeis_a054116.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 = (m + 3) + 1 by omega, step (m + 3) (by omega), step (m + 2) (by omega)]
  rw [show m + 2 + 1 = m + 3 by omega, Nat.factorial_succ (m + 3), Nat.factorial_succ (m + 2)]
  push_cast
  ring

end OMA.P054116

theorem OMA.solution : type_of% @OMA.S_oeis_a054116.main := OMA.P054116.sol
