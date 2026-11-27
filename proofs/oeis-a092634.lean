import OMAStatements.S_oeis_a092634
import Mathlib

-- Problem: oeis-a092634
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P092634
open OMA.S_oeis_a092634

lemma step (k : ℕ) (hk : 1 ≤ k) :
    a (k + 1) = a k - ((k + 1 : ℕ) : ℤ) * ((k + 1).factorial : ℤ) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem sol : type_of% @OMA.S_oeis_a092634.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = (m + 3) + 1 by omega, show m + 5 - 2 = (m + 2) + 1 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 = ((m + 3) + 1) + 1 by omega,
    step ((m + 3) + 1) (by omega), step (m + 3) (by omega), step (m + 2) (by omega)]
  rw [show m + 3 + 1 + 1 = (m + 4) + 1 by omega, Nat.factorial_succ (m + 4),
    show m + 3 + 1 = (m + 3) + 1 by omega, Nat.factorial_succ (m + 3),
    show m + 2 + 1 = m + 3 by omega, Nat.factorial_succ (m + 2)]
  push_cast
  ring

end OMA.P092634

theorem OMA.solution : type_of% @OMA.S_oeis_a092634.main := OMA.P092634.sol
