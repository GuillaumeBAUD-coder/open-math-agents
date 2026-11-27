import OMAStatements.S_oeis_a111883
import Mathlib

-- Problem: oeis-a111883
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P111883
open OMA.S_oeis_a111883

theorem sol : type_of% @OMA.S_oeis_a111883.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  unfold a
  rw [show m + 3 = (m + 1) + 2 by ring, involutions, show m + 2 = m + 2 by rfl, involutions]
  push_cast
  ring

end OMA.P111883

theorem OMA.solution : type_of% @OMA.S_oeis_a111883.main := OMA.P111883.sol
