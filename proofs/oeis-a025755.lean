import OMAStatements.S_oeis_a025755
import Mathlib

-- Problem: oeis-a025755
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P025755
open OMA.S_oeis_a025755

theorem sol : type_of% @OMA.S_oeis_a025755.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 = (m + 1) + 1 by ring]
  simp only [a]
  rw [ascPochhammer_succ_eval, Nat.factorial_succ (m + 1), pow_succ]
  have h : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.P025755

theorem OMA.solution : type_of% @OMA.S_oeis_a025755.main := OMA.P025755.sol
