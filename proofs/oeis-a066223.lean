import OMAStatements.S_oeis_a066223
import Mathlib

-- Problem: oeis-a066223
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P066223
open OMA.S_oeis_a066223

theorem sol : type_of% @OMA.S_oeis_a066223.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  unfold a
  rw [show 2 * (m + 2) = (2 * m + 2) + 2 by ring, t, show 2 * m + 2 + 1 = (2 * m + 1) + 2 by ring, t,
    show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 = (2 * m) + 2 by ring, t]
  push_cast
  ring

end OMA.P066223

theorem OMA.solution : type_of% @OMA.S_oeis_a066223.main := OMA.P066223.sol
