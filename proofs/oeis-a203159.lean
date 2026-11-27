import OMAStatements.S_oeis_a203159
import Mathlib

-- Problem: oeis-a203159
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P203159
open OMA.S_oeis_a203159

lemma ps (n : ℕ) : products (n + 1) = ((products n).1 * (2 * ((n : ℤ) + 1)),
    (products n).2 * (2 * ((n : ℤ) + 1)) + (products n).1) := rfl

theorem sol : type_of% @OMA.S_oeis_a203159.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = (m + 1) + 1 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 = ((m + 1) + 1) + 1 by omega]
  unfold a
  simp only [ps]
  push_cast
  ring

end OMA.P203159

theorem OMA.solution : type_of% @OMA.S_oeis_a203159.main := OMA.P203159.sol
