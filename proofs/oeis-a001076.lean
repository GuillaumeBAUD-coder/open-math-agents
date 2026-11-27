import OMAStatements.S_oeis_a001076
import Mathlib

-- Problem: oeis-a001076
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P001076
open OMA.S_oeis_a001076

lemma key : ∀ n : ℕ, A001077 (n + 1) = 2 * A001076 (n + 1) + A001076 n ∧
    A001077 (n + 2) = 2 * A001076 (n + 2) + A001076 (n + 1)
  | 0 => by decide
  | n + 1 => by
    obtain ⟨h1, h2⟩ := key n
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 2 = (n + 1) + 2 by ring, A001077, A001076, show n + 1 + 1 = n + 2 by ring, h2, h1]
    rw [show n + 2 = n + 2 by rfl, A001076]
    ring

theorem sol : type_of% @OMA.S_oeis_a001076.main := by
  intro n
  rw [show n + 2 = n + 2 by rfl, A001076, (key n).1]
  push_cast
  ring

end OMA.P001076

theorem OMA.solution : type_of% @OMA.S_oeis_a001076.main := OMA.P001076.sol
