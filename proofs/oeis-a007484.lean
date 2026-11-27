import OMAStatements.S_oeis_a007484
import Mathlib

-- Problem: oeis-a007484
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P007484
open OMA.S_oeis_a007484

lemma key : ∀ n : ℕ, 8 * a n = b (n + 2) + c (n + 1) ∧ 8 * a (n + 1) = b (n + 3) + c (n + 2)
  | 0 => by decide
  | n + 1 => by
    obtain ⟨h1, h2⟩ := key n
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 1 = n + 2 by ring, a, show n + 1 + 3 = (n + 2) + 2 by ring, b,
      show n + 1 + 2 = (n + 1) + 2 by ring, c]
    rw [show n + 2 + 1 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at *
    omega

theorem sol : type_of% @OMA.S_oeis_a007484.main := fun n => (key n).1

end OMA.P007484

theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := OMA.P007484.sol
