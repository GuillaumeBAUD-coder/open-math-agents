import OMAStatements.S_oeis_a182959
import Mathlib

-- Problem: oeis-a182959
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P182959
open OMA.S_oeis_a182959

lemma cb (n : ℕ) : (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) / (n + 1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [eq_div_iff (by positivity)]
  have h' : ((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  linear_combination h'

theorem sol : type_of% @OMA.S_oeis_a182959.main := by
  refine ⟨4, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = (m + 1) + 2 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 = (m + 2) + 2 by omega]
  simp only [a]
  rw [show m + 2 + 1 = (m + 2) + 1 by rfl, cb (m + 2), show m + 1 + 1 = m + 2 by ring, cb (m + 1)]
  push_cast
  field_simp
  ring

end OMA.P182959

theorem OMA.solution : type_of% @OMA.S_oeis_a182959.main := OMA.P182959.sol
