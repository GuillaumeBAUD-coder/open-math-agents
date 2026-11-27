import OMAStatements.S_oeis_a191993
import Mathlib

-- Problem: oeis-a191993
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P191993
open OMA.S_oeis_a191993

lemma cb (n : ℕ) : (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) / (n + 1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [eq_div_iff (by positivity)]
  have h' : ((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  linear_combination h'

theorem sol : type_of% @OMA.S_oeis_a191993.main := by
  intro t
  simp only
  unfold a
  simp only [show t + 3 - 1 = t + 2 by omega, show t + 2 - 1 = t + 1 by omega, show t + 1 - 1 = t by omega]
  rw [show t + 3 = (t + 2) + 1 by ring, cb (t + 2), show t + 2 = (t + 1) + 1 by ring, cb (t + 1)]
  push_cast
  field_simp
  ring

end OMA.P191993

theorem OMA.solution : type_of% @OMA.S_oeis_a191993.main := OMA.P191993.sol
