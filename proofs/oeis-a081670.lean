import OMAStatements.S_oeis_a081670
import Mathlib

-- Problem: oeis-a081670
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P081670
open OMA.S_oeis_a081670

lemma cb (n : ℕ) : (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) / (n + 1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [eq_div_iff (by positivity)]
  have h' : ((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n + 1) : ℚ) = 2 * (2 * n + 1) * (Nat.centralBinom n : ℚ) := by
    exact_mod_cast h
  push_cast at h'
  linear_combination h'

theorem sol : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [← Int.cast_inj (α := ℚ)]
  unfold a
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  push_cast
  try simp only [← Nat.centralBinom_eq_two_mul_choose]
  rw [show m + 3 = (m + 2) + 1 by ring, cb (m + 2), show m + 2 = (m + 1) + 1 by ring, cb (m + 1),
    show m + 1 = m + 1 by rfl, cb m]
  push_cast
  field_simp
  ring

end OMA.P081670

theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := OMA.P081670.sol
