import OMAStatements.S_oeis_a081670

namespace OMA.P_oeis_a081670
open OMA.S_oeis_a081670

lemma cb (k : ℕ) : ((k : ℤ) + 1) * (Nat.centralBinom (k + 1) : ℤ) =
    2 * (2 * (k : ℤ) + 1) * (Nat.centralBinom k : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

end OMA.P_oeis_a081670

theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [OMA.S_oeis_a081670.a]
  have e1 := OMA.P_oeis_a081670.cb m
  have e2 := OMA.P_oeis_a081670.cb (m + 1)
  have e3 := OMA.P_oeis_a081670.cb (m + 2)
  push_cast at e1 e2 e3 ⊢
  linear_combination (3 * (m : ℤ) ^ 2 + m + 2) * e3 + (-12 * (m : ℤ) ^ 2 - 16 * m - 8) * e2 +
    (9 * (m : ℤ) ^ 2 + 21 * m + 18) * e1
