import OMAStatements.S_oeis_a163250
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: write n = m + 3 and use F(m+9) = F(m+8) + F(m+7). The truncated subtractions are
-- harmless because F(m+7) ≥ m^2+6m+13 (two-step induction), and the polynomial parts agree:
-- (m+2)^2 + (m+3)^2+4(m+3)+8 = (m+2)^2+4(m+2)+8 + (m+1)^2+4(m+1)+8 - (m+2)^2 ... checked by omega.

namespace OMA.A163250Proof

theorem lb : ∀ m : ℕ, m ^ 2 + 6 * m + 13 ≤ Nat.fib (m + 7) ∧
    (m + 1) ^ 2 + 6 * (m + 1) + 13 ≤ Nat.fib (m + 8)
  | 0 => by norm_num [Nat.fib_add_two]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := lb m
    refine ⟨h2, ?_⟩
    rw [show m + 1 + 8 = (m + 7) + 2 by ring, Nat.fib_add_two, show m + 7 + 1 = m + 8 by ring]
    nlinarith

end OMA.A163250Proof

open OMA.A163250Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a163250.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [OMA.S_oeis_a163250.a, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have h : Nat.fib (m + 3 + 6) = Nat.fib (m + 2 + 6) + Nat.fib (m + 1 + 6) := by
    rw [show m + 3 + 6 = (m + 7) + 2 by ring, Nat.fib_add_two]; ring_nf
  have b1 := (lb m).1
  have b2 := (lb (m + 1)).1
  rw [h]
  rw [show m + 1 + 6 = m + 7 by ring, show m + 2 + 6 = m + 1 + 7 by ring] at *
  generalize Nat.fib (m + 7) = A at *
  generalize Nat.fib (m + 1 + 7) = B at *
  have e1 : (m + 3) ^ 2 + 4 * (m + 3) + 8 = m ^ 2 + 10 * m + 29 := by ring
  have e2 : (m + 2) ^ 2 + 4 * (m + 2) + 8 = m ^ 2 + 8 * m + 20 := by ring
  have e3 : (m + 1) ^ 2 + 4 * (m + 1) + 8 = m ^ 2 + 6 * m + 13 := by ring
  have e4 : (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
  have e5 : (m + 1) ^ 2 + 6 * (m + 1) + 13 = m ^ 2 + 8 * m + 20 := by ring
  rw [e1, e2, e3, e4]
  rw [e5] at b2
  generalize m ^ 2 = s at *
  omega
