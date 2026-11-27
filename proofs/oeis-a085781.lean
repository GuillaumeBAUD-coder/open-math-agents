import OMAStatements.S_oeis_a085781
import Mathlib

namespace OMA.P_oeis_a085781

open OMA.S_oeis_a085781

def c (m : ℕ) : ℤ := (((2 * m + 1).choose (m + 1) : ℕ) : ℤ)

theorem ha (n : ℕ) : a n = 2 * c n - 2 ^ n := rfl

theorem cb (m : ℕ) : ((Nat.centralBinom (m + 1) : ℕ) : ℤ) = 2 * c m := by
  have h : Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose (m + 1) := by
    rw [Nat.centralBinom, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ,
      Nat.choose_symm_half]
    ring
  rw [h, c]
  push_cast
  ring

theorem key (m : ℕ) : ((m : ℤ) + 2) * c (m + 1) = 2 * (2 * (m : ℤ) + 3) * c m := by
  have h3 : (((m + 1 + 1) * Nat.centralBinom (m + 1 + 1) : ℕ) : ℤ)
      = ((2 * (2 * (m + 1) + 1) * Nat.centralBinom (m + 1) : ℕ) : ℤ) := by
    rw [Nat.succ_mul_centralBinom_succ]
  have e1 := cb (m + 1)
  have e0 := cb m
  push_cast at h3
  rw [e1, e0] at h3
  linarith

end OMA.P_oeis_a085781

theorem OMA.solution : type_of% @OMA.S_oeis_a085781.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : m + 3 - 1 = m + 1 + 1 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : m + 3 - 3 = m := by omega
  have h0 : m + 3 = m + 1 + 1 + 1 := by omega
  rw [h1, h2, h3, h0]
  simp only [OMA.P_oeis_a085781.ha]
  have e0 := OMA.P_oeis_a085781.key m
  have e1 := OMA.P_oeis_a085781.key (m + 1)
  have e2 := OMA.P_oeis_a085781.key (m + 1 + 1)
  push_cast at e0 e1 e2 ⊢
  linear_combination 2 * e2 - 8 * e1 + 8 * e0
