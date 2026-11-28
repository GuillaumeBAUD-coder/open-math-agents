import OMAStatements.S_oeis_a051524
import Mathlib

-- Problem: A051524, the second unsigned column of A051338; Mathar's recurrence.
-- Upstream: formal-conjectures statements/oeis-a051524.lean (declaration OMA.S_oeis_a051524.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: with u(n) = |T(n,0)| and v(n) = |T(n,1)| one has u(n+1) = (n+6) u(n) and
-- v(n+1) = u(n) + (n+6) v(n); eliminating u gives the three-term recurrence for v = a.

namespace OMA.P_oeis_a051524

open OMA.S_oeis_a051524

theorem T0 (n : ℕ) : T (n + 1) 0 = -((n + 1 + 5 : ℕ) : ℤ) * T n 0 := rfl

theorem T1 (n : ℕ) : T (n + 1) 1 = T n 0 - ((n + 1 + 5 : ℕ) : ℤ) * T n 1 := rfl

/-- The unsigned first two columns. -/
def S0 (n : ℕ) : ℤ := (-1) ^ n * T n 0
def S1 (n : ℕ) : ℤ := (-1) ^ (n + 1) * T n 1

theorem S0_succ (n : ℕ) : S0 (n + 1) = ((n + 1 + 5 : ℕ) : ℤ) * S0 n := by
  unfold S0
  rw [T0, pow_succ]
  ring

theorem S1_succ (n : ℕ) : S1 (n + 1) = S0 n + ((n + 1 + 5 : ℕ) : ℤ) * S1 n := by
  unfold S0 S1
  rw [T1, pow_succ, pow_succ]
  ring

theorem nonneg : ∀ n : ℕ, 0 ≤ S0 n ∧ 0 ≤ S1 n
  | 0 => by
    refine ⟨by simp [S0, T], by simp [S1, T]⟩
  | n + 1 => by
    obtain ⟨h0, h1⟩ := nonneg n
    rw [S0_succ, S1_succ]
    constructor <;> positivity

theorem a_eq (n : ℕ) : a n = S1 n := by
  unfold a
  have hT : T n 1 = (-1) ^ (n + 1) * S1 n := by
    unfold S1
    rw [← mul_assoc, ← pow_add]
    rw [show n + 1 + (n + 1) = 2 * (n + 1) by ring, pow_mul]
    simp
  rw [hT, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (nonneg n).2]

theorem main' : ∀ n : ℕ,
    a (n + 2) + (-2 * ((n + 2 : ℕ) : ℤ) - 9) * a (n + 1) + (((n + 2 : ℕ) : ℤ) + 4) ^ 2 * a n = 0 := by
  intro n
  rw [a_eq, a_eq, a_eq]
  have e1 := S1_succ (n + 1)
  have e2 := S0_succ n
  have e3 := S1_succ n
  push_cast at e1 e2 e3 ⊢
  rw [e1, e2]
  have : S0 n = S1 (n + 1) - ((n : ℤ) + 1 + 5) * S1 n := by rw [e3]; ring
  rw [this]
  ring

end OMA.P_oeis_a051524

theorem OMA.solution : type_of% @OMA.S_oeis_a051524.main := OMA.P_oeis_a051524.main'
