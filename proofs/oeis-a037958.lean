import OMAStatements.S_oeis_a037958
import Mathlib

-- Problem: A037958, a(n) = binomial(n, floor((n-8)/2)), Mathar's three-term recurrence.
-- Upstream: formal-conjectures statements/oeis-a037958.lean (declaration OMA.S_oeis_a037958.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: small n are checked directly; for n >= 10 split by parity and relate the three binomial
-- coefficients by the absorption identities (N+1-k) C(N+1,k) = (N+1) C(N,k) and
-- (k+1) C(N,k+1) = (N-k) C(N,k); the recurrence is a linear combination of these.

namespace OMA.P_oeis_a037958

open OMA.S_oeis_a037958

/-- `(N + 1 - k) C(N+1, k) = (N + 1) C(N, k)` in the integers. -/
theorem r_up (N k : ℕ) :
    ((N + 1 - k : ℕ) : ℤ) * ((N + 1).choose k : ℤ) = ((N + 1 : ℕ) : ℤ) * (N.choose k : ℤ) := by
  have := Nat.choose_mul_succ_eq N k
  have h : ((N.choose k * (N + 1) : ℕ) : ℤ) = (((N + 1).choose k * (N + 1 - k) : ℕ) : ℤ) := by
    exact_mod_cast this
  push_cast at h ⊢
  linarith

/-- `(k + 1) C(N, k+1) = (N - k) C(N, k)` in the integers. -/
theorem r_right (N k : ℕ) :
    ((k + 1 : ℕ) : ℤ) * (N.choose (k + 1) : ℤ) = ((N - k : ℕ) : ℤ) * (N.choose k : ℤ) := by
  have := Nat.choose_succ_right_eq N k
  have h : ((N.choose (k + 1) * (k + 1) : ℕ) : ℤ) = ((N.choose k * (N - k) : ℕ) : ℤ) := by
    exact_mod_cast this
  push_cast at h ⊢
  linarith

theorem main' : ∀ n : ℕ, 2 ≤ n →
    -((n : ℤ) + 9) * ((n : ℤ) - 8) * a n + 2 * (n : ℤ) * a (n - 1) +
      4 * (n : ℤ) * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  intro n hn
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> simp [a]
  · rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · -- n = 2m with m ≥ 5; write m = j + 5
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
      subst hm
      have e0 : a (2 * (j + 5)) = ((2 * j + 10).choose (j + 1) : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) - 8) / 2 = j + 1 by omega,
          show 2 * (j + 5) = 2 * j + 10 by ring]
      have e1 : a (2 * (j + 5) - 1) = ((2 * j + 9).choose j : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) - 1 - 8) / 2 = j by omega,
          show 2 * (j + 5) - 1 = 2 * j + 9 by omega]
      have e2 : a (2 * (j + 5) - 2) = ((2 * j + 8).choose j : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) - 2 - 8) / 2 = j by omega,
          show 2 * (j + 5) - 2 = 2 * j + 8 by omega]
      rw [e0, e1, e2]
      have h1 := r_up (2 * j + 8) j
      have h2 := r_up (2 * j + 9) j
      have h3 := r_right (2 * j + 10) j
      rw [show 2 * j + 8 + 1 - j = j + 9 by omega, show 2 * j + 8 + 1 = 2 * j + 9 by ring] at h1
      rw [show 2 * j + 9 + 1 - j = j + 10 by omega, show 2 * j + 9 + 1 = 2 * j + 10 by ring] at h2
      rw [show 2 * j + 10 - j = j + 10 by omega] at h3
      push_cast at h1 h2 h3 ⊢
      linear_combination (-2 * (2 * (j : ℤ) + 19)) * h3 + (-2 * (2 * (j : ℤ) + 19)) * h2 +
        (-4 * (2 * (j : ℤ) + 10)) * h1
    · -- n = 2m + 1 with m ≥ 5; write m = j + 5
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
      subst hm
      have e0 : a (2 * (j + 5) + 1) = ((2 * j + 11).choose (j + 1) : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) + 1 - 8) / 2 = j + 1 by omega,
          show 2 * (j + 5) + 1 = 2 * j + 11 by ring]
      have e1 : a (2 * (j + 5) + 1 - 1) = ((2 * j + 10).choose (j + 1) : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) + 1 - 1 - 8) / 2 = j + 1 by omega,
          show 2 * (j + 5) + 1 - 1 = 2 * j + 10 by omega]
      have e2 : a (2 * (j + 5) + 1 - 2) = ((2 * j + 9).choose j : ℤ) := by
        unfold a; rw [if_neg (by omega), show (2 * (j + 5) + 1 - 2 - 8) / 2 = j by omega,
          show 2 * (j + 5) + 1 - 2 = 2 * j + 9 by omega]
      rw [e0, e1, e2]
      have r1 := r_up (2 * j + 10) (j + 1)
      have r2 := r_right (2 * j + 10) j
      have r3 := r_up (2 * j + 9) j
      rw [show 2 * j + 10 + 1 - (j + 1) = j + 10 by omega,
        show 2 * j + 10 + 1 = 2 * j + 11 by ring] at r1
      rw [show 2 * j + 10 - j = j + 10 by omega] at r2
      rw [show 2 * j + 9 + 1 - j = j + 10 by omega, show 2 * j + 9 + 1 = 2 * j + 10 by ring] at r3
      push_cast at r1 r2 r3 ⊢
      linear_combination (-2 * (2 * (j : ℤ) + 3)) * r1 + (-4 * (2 * (j : ℤ) + 11)) * r2 +
        (-4 * (2 * (j : ℤ) + 11)) * r3

end OMA.P_oeis_a037958

theorem OMA.solution : type_of% @OMA.S_oeis_a037958.main := OMA.P_oeis_a037958.main'
