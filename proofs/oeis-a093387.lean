import OMAStatements.S_oeis_a093387
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: the 2^(n-1) part satisfies the recurrence identically; for the central term split by parity,
-- write C(2k,k) = centralBinom k and C(2k+1,k) = centralBinom(k+1)/2, then use
-- (k+1) centralBinom(k+1) = 2(2k+1) centralBinom(k). No computer search.

namespace OMA.A093387Proof

open OMA.S_oeis_a093387

theorem L1 (k : ℕ) : ((2 * k + 1).choose k : ℚ) = ((k + 1).centralBinom : ℚ) / 2 := by
  have h1 : (k + 1).centralBinom = (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Nat.choose_succ_succ]
  have h2 : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k := Nat.choose_symm_half k
  rw [h1, h2]; push_cast; ring

theorem L0 (k : ℕ) : ((2 * k).choose k : ℚ) = (k.centralBinom : ℚ) := by
  rw [Nat.centralBinom_eq_two_mul_choose]

theorem hc (k : ℕ) : ((k + 1 : ℚ)) * (((k + 1).centralBinom : ℕ) : ℚ) = 2 * (2 * k + 1) * k.centralBinom := by
  have h := Nat.succ_mul_centralBinom_succ k
  exact_mod_cast h

theorem mainP : ∀ n : ℕ, 4 ≤ n → ((n : ℤ) + 1) * a n + 2 * (-(n : ℤ) - 1) * a (n - 1) + 4 * (-(n : ℤ) + 2) * a (n - 2) + 8 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hq : ∀ x : ℤ, (x : ℚ) = 0 → x = 0 := fun x h => by exact_mod_cast h
  apply hq
  unfold a
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega,
    show m + 1 - 1 = m by omega]
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [show (2 * k + 4) / 2 = k + 2 by omega, show (2 * k + 3) / 2 = k + 1 by omega,
      show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [show 2 * k + 4 = 2 * (k + 2) by ring, show 2 * k + 3 = 2 * (k + 1) + 1 by ring,
      show 2 * k + 2 = 2 * (k + 1) by ring, L0, L1, L0, L1]
    simp only [show k + 1 + 1 = k + 2 by ring] at *
    ring
  · rw [show (2 * k + 1 + 4) / 2 = k + 2 by omega, show (2 * k + 1 + 3) / 2 = k + 2 by omega,
      show (2 * k + 1 + 2) / 2 = k + 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast
    rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring, show 2 * k + 1 + 3 = 2 * (k + 2) by ring,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, L0, L1, L0, L1]
    have h2 := hc (k + 2)
    have h1 := hc (k + 1)
    push_cast at h1 h2
    simp only [show k + 1 + 1 = k + 2 by ring, show k + 2 + 1 = k + 3 by ring] at *
    linear_combination -h2 + 4 * h1

end OMA.A093387Proof

open OMA.A093387Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a093387.main := mainP
