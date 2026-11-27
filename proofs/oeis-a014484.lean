import OMAStatements.S_oeis_a014484
import Mathlib

-- Problem: oeis-a014484
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P014484
open OMA.S_oeis_a014484

lemma six_dvd (m : ℕ) : 6 ∣ (m + 3).factorial := by
  have h : (3 : ℕ).factorial ∣ (m + 3).factorial := Nat.factorial_dvd_factorial (by omega)
  exact h

-- a (m + 1) = (m+3)! (2m+5) 2^(m+1) / 6, written via c m = (m+3)!/6
lemma a_eq (m : ℕ) : (a (m + 1) : ℤ) = ((m + 3).factorial / 6 : ℕ) * (2 * m + 5) * 2 ^ (m + 1) := by
  obtain ⟨c, hc⟩ := six_dvd m
  unfold a
  have e : (m + 1 + 2).factorial * (2 * (m + 1) + 3) * 2 ^ (m + 1)
      = 6 * (c * (2 * m + 5) * 2 ^ (m + 1)) := by
    rw [show m + 1 + 2 = m + 3 by ring, hc]; ring
  rw [e, Nat.mul_div_cancel_left _ (by norm_num), hc, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast; ring

theorem sol : type_of% @OMA.S_oeis_a014484.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h0 : (a 0 : ℤ) = 1 := by decide
  rcases m with _ | m
  · simp only [show (0:ℕ) + 2 - 1 = 0 + 1 by rfl, show (0:ℕ) + 2 - 2 = 0 by rfl]
    rw [a_eq, h0, show (0:ℕ) + 2 = 1 + 1 by rfl, a_eq]
    simp [Nat.factorial]
  · simp only [show m + 1 + 2 - 1 = (m + 1) + 1 by omega, show m + 1 + 2 - 2 = m + 1 by omega,
      show m + 1 + 2 = (m + 2) + 1 by omega]
    rw [a_eq, a_eq, a_eq]
    obtain ⟨c, hc⟩ := six_dvd m
    have f1 : (m + 1 + 3).factorial = (m + 4) * (m + 3).factorial := by
      rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.factorial_succ]
    have f2 : (m + 2 + 3).factorial = (m + 5) * ((m + 4) * (m + 3).factorial) := by
      rw [show m + 2 + 3 = (m + 4) + 1 by ring, Nat.factorial_succ, ← f1]
    rw [f2, f1, hc]
    rw [show (m + 5) * ((m + 4) * (6 * c)) = 6 * ((m + 5) * ((m + 4) * c)) by ring,
      show (m + 4) * (6 * c) = 6 * ((m + 4) * c) by ring,
      Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast
    ring

end OMA.P014484

theorem OMA.solution : type_of% @OMA.S_oeis_a014484.main := OMA.P014484.sol
