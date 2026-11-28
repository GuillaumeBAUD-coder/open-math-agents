import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib

/-! Brocard's equation as a consecutive-factor equation, and a checked prefix. -/

theorem consecutive_factor_iff (n : ℕ) (hn : 4 ≤ n) :
    (∃ m : ℕ, n.factorial + 1 = m ^ 2) ↔
      ∃ x : ℕ, x * (x + 1) = n.factorial / 4 := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨v, hv⟩ := Nat.dvd_factorial (by decide : 0 < 2) (by omega : 2 ≤ n)
    have hOdd : Odd (m * m) := by
      rw [← pow_two, ← hm]
      exact ⟨v, by omega⟩
    obtain ⟨x, hx⟩ := (Nat.odd_mul.mp hOdd).1
    rw [hx] at hm
    have hProduct : n.factorial = 4 * (x * (x + 1)) := by nlinarith
    exact ⟨x, by omega⟩
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv⟩ := Nat.dvd_factorial (by decide : 0 < 4) hn
    have hProduct : n.factorial = 4 * (x * (x + 1)) := by omega
    refine ⟨2 * x + 1, ?_⟩
    rw [hProduct]
    ring

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H1 :=
  consecutive_factor_iff
