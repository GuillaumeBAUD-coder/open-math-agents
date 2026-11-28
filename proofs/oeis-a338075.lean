import OMAStatements.S_oeis_a338075
import Mathlib

open OMA.S_oeis_a338075 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a338075.main := by
  have ht : ∀ k : ℕ, t (k + 1) = 3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) / ((k : ℚ) + 1) ^ 2 * t k := by
    intro k
    unfold t
    rw [show 3 * (k + 1) = (3 * k + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ (3 * k + 1),
      Nat.factorial_succ (3 * k), Nat.factorial_succ k]
    have h1 : ((3 * k).factorial : ℚ) ≠ 0 := by positivity
    have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h3 : (k : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · ext n
    rw [show (1 + X : PowerSeries ℚ) * PowerSeries.mk t = PowerSeries.mk t + PowerSeries.mk t * X by ring]
    rcases n with _ | n
    · simp [a]
    · simp only [map_add, coeff_mk, coeff_succ_mul_X]
      simp [a]
      ring
  · intro n
    have e1 : a (n + 1) = t n + t (n + 1) := by simp [a]
    have e2 : a (n + 2) = t (n + 1) + t (n + 2) := by simp [a]
    have e3 : a (n + 3) = t (n + 2) + t (n + 3) := by simp [a]
    have e4 : a (n + 4) = t (n + 3) + t (n + 4) := by simp [a]
    rw [e1, e2, e3, e4, show n + 4 = (n + 3) + 1 by ring, ht (n + 3), show n + 3 = (n + 2) + 1 by ring,
      ht (n + 2), show n + 2 = (n + 1) + 1 by ring, ht (n + 1), ht n]
    push_cast
    have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h3 : (n : ℚ) + 1 + 1 + 1 ≠ 0 := by positivity
    have h4 : (n : ℚ) + 1 + 1 + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
