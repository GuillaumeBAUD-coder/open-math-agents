import OMAReductions.R_SteinerSystems_infinitely_many_steiner_t4_R1
import Mathlib

-- Step SteinerSystems.infinitely_many_steiner_t4.R1.H2: hypothesis H2 of reduction
-- SteinerSystems.infinitely_many_steiner_t4.R1
-- Credit: @ivillar

/-!
Take `n = 120 N + 5`. Then `n - 3 = 2 (60 N + 1)`, `n - 2 = 3 (40 N + 1)`, `n - 1 = 4 (30 N + 1)`,
`n = 5 (24 N + 1)`, and `k! C(m, k) = m (m - 1) ⋯ (m - k + 1)` gives
`C(n, 4) = 5 P₀`, `C(n - 1, 3) = 4 P₁`, `C(n - 2, 2) = 3 P₂`, `C(n - 3, 1) = 2 P₃`.
-/

theorem OMA.solution : OMA.R_SteinerSystems_infinitely_many_steiner_t4_R1.H2 := by
  unfold OMA.R_SteinerSystems_infinitely_many_steiner_t4_R1.H2
  intro N
  refine ⟨120 * N + 5, by omega, ?_⟩
  intro i hi
  interval_cases i
  · show 5 ∣ Nat.choose (120 * N + 5) 4
    have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 5) 4
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 120 * N + 5 - 3 = 120 * N + 2 by omega, show 120 * N + 5 - 2 = 120 * N + 3 by omega,
      show 120 * N + 5 - 1 = 120 * N + 4 by omega, show 120 * N + 5 - 0 = 120 * N + 5 by omega,
      show Nat.factorial 4 = 24 by rfl] at h
    exact ⟨(24 * N + 1) * (30 * N + 1) * (40 * N + 1) * (60 * N + 1), by nlinarith [h]⟩
  · show 4 ∣ Nat.choose (120 * N + 4) 3
    have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 4) 3
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 120 * N + 4 - 2 = 120 * N + 2 by omega, show 120 * N + 4 - 1 = 120 * N + 3 by omega,
      show 120 * N + 4 - 0 = 120 * N + 4 by omega, show Nat.factorial 3 = 6 by rfl] at h
    exact ⟨(30 * N + 1) * (40 * N + 1) * (60 * N + 1), by nlinarith [h]⟩
  · show 3 ∣ Nat.choose (120 * N + 3) 2
    have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 3) 2
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 120 * N + 3 - 1 = 120 * N + 2 by omega, show 120 * N + 3 - 0 = 120 * N + 3 by omega,
      show Nat.factorial 2 = 2 by rfl] at h
    exact ⟨(40 * N + 1) * (60 * N + 1), by nlinarith [h]⟩
  · show 2 ∣ Nat.choose (120 * N + 2) 1
    rw [Nat.choose_one_right]
    exact ⟨60 * N + 1, by ring⟩
