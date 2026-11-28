import OMAReductions.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1
import Mathlib

-- Step EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1.H1: hypothesis H1 of reduction EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1
-- Credit: @ivillar. If 3 or 4 divides k, a^k + b^k = c^k has no positive solution by Fermat's Last Theorem for exponents 3 and 4 (Mathlib fermatLastTheoremThree, fermatLastTheoremFour, FermatLastTheoremFor.mono).

/-! Step EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1.H1. -/

theorem P8Euler.euler_h1 : ∀ k b : ℕ, 5 < k → (3 ∣ k ∨ 4 ∣ k) → ∀ a : Fin 2 → ℕ, (∀ i, a i > 0) →
    ∑ i, (a i) ^ k ≠ b ^ k := by
  intro k b hk5 hk a ha
  have hF : FermatLastTheoremFor k := by
    rcases hk with h | h
    · exact fermatLastTheoremThree.mono h
    · exact fermatLastTheoremFour.mono h
  rw [Fin.sum_univ_two]
  intro heq
  by_cases hb : b = 0
  · subst hb
    have h0 : 0 < a 0 ^ k := pow_pos (ha 0) k
    rw [zero_pow (by omega)] at heq
    omega
  · exact hF (a 0) (a 1) b (ha 0).ne' (ha 1).ne' hb heq

theorem OMA.solution : OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1.H1 :=
  P8Euler.euler_h1
