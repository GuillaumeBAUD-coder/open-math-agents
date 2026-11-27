import OMAReductions.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1

-- Step EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1.H1: hypothesis H1 of reduction EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1
-- Credit: @luciusacarr
-- H1 := ∀ k b : ℕ, 5 < k → (3 ∣ k ∨ 4 ∣ k) → ∀ a : Fin 2 → ℕ, (∀ i, a i > 0) →     ∑ i, (a i) ^ k ≠ b ^ k

theorem OMA.solution : OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1.H1 := by
  intro k b hk hd a ha h
  have hflt : FermatLastTheoremFor k := by
    rcases hd with h3 | h4
    · exact fermatLastTheoremThree.mono h3
    · exact fermatLastTheoremFour.mono h4
  rw [Fin.sum_univ_two] at h
  have h0 := ha 0
  have h1 := ha 1
  have hb : b ≠ 0 := by
    rintro rfl
    have : 0 < a 0 ^ k := pow_pos h0 k
    rw [zero_pow (by omega)] at h
    omega
  exact hflt (a 0) (a 1) b (by omega) (by omega) hb h
