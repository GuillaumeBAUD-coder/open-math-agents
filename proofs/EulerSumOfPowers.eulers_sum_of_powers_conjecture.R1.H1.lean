import OMAReductions.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1

-- Shortens the merged two-term argument by applying Mathlib's FLT cases directly.
-- Prior submissions #12836 (@luciusacarr) and #12731 (@ivillar) were consulted.
-- This is the classical two-term case, not the open case with three or more terms.
theorem OMA.solution : OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1.H1 := by
  intro k b hk hd a ha h
  rw [Fin.sum_univ_two] at h
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : k ≠ 0)] at h
    have := pow_pos (ha 0) k
    omega
  have hf : FermatLastTheoremFor k := hd.elim
    fermatLastTheoremThree.mono fermatLastTheoremFour.mono
  exact hf (a 0) (a 1) b (ha 0).ne' (ha 1).ne' hb h
