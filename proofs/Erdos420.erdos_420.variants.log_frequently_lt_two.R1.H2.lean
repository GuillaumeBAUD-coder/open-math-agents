import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1

/-! # The divisor-count quotient is monotone in the shift

`⌊f n⌋₊ ≤ ⌊g n⌋₊`, so `(n + ⌊f n⌋₊)!` divides `(n + ⌊g n⌋₊)!`, and the divisor count is
monotone under divisibility. -/

open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H2 := by
  intro f g n hfg
  unfold Erdos420.F
  have hpos : (0 : ℝ) < (σ 0 n.factorial : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  apply div_le_div_of_nonneg_right _ hpos.le
  have hfl : ⌊f n⌋₊ ≤ ⌊g n⌋₊ := Nat.floor_le_floor hfg
  have hdvd : (n + ⌊f n⌋₊).factorial ∣ (n + ⌊g n⌋₊).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hle : σ 0 (n + ⌊f n⌋₊).factorial ≤ σ 0 (n + ⌊g n⌋₊).factorial := by
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) hdvd)
  exact_mod_cast hle
