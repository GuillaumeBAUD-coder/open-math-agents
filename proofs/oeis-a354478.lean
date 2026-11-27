import OMAStatements.S_oeis_a354478
import Mathlib

theorem stir_pos : ∀ n k : ℕ, k ≤ n → 0 < Nat.stirlingFirst (n + 1) (k + 1) := by
  intro n
  induction n with
  | zero => intro k hk; interval_cases k; simp [Nat.stirlingFirst_self]
  | succ n ih =>
    intro k hk
    rcases k with _ | k
    · rw [Nat.stirlingFirst_succ_succ]
      have := ih 0 (Nat.zero_le _)
      positivity
    · rw [Nat.stirlingFirst_succ_succ]
      have := ih k (by omega)
      omega

theorem stir_lower (m j : ℕ) (hj : j ≤ m) :
    m * (m + 1) ≤ 2 * Nat.stirlingFirst (m + 2) (j + 1) := by
  rcases Nat.lt_or_ge j m with h | h
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : Nat.stirlingFirst (m' + 3) (j + 1) ≥ (m' + 2) * Nat.stirlingFirst (m' + 2) (j + 1) := by
      rw [Nat.stirlingFirst_succ_succ]; omega
    have h2 : Nat.stirlingFirst (m' + 2) (j + 1) ≥ (m' + 1) * Nat.stirlingFirst (m' + 1) (j + 1) := by
      rw [Nat.stirlingFirst_succ_succ]; omega
    have h3 := stir_pos m' j (by omega)
    have h4 : Nat.stirlingFirst (m' + 2) (j + 1) ≥ m' + 1 := by
      calc _ ≥ (m' + 1) * Nat.stirlingFirst (m' + 1) (j + 1) := h2
        _ ≥ (m' + 1) * 1 := Nat.mul_le_mul_left _ h3
        _ = m' + 1 := by ring
    have h5 : Nat.stirlingFirst (m' + 3) (j + 1) ≥ (m' + 2) * (m' + 1) := by
      calc _ ≥ (m' + 2) * Nat.stirlingFirst (m' + 2) (j + 1) := h1
        _ ≥ (m' + 2) * (m' + 1) := Nat.mul_le_mul_left _ h4
    show (m' + 1) * (m' + 1 + 1) ≤ 2 * Nat.stirlingFirst (m' + 3) (j + 1)
    nlinarith
  · have : j = m := by omega
    subst this
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.stirlingFirst_succ_self_left]
    have := Nat.choose_two_right (j + 2)
    have h2 : 2 * ((j + 2) * (j + 2 - 1) / 2) = (j + 2) * (j + 2 - 1) := by
      apply Nat.mul_div_cancel'
      exact Nat.even_mul_pred_self (j + 2) |>.two_dvd
    rw [this, h2]
    show j * (j + 1) ≤ (j + 2) * (j + 1)
    nlinarith

theorem row_bound (m : ℕ) (hm : 1 ≤ m) :
    |OMA.S_oeis_a354478.rowSum (m + 2) - 1| ≤ 2 / (m : ℚ) := by
  unfold OMA.S_oeis_a354478.rowSum
  rw [Finset.sum_range_succ]
  have hlast : (1 : ℚ) / (OMA.S_oeis_a354478.signedStirling (m + 2) (m + 1 + 1) : ℚ) = 1 := by
    simp [OMA.S_oeis_a354478.signedStirling, Nat.stirlingFirst_self]
  rw [hlast, add_sub_cancel_right]
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  calc |∑ j ∈ Finset.range (m + 1), (1 : ℚ) / (OMA.S_oeis_a354478.signedStirling (m + 2) (j + 1) : ℚ)|
      ≤ ∑ j ∈ Finset.range (m + 1), |(1 : ℚ) / (OMA.S_oeis_a354478.signedStirling (m + 2) (j + 1) : ℚ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), (2 : ℚ) / ((m : ℚ) * (m + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        have hb := stir_lower m j (by omega)
        have hbq : (m : ℚ) * (m + 1) ≤ 2 * (Nat.stirlingFirst (m + 2) (j + 1) : ℚ) := by
          exact_mod_cast hb
        have hpos : (0 : ℚ) < (Nat.stirlingFirst (m + 2) (j + 1) : ℚ) := by
          have : (0 : ℚ) < (m : ℚ) * (m + 1) := by positivity
          linarith
        unfold OMA.S_oeis_a354478.signedStirling
        push_cast
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos hpos]
        rw [div_le_div_iff₀ hpos (by positivity)]
        linarith
    _ = 2 / (m : ℚ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

theorem OMA.solution : type_of% @OMA.S_oeis_a354478.main := by
  have hfun : (fun n : ℕ => ((OMA.S_oeis_a354478.rowSum n).num : ℝ) /
      ((OMA.S_oeis_a354478.rowSum n).den : ℝ)) =
      fun n : ℕ => ((OMA.S_oeis_a354478.rowSum n : ℚ) : ℝ) := by
    funext n
    rw [Rat.cast_def]
  rw [hfun, ← Filter.tendsto_add_atTop_iff_nat 3]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  have hb := row_bound (n + 1) (by omega)
  rw [Real.norm_eq_abs]
  have : |((OMA.S_oeis_a354478.rowSum (n + 3) : ℚ) : ℝ) - 1| =
      ((|OMA.S_oeis_a354478.rowSum (n + 1 + 2) - 1| : ℚ) : ℝ) := by
    push_cast; rfl
  rw [this]
  have hc : ((|OMA.S_oeis_a354478.rowSum (n + 1 + 2) - 1| : ℚ) : ℝ) ≤ ((2 / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hb
  calc _ ≤ _ := hc
    _ = 2 * (1 / ((n : ℝ) + 1)) := by push_cast; ring
