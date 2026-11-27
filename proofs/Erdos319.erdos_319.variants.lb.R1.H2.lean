import OMAReductions.R_Erdos319_erdos_319_variants_lb_R1

-- Step Erdos319.erdos_319.variants.lb.R1.H2: hypothesis H2 of reduction Erdos319.erdos_319.variants.lb.R1

/-!
Let `C = [B, N] \ S`. Every `i ∈ C` has `1 / N ≤ 1 / i`, so `|C| / N ≤ ∑_{i ∈ C} 1 / i`, and that
sum is `∑_{i = B}^{N} 1 / i - 1` because the reciprocals over `S` sum to `1`. Finally
`1 / i ≤ log i - log (i - 1)` telescopes to `∑_{i = B}^{N} 1 / i ≤ log N - log (B - 1)`.
-/

namespace OMA

theorem inv_le_log_sub (x : ℝ) (hx : 2 ≤ x) : 1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
  rw [Real.log_div hx1.ne' hx0.ne'] at h
  have e : (x - 1) / x - 1 = -(1 / x) := by
    field_simp
    ring
  rw [e] at h
  linarith

theorem harm_le (B : ℕ) (hB : 2 ≤ B) : ∀ m : ℕ,
    ∑ i ∈ Finset.Icc B (B - 1 + m), (1 : ℝ) / (i : ℝ) ≤
      Real.log ((B - 1 + m : ℕ) : ℝ) - Real.log ((B - 1 : ℕ) : ℝ) := by
  intro m
  induction m with
  | zero =>
    have he : Finset.Icc B (B - 1 + 0) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he]
    simp
  | succ m ih =>
    have e : B - 1 + (m + 1) = (B - 1 + m) + 1 := by omega
    rw [e, Finset.sum_Icc_succ_top (by omega)]
    have hk := inv_le_log_sub (((B - 1 + m + 1 : ℕ)) : ℝ) (by
      have : 2 ≤ B - 1 + m + 1 := by omega
      exact_mod_cast this)
    have e2 : (((B - 1 + m + 1 : ℕ)) : ℝ) - 1 = ((B - 1 + m : ℕ) : ℝ) := by
      push_cast
      ring
    rw [e2] at hk
    linarith

end OMA

theorem OMA.solution : OMA.R_Erdos319_erdos_319_variants_lb_R1.H2 := by
  unfold OMA.R_Erdos319_erdos_319_variants_lb_R1.H2
  intro B N S hB hBN hS hsum
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsumR : ∑ i ∈ S, (1 : ℝ) / (i : ℝ) = 1 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hsum
    simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at h
    exact h
  -- the complement
  have hcard : ((Finset.Icc B N \ S).card : ℝ) = ((Finset.Icc B N).card : ℝ) - (S.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hS, Nat.cast_sub (Finset.card_le_card hS)]
  have hsplit : ∑ i ∈ Finset.Icc B N \ S, (1 : ℝ) / (i : ℝ) + ∑ i ∈ S, (1 : ℝ) / (i : ℝ) =
      ∑ i ∈ Finset.Icc B N, (1 : ℝ) / (i : ℝ) := Finset.sum_sdiff hS
  have hlow : ((Finset.Icc B N \ S).card : ℝ) / (N : ℝ) ≤
      ∑ i ∈ Finset.Icc B N \ S, (1 : ℝ) / (i : ℝ) := by
    have h : ∑ _i ∈ Finset.Icc B N \ S, (1 : ℝ) / (N : ℝ) ≤
        ∑ i ∈ Finset.Icc B N \ S, (1 : ℝ) / (i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiI := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi).1
      have hipos : (0 : ℝ) < (i : ℝ) := by
        have : 0 < i := by omega
        exact_mod_cast this
      exact one_div_le_one_div_of_le hipos (by exact_mod_cast hiI.2)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    have e : ((Finset.Icc B N \ S).card : ℝ) / (N : ℝ) =
        ((Finset.Icc B N \ S).card : ℝ) * (1 / (N : ℝ)) := by ring
    rw [e]
    exact h
  have hharm := OMA.harm_le B hB (N - B + 1)
  have eN : B - 1 + (N - B + 1) = N := by omega
  rw [eN] at hharm
  have eB : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [eB] at hharm
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  rw [← hcard, Real.log_div hNpos.ne' hB1.ne']
  linarith
