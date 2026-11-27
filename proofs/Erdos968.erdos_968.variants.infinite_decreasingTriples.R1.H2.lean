import OMAReductions.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1

-- Step Erdos968.erdos_968.variants.infinite_decreasingTriples.R1.H2: hypothesis H2 of reduction Erdos968.erdos_968.variants.infinite_decreasingTriples.R1

/-!
Chebyshev's bound gives `π(x) ≤ (log 4 + 1) x / log x` for large `x`. Once
`log x > (log 4 + 1) / δ` this is below `δ x`.
-/

theorem OMA.solution :
    OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1.H2 := by
  unfold OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R1.H2
  intro c hc
  have h1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have h2 : ∀ᶠ k : ℕ in Filter.atTop, (Real.log 4 + 1) / c < Real.log (k : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop _
  filter_upwards [h1, h2, Filter.eventually_gt_atTop 1] with k hk1 hk2 hk3
  show ((Nat.primeCounting k : ℕ) : ℝ) < c * (k : ℝ)
  rw [Nat.floor_natCast] at hk1
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : 0 < Real.log (k : ℝ) :=
    lt_of_le_of_lt (div_nonneg (by linarith) hc.le) hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk3
    linarith
  have h3 : Real.log 4 + 1 < Real.log (k : ℝ) * c := (div_lt_iff₀ hc).mp hk2
  have h4 : (Real.log 4 + 1) * (k : ℝ) / Real.log (k : ℝ) < c * (k : ℝ) := by
    rw [div_lt_iff₀ hlog]
    nlinarith
  linarith
