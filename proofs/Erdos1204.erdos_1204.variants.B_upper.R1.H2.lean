import OMAReductions.R_Erdos1204_erdos_1204_variants_B_upper_R1

-- Step Erdos1204.erdos_1204.variants.B_upper.R1.H2: hypothesis H2 of reduction Erdos1204.erdos_1204.variants.B_upper.R1
-- Credit: @OrangeHeadz
-- H2 := ∀ δ > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (Nat.primeCounting k : ℝ) ≤ δ * k  /-- The `k` primes `p_{π(k)}, …, p_{π(k)+k-1}` form an admissible set, so `minSum k` is at most their sum. -/

/-! # The primes have density zero

Mathlib's Chebyshev bound gives `π ⌊x⌋ ≤ (log 4 + 1) * x / log x` for all large real `x`.
Specialising to `x = k` and taking `k` large enough that `log k ≥ (log 4 + 1) / δ` gives
`π k ≤ δ * k`. -/

open Filter

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_B_upper_R1.H2 := by
  intro δ hδ
  have h1 := Chebyshev.eventually_primeCounting_le (ε := 1) one_pos
  have h2 : ∀ᶠ k : ℕ in atTop, (Nat.primeCounting ⌊(k : ℝ)⌋₊ : ℝ) ≤
      (Real.log 4 + 1) * (k : ℝ) / Real.log (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually h1
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h2, hlog.eventually_ge_atTop ((Real.log 4 + 1) / δ),
    hlog.eventually_gt_atTop 0] with k hk hl hpos
  rw [Nat.floor_natCast] at hk
  refine hk.trans ?_
  rw [div_le_iff₀ hpos]
  have h3 := (div_le_iff₀ hδ).1 hl
  have h4 := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg (α := ℝ) k)
  nlinarith
