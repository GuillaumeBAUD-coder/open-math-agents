import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1

/-!
# Proof of `Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H2`

Iteration lemma for the Leng–Sah–Sawhney density increment framework on Erdős Problem #3 ($5,000):
a fixed decrease `η > 0` in the nonnegative quantity `gap s` allows at most `⌊gap s / η⌋₊ + 1`
steps, bounding `level s ≤ M * (1 + gap s) ^ (D + 1)` and yielding
`exp (-gap s) ≤ K * exp (-(max (level s) 0) ^ c)` with `c = 1 / (D + 2)` and `K = exp (M + 1)`.
-/

-- Step Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H2
-- Credit: @Need17Bread

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1.H2 := by
  intro State gap level η C D hη hC hgap hstep
  have hiter : ∀ (n : ℕ) (s : State), gap s < ((n : ℝ) + 1) * η →
      level s ≤ ((n : ℝ) + 1) * C * (1 + gap s) ^ D := by
    intro n
    induction n with
    | zero =>
      intro s hlt
      simp only [Nat.cast_zero, zero_add, one_mul] at hlt
      rcases hstep s with hbase | ⟨t, hgt, _⟩
      · simpa using hbase
      · linarith [hgap t]
    | succ n ih =>
      intro s hlt
      have h1g : 0 ≤ 1 + gap s := by linarith [hgap s]
      have hpow_nonneg : 0 ≤ C * (1 + gap s) ^ D := by positivity
      rcases hstep s with hbase | ⟨t, hgt, hlt_lev⟩
      · have hge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
        nlinarith
      · have ht_lt : gap t < ((n : ℝ) + 1) * η := by
          push_cast at hlt
          linarith
        have hih := ih t ht_lt
        have hpow_le : (1 + gap t) ^ D ≤ (1 + gap s) ^ D :=
          pow_le_pow_left₀ (by linarith [hgap t]) (by linarith) D
        have hcoeff_nonneg : 0 ≤ ((n : ℝ) + 1) * C := by positivity
        have ht_bound : level t ≤ ((n : ℝ) + 1) * C * (1 + gap s) ^ D :=
          hih.trans (mul_le_mul_of_nonneg_left hpow_le hcoeff_nonneg)
        push_cast
        linarith
  let M : ℝ := C * max 1 η⁻¹
  have hM_pos : 0 < M := by positivity
  let c : ℝ := 1 / ((D + 2 : ℕ) : ℝ)
  have hc_pos : 0 < c := by positivity
  let K : ℝ := Real.exp (M + 1)
  have hK_pos : 0 < K := Real.exp_pos _
  have hpow_cancel : ∀ a : ℝ, 0 ≤ a → (a ^ (D + 2)) ^ c = a := by
    intro a ha
    rw [← Real.rpow_natCast a (D + 2), ← Real.rpow_mul ha]
    have hne : ((D + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp only [c]
    rw [mul_one_div_cancel hne, Real.rpow_one]
  refine ⟨c, K, hc_pos, hK_pos, fun s => ?_⟩
  let n : ℕ := ⌊gap s / η⌋₊
  have hn_lt : gap s < ((n : ℝ) + 1) * η :=
    (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one (gap s / η))
  have hn_le : (n : ℝ) ≤ gap s / η :=
    Nat.floor_le (div_nonneg (hgap s) hη.le)
  have hn1_le : (n : ℝ) + 1 ≤ max 1 η⁻¹ * (1 + gap s) := by
    have h1 : (1 : ℝ) ≤ max 1 η⁻¹ := le_max_left _ _
    have h2 : η⁻¹ ≤ max 1 η⁻¹ := le_max_right _ _
    have hdiv : gap s / η = η⁻¹ * gap s := by rw [div_eq_inv_mul]
    rw [hdiv] at hn_le
    nlinarith [hgap s]
  have hlev_poly : level s ≤ M * (1 + gap s) ^ (D + 1) := by
    have hbase := hiter n s hn_lt
    have hpow_nonneg : 0 ≤ (1 + gap s) ^ D := pow_nonneg (by linarith [hgap s]) D
    have hmul : ((n : ℝ) + 1) * C ≤ M * (1 + gap s) := by
      dsimp only [M]
      nlinarith
    calc level s
        ≤ ((n : ℝ) + 1) * C * (1 + gap s) ^ D := hbase
      _ ≤ (M * (1 + gap s)) * (1 + gap s) ^ D :=
          mul_le_mul_of_nonneg_right hmul hpow_nonneg
      _ = M * (1 + gap s) ^ (D + 1) := by rw [pow_succ', mul_assoc]
  have hmax_le : max (level s) 0 ≤ M * (1 + gap s) ^ (D + 1) :=
    max_le hlev_poly (mul_nonneg hM_pos.le (pow_nonneg (by linarith [hgap s]) _))
  have hbound_c : (max (level s) 0) ^ c ≤ gap s + (M + 1) := by
    by_cases hle : 1 + gap s ≤ M
    · have hdom : max (level s) 0 ≤ M ^ (D + 2) := by
        calc max (level s) 0
            ≤ M * (1 + gap s) ^ (D + 1) := hmax_le
          _ ≤ M * M ^ (D + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hgap s]) hle _) hM_pos.le
          _ = M ^ (D + 2) := by rw [← pow_succ']
      have hrp := Real.rpow_le_rpow (le_max_right _ _) hdom hc_pos.le
      rw [hpow_cancel M hM_pos.le] at hrp
      linarith [hgap s]
    · have hge : M ≤ 1 + gap s := le_of_not_ge hle
      have hdom : max (level s) 0 ≤ (1 + gap s) ^ (D + 2) := by
        calc max (level s) 0
            ≤ M * (1 + gap s) ^ (D + 1) := hmax_le
          _ ≤ (1 + gap s) * (1 + gap s) ^ (D + 1) :=
              mul_le_mul_of_nonneg_right hge (pow_nonneg (by linarith [hgap s]) _)
          _ = (1 + gap s) ^ (D + 2) := by rw [← pow_succ']
      have hrp := Real.rpow_le_rpow (le_max_right _ _) hdom hc_pos.le
      rw [hpow_cancel (1 + gap s) (by linarith [hgap s])] at hrp
      linarith
  dsimp only [K]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith
