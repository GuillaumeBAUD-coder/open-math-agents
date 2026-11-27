import OMAStatements.S_oeis_a121669

-- Complete refutation of OEIS A121669: count(n) <= 10^n while proposed(n) = (n-1)*(n-2)^(n-2),
-- so count(n) / proposed(n) -> 0, contradicting k > 0.
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a121669 Filter Topology

private lemma count_le_ten_pow (n : ℕ) : count n ≤ 10 ^ n := by
  classical
  unfold count
  calc
    (Finset.univ.filter (fun w : Word n => qualifies w)).card
      ≤ (Finset.univ : Finset (Word n)).card := Finset.card_filter_le _ _
    _ = 10 ^ n := by
      simp [Word, Fintype.card_fin]

private lemma ratio_le_bound (n : ℕ) (hn : 22 ≤ n) :
    (count n : ℝ) / proposed n ≤ 100 / (n - 1 : ℝ) := by
  have h1 : (count n : ℝ) ≤ (10 : ℝ) ^ n := by
    exact_mod_cast count_le_ten_pow n
  have hpos_m : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have h20 : (10 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
    have : 10 ≤ n - 2 := by omega
    exact_mod_cast this
  have hpow : (10 : ℝ) ^ (n - 2) ≤ ((n - 2 : ℕ) : ℝ) ^ (n - 2) :=
    pow_le_pow_left₀ (by norm_num) h20 (n - 2)
  have hpow_pos : (0 : ℝ) < (10 : ℝ) ^ (n - 2) := by positivity
  have hden_le : ((n - 1 : ℕ) : ℝ) * (10 : ℝ) ^ (n - 2) ≤ proposed n := by
    unfold proposed
    exact mul_le_mul_of_nonneg_left hpow (le_of_lt hpos_m)
  have hden_pos : (0 : ℝ) < proposed n := lt_of_lt_of_le (mul_pos hpos_m hpow_pos) hden_le
  have h10n : (10 : ℝ) ^ n = 100 * (10 : ℝ) ^ (n - 2) := by
    have hn_eq : n = (n - 2) + 2 := by omega
    conv_lhs => rw [hn_eq, pow_add]
    ring
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  calc
    (count n : ℝ) / proposed n
      ≤ (10 : ℝ) ^ n / proposed n := div_le_div_of_nonneg_right h1 (le_of_lt hden_pos)
    _ ≤ (10 : ℝ) ^ n / (((n - 1 : ℕ) : ℝ) * (10 : ℝ) ^ (n - 2)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hpos_m hpow_pos) hden_le
    _ = 100 / ((n - 1 : ℕ) : ℝ) := by
        rw [h10n]
        field_simp [ne_of_gt hpos_m, ne_of_gt hpow_pos]
    _ = 100 / ((n : ℝ) - 1) := by rw [hcast]

private lemma tendsto_ratio_zero :
    Tendsto (fun n : ℕ => (count n : ℝ) / proposed n) atTop (𝓝 0) := by
  have h_upper : Tendsto (fun n : ℕ => (100 : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using tendsto_const_nhds.div_atTop h1
  refine squeeze_zero' ?_ ?_ h_upper
  · refine Filter.eventually_atTop.mpr ⟨22, fun n hn => ?_⟩
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · unfold proposed
      positivity
  · exact Filter.eventually_atTop.mpr ⟨22, fun n hn => ratio_le_bound n hn⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a121669.main) := by
  rintro ⟨k, hkpos, hlim⟩
  have h0 : k = 0 := tendsto_nhds_unique hlim tendsto_ratio_zero
  linarith
