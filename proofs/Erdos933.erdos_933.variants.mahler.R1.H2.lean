import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1

-- Step Erdos933.erdos_933.variants.mahler.R1.H2: hypothesis H2 of reduction Erdos933.erdos_933.variants.mahler.R1
-- Credit: @corentingenton
-- H2 := ∀ F : ℕ → ℝ,   (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, F n < (n : ℝ) ^ (1 + ε)) →   ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop, F n < (n : ℝ) ^ (1 + c n)

open Filter Asymptotics

/- Proof: take G n = max (F n) 1 and c n = max (logb n (G n) - 1) 0 + 1 / n.
   For n ≥ 2, F n ≤ G n = n ^ (logb n (G n)) < n ^ (1 + c n).
   c tends to 0: c n ≥ 0, and for a > 0, eventually F n < n ^ (1 + a / 2), hence
   logb n (G n) < 1 + a / 2, while 1 / n < a / 2. -/
theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1.H2 := by
  intro F hF
  refine ⟨fun n => max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ), ?_, ?_⟩
  · have key : Tendsto (fun n : ℕ => max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ))
        atTop (nhds 0) := by
      rw [tendsto_order]
      constructor
      · intro a ha
        filter_upwards with n
        have h1 : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
        have h2 := le_max_right (Real.logb n (max (F n) 1) - 1) 0
        linarith
      · intro a ha
        have ha2 : 0 < a / 2 := half_pos ha
        have hinv := (tendsto_order.1 tendsto_one_div_atTop_nhds_zero_nat).2 _ ha2
        filter_upwards [hF (a / 2) ha2, hinv, eventually_ge_atTop 2] with n hn hn' h2
        have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
        have hGpos : (0:ℝ) < max (F n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
        have hGlt : max (F n) 1 < (n:ℝ) ^ (1 + a / 2) :=
          max_lt hn (Real.one_lt_rpow hn1 (by linarith))
        have hlog : Real.logb n (max (F n) 1) < 1 + a / 2 :=
          (Real.logb_lt_iff_lt_rpow hn1 hGpos).2 hGlt
        have hm : max (Real.logb n (max (F n) 1) - 1) 0 < a / 2 := max_lt (by linarith) ha2
        linarith
    exact (isLittleO_one_iff ℝ).2 key
  · filter_upwards [eventually_ge_atTop 2] with n h2
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0:ℝ) < n := by linarith
    have hGpos : (0:ℝ) < max (F n) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hrpow : (n:ℝ) ^ (Real.logb n (max (F n) 1)) = max (F n) 1 :=
      Real.rpow_logb hn0 hn1.ne' hGpos
    have hpos : (0:ℝ) < 1 / (n:ℝ) := by positivity
    have hle := le_max_left (Real.logb n (max (F n) 1) - 1) 0
    have hexp : Real.logb n (max (F n) 1)
        < 1 + (max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n:ℝ)) := by linarith
    calc F n ≤ max (F n) 1 := le_max_left _ _
      _ = (n:ℝ) ^ (Real.logb n (max (F n) 1)) := hrpow.symm
      _ < (n:ℝ) ^ (1 + (max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n:ℝ))) :=
        Real.rpow_lt_rpow_of_exponent_lt hn1 hexp
