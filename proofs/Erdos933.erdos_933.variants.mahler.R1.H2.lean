import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1
import Mathlib

/-! Take c(n) = max (log_n (max (F n) 1) - 1) 0 + 1/n. Then F n < n^(1 + c n) for n at least 2,
and c n tends to 0 because log_n (max (F n) 1) is eventually below 1 + eps/2 for every eps. -/

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1.H2 := by
  intro F hF
  refine ⟨fun n => max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ), ?_, ?_⟩
  · have h1 : (1 : ℕ → ℝ) = fun _ => (1 : ℝ) := rfl
    rw [h1, Asymptotics.isLittleO_one_iff]
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ?_, fun a ha => ?_⟩
    · have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      have := le_max_right (Real.logb n (max (F n) 1) - 1) 0
      show a < max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ)
      linarith
    · filter_upwards [hF (a / 2) (by positivity), eventually_ge_atTop (max 2 (⌈2 / a⌉₊ + 1))]
        with n hlt hge
      show max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ) < a
      have hn2 : (2 : ℝ) ≤ n := by
        have : 2 ≤ n := le_trans (le_max_left _ _) hge
        exact_mod_cast this
      have hnc : (⌈2 / a⌉₊ : ℝ) + 1 ≤ n := by
        have : ⌈2 / a⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hge
        exact_mod_cast this
      have hca : 2 / a ≤ (⌈2 / a⌉₊ : ℝ) := Nat.le_ceil _
      have hinv : 1 / (n : ℝ) < a / 2 := by
        have hn0 : (0 : ℝ) < n := by linarith
        rw [div_lt_div_iff₀ hn0 (by norm_num)]
        have : 2 / a < n := by linarith
        rw [div_lt_iff₀ ha] at this
        linarith
      have hM : max (F n) 1 < (n : ℝ) ^ (1 + a / 2) :=
        max_lt hlt (Real.one_lt_rpow (by linarith) (by linarith))
      have hlog : Real.logb n (max (F n) 1) < 1 + a / 2 := by
        have := Real.logb_lt_logb (by linarith : (1 : ℝ) < n)
          (lt_max_of_lt_right one_pos) hM
        rwa [Real.logb_rpow (by linarith) (by linarith)] at this
      have : max (Real.logb n (max (F n) 1) - 1) 0 < a / 2 :=
        max_lt (by linarith) (by linarith)
      linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    show F n < (n : ℝ) ^ (1 + (max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ)))
    have hn1 : (1 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hM0 : (0 : ℝ) < max (F n) 1 := lt_max_of_lt_right one_pos
    have hpow : (n : ℝ) ^ Real.logb n (max (F n) 1) = max (F n) 1 :=
      Real.rpow_logb (by linarith) (ne_of_gt hn1) hM0
    have hlt : Real.logb n (max (F n) 1) <
        1 + (max (Real.logb n (max (F n) 1) - 1) 0 + 1 / (n : ℝ)) := by
      have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      have := le_max_left (Real.logb n (max (F n) 1) - 1) 0
      linarith
    calc F n ≤ max (F n) 1 := le_max_left _ _
      _ = (n : ℝ) ^ Real.logb n (max (F n) 1) := hpow.symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hn1 hlt
