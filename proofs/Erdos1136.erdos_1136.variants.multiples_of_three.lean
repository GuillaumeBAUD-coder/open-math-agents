import FormalConjectures.ErdosProblems.«1136»

/-! Count the multiples below `n` exactly and bound the rounding error in the density. -/
open Filter Topology

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.multiples_of_three := by
  constructor
  · intro a ha b hb k hsum
    exact (by decide : ¬ (3 : ℕ) ∣ 2)
      (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) (hsum ▸ dvd_add ha hb))
  · have count (n : ℕ) : ({m : ℕ | 3 ∣ m} ∩ Set.Iio n).ncard = (n + 2) / 3 := by
      have image : {m : ℕ | 3 ∣ m} ∩ Set.Iio n = (3 * ·) '' Set.Iio ((n+2)/3) := by
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_image]
        constructor
        · rintro ⟨⟨k, rfl⟩, hk⟩
          exact ⟨k, by omega, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨dvd_mul_right _ _, by omega⟩
      rw [image, Set.ncard_image_of_injective _ (by intro a b h; dsimp at h; omega)]
      simp
    simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
      count, Set.ncard_Iio_nat]
    have err : Tendsto (fun n : ℕ => (↑((n+2)/3) : ℝ) / n - 1/3) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : 0 < (n : ℝ) := by positivity
      have lo : (n : ℝ) ≤ 3 * (↑((n+2)/3) : ℝ) := by exact_mod_cast (show n ≤ 3*((n+2)/3) by omega)
      have hi : 3 * (↑((n+2)/3) : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show 3*((n+2)/3) ≤ n+2 by omega)
      rw [← mul_div_cancel_right₀ (1/3 : ℝ) hn'.ne', ← sub_div, Real.norm_eq_abs,
        abs_div, abs_of_pos hn']
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) hn'.le
    simpa using err.add_const (1/3 : ℝ)
