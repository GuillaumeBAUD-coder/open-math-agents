import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R2

-- Credit: @Masselorc
-- Agent: chatgpt
-- Model: GPT-6 Astra Pro
-- Prime extraction, with a direct indicator bound and floor-division simplification.
-- The original tent argument and mass comparison come from the merged CramerConjecture
-- baker_harman_pintz R1 reduction and its H2 proof.

namespace OMA.Erdos687PrimeExtraction
open Filter Finset ArithmeticFunction

-- The finite tent estimate adapts the CramerConjecture baker_harman_pintz R1 reduction.

noncomputable def F (n : ℕ) : ℝ := ∑ k ∈ range n, Λ k * ((n : ℝ) - k)

lemma truncate_sum {n N : ℕ} (hn : n ≤ N) :
    F n = ∑ k ∈ range N, Λ k * max ((n : ℝ) - k) 0 := by
  unfold F
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun k hk => ?_
    have : (k : ℝ) < n := by exact_mod_cast mem_range.mp hk
    rw [max_eq_left (by linarith)]
  · intro k _ hk
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (by simpa using hk)
    rw [max_eq_right (by linarith), mul_zero]

lemma tent_bound (a h : ℕ) :
    F (a + 2*h) - 2*F (a+h) + F a ≤ h * ∑ k ∈ Ico a (a+2*h), Λ k := by
  rw [truncate_sum (N := a+2*h) le_rfl, truncate_sum (N := a+2*h) (by omega),
    truncate_sum (n := a) (N := a+2*h) (by omega), mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, mul_sum]
  rw [show Ico a (a+2*h) = (range (a+2*h)).filter (a ≤ ·) by ext; simp [and_comm], sum_filter]
  refine sum_le_sum fun k _ => ?_
  have hw : max (((a+2*h : ℕ) : ℝ)-k) 0 - 2*max (((a+h : ℕ) : ℝ)-k) 0 +
      max ((a : ℝ)-k) 0 ≤ if a ≤ k then (h : ℝ) else 0 := by
    have hh : (0 : ℝ) ≤ h := h.cast_nonneg
    push_cast
    simp only [← Nat.cast_le (α := ℝ), max_def]
    split_ifs <;> linarith
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ Λ k from vonMangoldt_nonneg)
  split_ifs at * <;> nlinarith only [hm]

lemma mass_le (a h : ℕ) (ha : 1 ≤ a)
    (hnop : ∀ k ∈ Ico a (a + 2 * h), ¬ k.Prime) :
    ∑ k ∈ Ico a (a + 2 * h), (vonMangoldt k : ℝ) ≤
      Chebyshev.psi (a + 2 * h : ℕ) - Chebyshev.theta (a + 2 * h : ℕ) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
  intro k hk
  obtain ⟨hka, hkb⟩ := mem_Ico.mp hk
  simp only [mem_filter, mem_Ioc, Nat.floor_natCast]
  exact ⟨⟨Nat.succ_le_iff.mp (ha.trans hka), hkb.le⟩, hnop k hk⟩

theorem scale_bound (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ n : ℕ in atTop,
    let h := ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ / 2
    C * Real.sqrt (n + 1 + 2 * h : ℕ) ≤ (h : ℝ) / 4 := by
  simp_rw [← Nat.floor_div_natCast]
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ (4 / 25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually (eventually_ge_atTop (16 * C + 4)),
    eventually_ge_atTop 1] with n hn hn1
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set h := ⌊(n : ℝ) ^ (33 / 50 : ℝ) / 2⌋₊
  change C * Real.sqrt (n + 1 + 2 * h : ℕ) ≤ (h : ℝ) / 4
  have hf : (h : ℝ) ≤ (n : ℝ) ^ (33 / 50 : ℝ) / 2 := Nat.floor_le (by positivity)
  have hl : (n : ℝ) ^ (33 / 50 : ℝ) / 2 < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr : (n : ℝ) ^ (33 / 50 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1r (show (33 / 50 : ℝ) ≤ 1 by norm_num)
  have hs : Real.sqrt (n + 1 + 2 * h : ℕ) ≤ 2 * Real.sqrt n := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    push_cast
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have he : (n : ℝ) ^ (33 / 50 : ℝ) = Real.sqrt n * (n : ℝ) ^ (4 / 25 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : (0 : ℝ) < n)]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (n : ℝ))
  have hs1 := Real.one_le_sqrt.mpr hn1r
  have hb := mul_le_mul_of_nonneg_left hs hC
  rw [he] at hl
  nlinarith

lemma floor_cube {n : ℕ} (hn : 1 ≤ n) : ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ ^ 3 ≤ n ^ 2 := by
  have h : (⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
    (Nat.floor_le (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) h 3
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)] at hp
  norm_num at hp
  exact_mod_cast hp

end OMA.Erdos687PrimeExtraction

open Filter Finset ArithmeticFunction OMA.Erdos687PrimeExtraction in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R2.H3 := by
  classical
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hC0 : 0 ≤ C := by simpa using hC 1
  filter_upwards [scale_bound C hC0, eventually_ge_atTop 1] with n hs hn
  let h := ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ / 2
  change C * Real.sqrt (n + 1 + 2 * h : ℕ) ≤ (h : ℝ) / 4 at hs
  intro hmass
  change (h : ℝ)^2/4 < F (n+1+2*h) - 2*F (n+1+h) + F (n+1) at hmass
  by_contra! hbad
  have hnop : ∀ p ∈ Ico (n+1) (n+1+2*h), ¬ p.Prime := by
    intro p hp hprime
    have hi := mem_Ico.mp hp
    have hd : p-n ≤ ⌊(n : ℝ) ^ (33 / 50 : ℝ)⌋₊ := by omega
    exact not_lt_of_ge ((Nat.pow_le_pow_left hd 3).trans (floor_cube hn))
      (hbad p hprime (by omega))
  have hsum := ((mass_le (n+1) h (by omega) hnop).trans (hC _)).trans hs
  have ht := tent_bound (n+1) h
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg h)
  nlinarith
