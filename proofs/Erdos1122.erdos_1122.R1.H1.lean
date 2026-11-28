import OMAReductions.R_Erdos1122_erdos_1122_R1
import Mathlib

-- Step H1 of the Erdős 1122 reduction: Erdős's 1946 theorem that a nondecreasing additive
-- function is a multiple of the logarithm.
-- The proof is adapted from the merged proof of Erdos1122.erdos_1122.variants.monotone in
-- open-math-agents (PR 15, by @Genbox); only the statement it is attached to is changed.
/-! Nondecreasing additive arithmetic functions are multiples of the logarithm. -/

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos1122_erdos_1122_R1.H1 := by
  intro f hf hmono
  have hf1 : f 1 = 0 := by
    have h := hf 1 (by decide) 1 (by decide) (by decide)
    simp only [Nat.one_mul] at h
    linarith
  have hle {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : f a ≤ f b := by
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact ih.trans (hmono b (ha.trans hb))
  have hgrowth (i : ℕ) : f (2 ^ (i + 1) + 1) ≤ (i : ℝ) * f 2 + f 3 := by
    induction i with
    | zero => norm_num
    | succ i ih =>
      have hc : (2 : ℕ).Coprime (2 ^ (i + 1) + 1) := by
        rw [pow_succ', Nat.coprime_mul_left_add_right]
        simp
      calc
        f (2 ^ (i + 1 + 1) + 1) ≤ f (2 * (2 ^ (i + 1) + 1)) :=
          hle (Nat.succ_le_iff.mpr (by positivity)) (by rw [pow_succ']; omega)
        _ = f 2 + f (2 ^ (i + 1) + 1) := hf 2 (by decide) _ (by positivity) hc
        _ ≤ ((i + 1 : ℕ) : ℝ) * f 2 + f 3 := by
          push_cast
          linarith
  have small_gap (m : ℕ) (e : ℝ) (he : 0 < e) :
      ∃ a : ℕ, 0 < a ∧ m.Coprime a ∧ f (a + 2 * m) - f a < e := by
    let K := 2 * m
    let q (j : ℕ) := 1 + K * j
    have hq (j : ℕ) : 0 < q j := by dsimp [q]; omega
    by_contra h
    have hgap (j : ℕ) : e ≤ f (q (j + 1)) - f (q j) := by
      by_contra! hlt
      apply h
      refine ⟨q j, hq j, ?_, ?_⟩
      · change Nat.Coprime m (1 + 2 * m * j)
        rw [show 2 * m * j = (2 * j) * m by ring, Nat.coprime_add_mul_right_right]
        simp
      · rw [show q j + 2 * m = q (j + 1) by dsimp [q, K]; ring]
        exact hlt
    have hlinear (j : ℕ) : (j : ℝ) * e ≤ f (q j) := by
      induction j with
      | zero => simp [q, hf1]
      | succ j ih =>
        have hstep := hgap j
        push_cast
        linarith
    have hcompare (i : ℕ) : q (2 ^ i) ≤ 2 ^ (i + K + 1) + 1 := by
      have hK : K ≤ 2 ^ (K + 1) :=
        le_trans (le_of_lt K.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) (by omega))
      calc
        q (2 ^ i) = 1 + K * 2 ^ i := rfl
        _ ≤ 1 + 2 ^ (K + 1) * 2 ^ i :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _
        _ = 2 ^ (i + K + 1) + 1 := by
          rw [← pow_add, show K + 1 + i = i + K + 1 by omega, Nat.add_comm]
    have hb (i : ℕ) : e ≤ (((i : ℝ) + K) * f 2 + f 3) / (2 : ℝ) ^ i := by
      apply (le_div_iff₀ (by positivity)).mpr
      have h1 := hlinear (2 ^ i)
      have h2 := hle (hq (2 ^ i)) (hcompare i)
      have h3 := hgrowth (i + K)
      push_cast at h1 h3
      linarith
    have hlim1 : Tendsto (fun i : ℕ => (i : ℝ) / (2 : ℝ) ^ i) atTop (𝓝 0) := by
      simpa only [pow_one] using
        (tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num))
    have hlim0 : Tendsto (fun i : ℕ => (1 : ℝ) / (2 : ℝ) ^ i) atTop (𝓝 0) := by
      simpa only [pow_zero] using
        (tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num))
    have hlim : Tendsto (fun i : ℕ => (((i : ℝ) + K) * f 2 + f 3) / (2 : ℝ) ^ i)
        atTop (𝓝 0) := by
      have hsum := (hlim1.const_mul (f 2)).add (hlim0.const_mul ((K : ℝ) * f 2 + f 3))
      rw [mul_zero, mul_zero, add_zero] at hsum
      exact hsum.congr (fun i => by ring)
    exact (not_le_of_gt he) (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb)
  have f_pow_succ (m : ℕ) (hm : 0 < m) (r : ℕ) :
      f (m ^ (r + 1)) = f (m ^ r) + f m := by
    by_cases hm1 : m = 1
    · simp [hm1, hf1]
    have hm2 : 1 < m := by omega
    have hbound (e : ℝ) (he : 0 < e) :
        |f (m ^ (r + 1)) - (f (m ^ r) + f m)| ≤ e := by
      obtain ⟨a, ha, hcop, hgap⟩ := small_gap m e he
      let x := a + m
      have hx : 0 < x := by dsimp [x]; omega
      have hc : m.Coprime x := Nat.coprime_add_self_right.mpr hcop
      have hcb : m.Coprime (a + 2 * m) :=
        (Nat.coprime_add_mul_right_right m a 2).mpr hcop
      have hm_x : 1 < m * x := hm2.trans_le (Nat.le_mul_of_pos_right _ hx)
      have hminus_pos : 0 < m * x - 1 := by omega
      have hplus : m.Coprime (m * x + 1) := by
        rw [Nat.coprime_mul_left_add_right]
        simp
      have hminus : m.Coprime (m * x - 1) := by
        refine Nat.Coprime.of_dvd_left (dvd_mul_right m x) ?_
        refine (Nat.coprime_self_sub_right (show 1 ≤ m * x by omega)).mpr ?_
        simp
      have hmid : f (m ^ (r + 1) * x) = f (m ^ (r + 1)) + f x :=
        hf _ (by positivity) _ hx (hc.pow_left _)
      have hax : f a ≤ f x := hle ha (by dsimp [x]; omega)
      have hxb : f x ≤ f (a + 2 * m) := hle hx (by dsimp [x]; omega)
      have hreal_lower : f (m ^ r) + f m + f a ≤ f (m ^ (r + 1)) + f x := by
        calc
          f (m ^ r) + f m + f a = f (m ^ r) + f (m * a) := by
            rw [hf m hm a ha hcop, add_assoc]
          _ ≤ f (m ^ r) + f (m * x - 1) := by
            apply add_le_add_right
            apply hle (Nat.succ_le_iff.mpr (by positivity))
            have hx_eq : m * x = m * a + m * m := by dsimp [x]; ring
            rw [hx_eq]
            have hm_sq : 0 < m * m := Nat.mul_pos hm hm
            omega
          _ = f (m ^ r * (m * x - 1)) := (hf _ (by positivity) _ hminus_pos (hminus.pow_left _)).symm
          _ ≤ f (m ^ (r + 1) * x) := by
            apply hle (Nat.mul_pos (pow_pos hm r) hminus_pos)
            rw [pow_succ, Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = _ := hmid
      have hreal_upper : f (m ^ (r + 1)) + f x ≤ f (m ^ r) + f m + f (a + 2 * m) := by
        calc
          f (m ^ (r + 1)) + f x = f (m ^ (r + 1) * x) := hmid.symm
          _ ≤ f (m ^ r * (m * x + 1)) := by
            apply hle (Nat.succ_le_iff.mpr (by positivity))
            rw [pow_succ, Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.le_succ _)
          _ = f (m ^ r) + f (m * x + 1) :=
            hf _ (by positivity) _ (by positivity) (hplus.pow_left _)
          _ ≤ f (m ^ r) + f (m * (a + 2 * m)) := by
            apply add_le_add_right
            apply hle (Nat.succ_le_iff.mpr (by positivity))
            have hx_eq : m * (a + 2 * m) = m * x + m * m := by dsimp [x]; ring
            rw [hx_eq]
            have hm_sq : 0 < m * m := Nat.mul_pos hm hm
            omega
          _ = _ := by rw [hf m hm _ (by omega) hcb, add_assoc]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    by_contra hne
    have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hhalf := hbound _ (half_pos hpos)
    linarith
  have hpow (a : ℕ) (ha : 0 < a) (r : ℕ) : f (a ^ r) = (r : ℝ) * f a := by
    induction r with
    | zero => simp [hf1]
    | succ r ih =>
      rw [f_pow_succ a ha r, ih]
      push_cast
      ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf2 : 0 ≤ f 2 := by
    rw [← hf1]
    exact hle (by decide) (by decide)
  let c := f 2 / Real.log 2
  have hc : 0 ≤ c := div_nonneg hf2 hlog2.le
  have hc_log : c * Real.log 2 = f 2 := div_mul_cancel₀ _ hlog2.ne'
  refine ⟨c, ?_⟩
  intro n hn
  have hbound (t : ℕ) : |(t : ℝ) * (f n - c * Real.log n)| ≤ f 2 := by
    let k := Nat.log 2 (n ^ t)
    have hlow : 2 ^ k ≤ n ^ t := Nat.pow_log_le_self _ (pow_ne_zero _ hn.ne')
    have hhigh : n ^ t ≤ 2 ^ (k + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hf_low := hle (pow_pos (by decide : 0 < (2 : ℕ)) k) hlow
    have hf_high := hle (pow_pos hn t) hhigh
    rw [hpow 2 (by decide) k, hpow n hn t] at hf_low
    rw [hpow 2 (by decide) (k + 1), hpow n hn t] at hf_high
    have hlog_low : (k : ℝ) * Real.log 2 ≤ (t : ℝ) * Real.log n := by
      have h := Real.log_le_log (show 0 < ((2 ^ k : ℕ) : ℝ) by positivity)
        (show ((2 ^ k : ℕ) : ℝ) ≤ ((n ^ t : ℕ) : ℝ) by exact_mod_cast hlow)
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
    have hlog_high : (t : ℝ) * Real.log n ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      have h := Real.log_le_log (show 0 < ((n ^ t : ℕ) : ℝ) by positivity)
        (show ((n ^ t : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) by exact_mod_cast hhigh)
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
    have hc_low : (k : ℝ) * f 2 ≤ (t : ℝ) * (c * Real.log n) := by
      rw [← hc_log]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hlog_low hc
    have hc_high : (t : ℝ) * (c * Real.log n) ≤ ((k + 1 : ℕ) : ℝ) * f 2 := by
      rw [← hc_log]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hlog_high hc
    push_cast at hf_high hc_high
    rw [mul_sub]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  by_contra hne
  have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨t, ht⟩ := exists_nat_gt (f 2 / |f n - c * Real.log n|)
  have hbig := (div_lt_iff₀ hpos).mp ht
  have hsmall := hbound t
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)] at hsmall
  exact (not_lt_of_ge hsmall) hbig