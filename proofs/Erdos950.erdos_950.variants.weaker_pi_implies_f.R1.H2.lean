import OMAReductions.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Reciprocal sums from two interval counting estimates

Group the integers by their dyadic scale. Below the cutoff the reciprocal
contribution of the jth block is bounded by a constant times 1/j. Above
the cutoff each block contributes at most a constant divided by log n.
-/
open Finset Filter Real

theorem OMA.solution : OMA.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1.H2 := by
  classical
  intro K K₀ C hK hK₀ hC
  have h2 : 0 < log 2 := log_pos (by norm_num)
  let A := 2*K₀/log 2
  let D := C/log 2
  let B := 2*K*(1/log 2+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := div_pos hC h2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  use A*(2+|log D|)+B
  have hlog : Tendsto (fun n : ℕ => log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := tendsto_log_atTop.comp hlog
  have hlll := tendsto_log_atTop.comp hll
  have hcut := ((isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hlog.eventually_ge_atTop 1, hll.eventually_ge_atTop (1/D),
    hlll.eventually_ge_atTop 1,tendsto_natCast_atTop_atTop.eventually hcut,eventually_ge_atTop 2]
    with n hnlog hnll hnlll hncut hn2
  intro S hS hsmall hlarge
  change 1 ≤ log (log (log n)) at hnlll
  change 1/D ≤ log (log n) at hnll
  have hln : 0 < log n := by linarith
  let L := log n ^ C
  have hL : 0 < L := rpow_pos_of_pos hln _
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hLn : L < n := by
    change ‖L‖ ≤ (1/2)*‖(n:ℝ)^(1:ℝ)‖ at hncut
    rw [rpow_one,Real.norm_of_nonneg hL.le,Real.norm_of_nonneg hn0.le] at hncut
    linarith
  let y := D * log (log n)
  have hy : 1 ≤ y := by
    dsimp [y]
    linarith [(div_le_iff₀ hD).mp hnll]
  let u := Nat.log 2 n + 1
  let J := ⌊y⌋₊
  let sets (j : ℕ) := S.filter fun s => Nat.log 2 s = j
  let weights (j : ℕ) := ∑ s ∈ sets j, (1:ℝ)/s
  have hsumeq : (∑ j ∈ range u, weights j) = ∑ s ∈ S, (1:ℝ)/s :=
    sum_fiberwise_of_maps_to (g := Nat.log 2) (fun s hs => mem_range.mpr
      (Nat.lt_succ_of_le (Nat.log_monotone (hS s hs).2))) _
  have hblock (j : ℕ) : weights j ≤
      (if j < J then A*((j:ℝ)+1)⁻¹ else 0) + 2*K/log n := by
    let t := 2^(j+1)
    have ht2 : 2 ≤ t := Nat.le_self_pow (Nat.succ_ne_zero _) _
    have hscale : (t:ℝ) = (2:ℝ)^j * 2 := by simp [t,pow_succ]
    have htpos : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
    have hden : (0:ℝ)<2^j := by positivity
    have hsub : sets j ⊆ S.filter (· ≤ min t n) := by
      intro s hs
      obtain ⟨hs,hj⟩ := mem_filter.mp hs
      have hh := Nat.lt_pow_succ_log_self (b:=2) (by decide) s
      rw [hj] at hh
      exact mem_filter.mpr ⟨hs,le_min hh.le (hS s hs).2⟩
    have hh : weights j ≤ ((sets j).card:ℝ)/(2:ℝ)^j := by
      calc
        _ ≤ ∑ _ ∈ sets j, (1:ℝ)/(2:ℝ)^j := sum_le_sum (by
          intro s hs
          obtain ⟨hs,hj⟩ := mem_filter.mp hs
          have hpos := (hS s hs).1
          have hpow := Nat.pow_log_le_self 2 (show s ≠ 0 by omega)
          rw [hj] at hpow
          gcongr
          exact_mod_cast hpow)
        _ = _ := by simp [div_eq_mul_inv]
    have hrest : 0 ≤ 2*K/log n := by positivity
    have hterm : 0 ≤ (if j < J then A*((j:ℝ)+1)⁻¹ else 0) := by split_ifs <;> positivity
    by_cases htl : (t:ℝ) ≤ L
    · have hsub' : sets j ⊆ S.filter (· ≤ t) := hsub.trans
        (monotone_filter_right S (fun s _ hs => le_trans hs (min_le_left _ _)))
      have ha := hsmall t ht2 htl
      have hw := (show ((sets j).card:ℝ) ≤ _ by exact_mod_cast card_le_card hsub').trans ha
      have hlt : log t = ((j:ℝ)+1)*log 2 := by simp [t,Real.log_pow]
      have hjlt : j < J := by
        have hl := log_le_log htpos htl
        rw [hlt,show log L = C*log (log n) from Real.log_rpow hln _] at hl
        have h := (le_div_iff₀ h2).mpr hl
        have hj : (j+1:ℕ) ≤ y := by
          calc
            (↑(j+1:ℕ):ℝ) = (j:ℝ)+1 := by simp
            _ ≤ C*log (log n)/log 2 := h
            _ = y := by dsimp only [y,D]; ring
        exact Nat.lt_of_succ_le (Nat.le_floor hj)
      rw [if_pos hjlt]
      apply hh.trans
      apply le_add_of_le_of_nonneg _ hrest
      rw [hlt,hscale] at hw
      dsimp [A]
      apply (div_le_iff₀ hden).mpr
      convert hw using 1 <;> field_simp <;> ring
    · have ha := hlarge (min t n) (by
        rw [Nat.cast_min, lt_min_iff]
        exact ⟨lt_of_not_ge htl,hLn⟩) (min_le_right _ _)
      have hw := (show ((sets j).card:ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans ha
      have hm : (min t n:ℝ) ≤ t := by exact_mod_cast min_le_left t n
      push_cast at hw
      have hlim : ((sets j).card:ℝ) ≤ K*t/log n := hw.trans (by gcongr)
      apply hh.trans
      apply le_add_of_nonneg_of_le hterm
      apply (div_le_iff₀ hden).mpr
      rw [hscale] at hlim
      calc
        _ ≤ K*((2:ℝ)^j*2)/log n := hlim
        _ = _ := by ring
  have harm : ∑ j ∈ range u, (if j < J then A*((j:ℝ)+1)⁻¹ else 0) ≤ A*(1+log y) := by
    rw [← sum_filter,← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hA.le
    calc
      _ ≤ ∑ j ∈ range J, ((j:ℝ)+1)⁻¹ := sum_le_sum_of_subset_of_nonneg
        (fun j hj => mem_range.mpr (mem_filter.mp hj).2) (by intros; positivity)
      _ = (harmonic J : ℝ) := by simp [harmonic]
      _ ≤ _ := harmonic_floor_le_one_add_log y hy
  have hu : ((u:ℝ)* (2*K/log n)) ≤ B := by
    have hh := Real.log_le_log (show 0 < (2:ℝ)^(Nat.log 2 n) by positivity)
      (show (2:ℝ)^(Nat.log 2 n) ≤ n by exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega))
    rw [Real.log_pow] at hh
    have hmax := (le_div_iff₀ h2).2 hh
    dsimp [u,B]
    push_cast
    have h1 : ((Nat.log 2 n:ℝ)+1) ≤ (log n/log 2 + log n) := by linarith
    calc
      _ ≤ (log n/log 2 + log n)*(2*K/log n) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by field_simp
  have hsum := sum_le_sum (s := range u) (fun j _ => hblock j)
  rw [hsumeq,sum_add_distrib] at hsum
  simp only [sum_const,card_range,nsmul_eq_mul] at hsum
  have hylog : log y = log D + log (log (log n)) := Real.log_mul hD.ne'
    (by have := (one_div_pos.mpr hD).trans_le hnll; positivity)
  rw [hylog] at harm
  have hh : 1+ (log D + log (log (log n))) ≤ (2+|log D|)*log (log (log n)) := by
    nlinarith [le_abs_self (log D),mul_le_mul_of_nonneg_left hnlll (abs_nonneg (log D))]
  nlinarith [mul_le_mul_of_nonneg_left hh hA.le,mul_le_mul_of_nonneg_left hnlll hB]
