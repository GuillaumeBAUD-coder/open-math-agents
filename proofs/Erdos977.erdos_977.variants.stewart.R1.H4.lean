import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1
import Mathlib

namespace OMA.Erdos977R1H4Proof

open Real Filter OMA.R_Erdos977_erdos_977_variants_stewart_R1

private lemma eventually_log_le_rpow_quarter :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_ge_atTop ((8 : ℝ) ^ (8 : ℕ))] with x hx
  have hx0 : 0 < x := by linarith [show (1 : ℝ) ≤ (8 : ℝ) ^ (8 : ℕ) by norm_num]
  have h8 : Real.log (x ^ (1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
  have hlog8 : Real.log x = 8 * Real.log (x ^ (1 / 8 : ℝ)) := by
    rw [Real.log_rpow hx0]
    ring
  have hge8 : (8 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    calc
      (8 : ℝ) = ((8 : ℝ) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num)]
        norm_num
      _ = ((8 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by norm_num
      _ ≤ x ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hmul : 8 * x ^ (1 / 8 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
    calc
      8 * x ^ (1 / 8 : ℝ) ≤ x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hge8 (Real.rpow_nonneg hx0.le _)
      _ = x ^ ((1 / 8 : ℝ) + (1 / 8 : ℝ)) := (Real.rpow_add hx0 _ _).symm
      _ = x ^ (1 / 4 : ℝ) := by norm_num
  linarith

lemma h4_proof : H4 := by
  let M : ℝ := ∑ k ∈ Finset.range 16,
    |(k : ℝ) * ((k : ℝ) * exp (-log (k : ℝ) / (51.9 * log (log (k : ℝ)))) * log (k : ℝ))|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM_bound : ∀ P : ℕ, P < 16 →
      (P : ℝ) * ((P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log (P : ℝ)) ≤ M := by
    intro P hP
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum
      (f := fun k : ℕ => |(k : ℝ) * ((k : ℝ) * exp (-log (k : ℝ) / (51.9 * log (log (k : ℝ)))) * log (k : ℝ))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hP)
  refine ⟨1, one_pos, ?_⟩
  have hnat_log : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnat_ll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat_log
  have h1 : ∀ᶠ n : ℕ in atTop, 16 ≤ n := eventually_ge_atTop 16
  have h2 : ∀ᶠ n : ℕ in atTop, 100 ≤ Real.log (Real.log (n : ℝ)) :=
    hnat_ll.eventually (eventually_ge_atTop 100)
  have h3 : ∀ᶠ n : ℕ in atTop, 100 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hpow := tendsto_natCast_atTop_atTop.eventually eventually_log_le_rpow_quarter
    have hbig : ∀ᶠ n : ℕ in atTop, (10000 : ℝ) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 10000)
    have hge1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hpow, hbig, hge1] with n hn hnb hn1
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hn0 : 0 ≤ (n : ℝ) := by linarith
    have h4th : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
      norm_num
    have hsq : (100 * (Real.log (n : ℝ)) ^ 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
      calc
        (100 * (Real.log (n : ℝ)) ^ 2) ^ 2
            = 10000 * (Real.log (n : ℝ)) ^ 4 := by ring
        _ ≤ 10000 * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by gcongr
        _ = 10000 * (n : ℝ) := by rw [h4th]
        _ ≤ (n : ℝ) ^ 2 := by nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hn0 hsq
  have h4 : ∀ᶠ n : ℕ in atTop, 10 * (M + 1) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (10 * (M + 1)))
  have h5 : ∀ᶠ n : ℕ in atTop,
      4 * Real.log (Real.log (n : ℝ)) + 10 ≤
        Real.log (n : ℝ) / (60000 * Real.log (Real.log (n : ℝ))) := by
    have hpow := hnat_log.eventually eventually_log_le_rpow_quarter
    have hbig : ∀ᶠ n : ℕ in atTop, (300000 : ℝ) ^ 2 ≤ Real.log (n : ℝ) :=
      hnat_log.eventually (eventually_ge_atTop ((300000 : ℝ) ^ 2))
    filter_upwards [hpow, hbig, h2] with n hn hnb hll
    have hl0 : 0 ≤ Real.log (n : ℝ) := by linarith
    have hll0 : 0 ≤ Real.log (Real.log (n : ℝ)) := by linarith
    have h4th : ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) ^ 4 = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
      norm_num
    have hsq : (300000 * (Real.log (Real.log (n : ℝ))) ^ 2) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
      calc
        (300000 * (Real.log (Real.log (n : ℝ))) ^ 2) ^ 2
            = 300000 ^ 2 * (Real.log (Real.log (n : ℝ))) ^ 4 := by ring
        _ ≤ 300000 ^ 2 * ((Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) ^ 4 := by gcongr
        _ = 300000 ^ 2 * Real.log (n : ℝ) := by rw [h4th]
        _ ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
    have h300 : 300000 * (Real.log (Real.log (n : ℝ))) ^ 2 ≤ Real.log (n : ℝ) :=
      le_of_pow_le_pow_left₀ (by norm_num) hl0 hsq
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hlog_ge : ∀ᶠ n : ℕ in atTop, 100 ≤ Real.log (n : ℝ) :=
    hnat_log.eventually (eventually_ge_atTop 100)
  filter_upwards [h1, h2, h3, h4, h5, hlog_ge] with n hn16 hll_ge hsq_bound hM_lt h5_bound hl_ge
  intro P hineq
  rw [one_mul]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog2_gt : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_lt : Real.log 2 < (0.7 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hnatlog_le : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h := Real.log_le_log (by positivity) hpow
    simpa [Real.log_pow] using h
  have hden_pos : 0 < (Nat.log 2 n : ℝ) + 1 := by positivity
  have hden_le : (Nat.log 2 n : ℝ) + 1 ≤ 2 * Real.log (n : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    nlinarith
  have hlhs_main : (2 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) ≤
      (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by
    have h1d : Real.log 2 / (2 * Real.log (n : ℝ)) ≤ 1 / ((Nat.log 2 n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) hden_pos]
      rw [one_mul, mul_comm (Real.log 2), ← le_div_iff₀ hlog2_pos]
      exact hden_le
    calc
      (2 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ)
          ≤ (Real.log 2 ^ 2 / (2 * Real.log (n : ℝ))) * (n : ℝ) := by
            have h2a : (2 / 10 : ℝ) * 2 ≤ Real.log 2 ^ 2 := by nlinarith
            have h2b : (2 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) =
                ((2 / 10 : ℝ) * 2 / (2 * Real.log (n : ℝ))) * (n : ℝ) := by
              field_simp
            rw [h2b]
            gcongr
      _ = (n : ℝ) * (Real.log 2 / (2 * Real.log (n : ℝ))) * Real.log 2 := by ring
      _ ≤ (n : ℝ) * (1 / ((Nat.log 2 n : ℝ) + 1)) * Real.log 2 := by gcongr
      _ = (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) * Real.log 2 := by ring
  have hlog4n : Real.log (4 * (n : ℝ)) ≤ (1 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by
    have h4eq : Real.log (4 * (n : ℝ)) = 2 * Real.log 2 + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) hn_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      ring
    have hle2 : Real.log (4 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by linarith
    have hsq2 : 2 * Real.log (n : ℝ) ≤ (1 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    exact hle2.trans hsq2
  have hlhs_sub : (1 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) ≤
      (P : ℝ) / n * ((P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log 2 * log (n : ℝ) * log (P : ℝ)) := by
    have hsub1 : (2 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) -
        (1 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) =
        (1 / 10 : ℝ) * (n : ℝ) / Real.log (n : ℝ) := by ring
    linarith only [hlhs_main, hlog4n, hineq, hsub1]
  by_contra hlt
  push Not at hlt
  set L : ℝ := Real.log (n : ℝ)
  set LL : ℝ := Real.log L
  set X : ℝ := (n : ℝ) ^ (1 + 1 / (104 * LL))
  by_cases hP16 : P < 16
  · have hPm : (P : ℝ) / n *
        ((P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log 2 * L * log (P : ℝ))
        ≤ M * log 2 * L / (n : ℝ) := by
      have h1P := hM_bound P hP16
      have hfac : 0 ≤ log 2 * L / (n : ℝ) := by positivity
      calc
        (P : ℝ) / n * ((P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log 2 * L * log (P : ℝ))
            = ((P : ℝ) * ((P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log (P : ℝ))) * (log 2 * L / (n : ℝ)) := by
              ring
        _ ≤ M * (log 2 * L / (n : ℝ)) := mul_le_mul_of_nonneg_right h1P hfac
        _ = M * log 2 * L / (n : ℝ) := by ring
    have hcontra : M * log 2 * L / (n : ℝ) < (1 / 10 : ℝ) * (n : ℝ) / L := by
      have hML : M * log 2 * L ≤ (M + 1) * L := by
        have : M * log 2 ≤ M + 1 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      have hlt1 : (M + 1) * L / (n : ℝ) < (1 / 10 : ℝ) * (n : ℝ) / L := by
        rw [div_lt_div_iff₀ hn_pos (by linarith)]
        nlinarith [hsq_bound, hM_lt]
      exact lt_of_le_of_lt ((div_le_div_iff_of_pos_right hn_pos).mpr hML) hlt1
    linarith
  · have hP_ge16 : (16 : ℝ) ≤ (P : ℝ) := by
      exact_mod_cast (by omega : 16 ≤ P)
    have hP_le_X : (P : ℝ) ≤ X := hlt.le
    have hX_pos : 0 < X := Real.rpow_pos_of_pos hn_pos _
    have hP_pos : (0 : ℝ) < (P : ℝ) := by linarith
    have hlogP_le : Real.log (P : ℝ) ≤ Real.log X := Real.log_le_log hP_pos hP_le_X
    have hlogP_nonneg : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by linarith)
    have hmono := mono_aux hP_ge16 hP_le_X
    have hexp_nonneg : 0 ≤ X * exp (-log X / (51.9 * log (log X))) := by positivity
    have hrhs_le : (1 / 10 : ℝ) * (n : ℝ) / L ≤
        (X / (n : ℝ)) * (X * exp (-log X / (51.9 * log (log X))) * log 2 * L * log X) := by
      refine hlhs_sub.trans ?_
      have h1 : (P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * log 2 * L * log (P : ℝ) ≤
          X * exp (-log X / (51.9 * log (log X))) * log 2 * L * log X := by
        have ha : (P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * (log 2 * L) ≤
            X * exp (-log X / (51.9 * log (log X))) * (log 2 * L) :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
        have hb : (P : ℝ) * exp (-log (P : ℝ) / (51.9 * log (log (P : ℝ)))) * (log 2 * L) * log (P : ℝ) ≤
            X * exp (-log X / (51.9 * log (log X))) * (log 2 * L) * log X :=
          mul_le_mul ha hlogP_le hlogP_nonneg (by positivity)
        simpa [mul_assoc] using hb
      have h2 : (P : ℝ) / (n : ℝ) ≤ X / (n : ℝ) := div_le_div_of_nonneg_right hP_le_X hn_pos.le
      exact mul_le_mul h2 h1 (by positivity) (by positivity)
    have hlogX_eq : Real.log X = (1 + 1 / (104 * LL)) * L := by
      dsimp [X]
      rw [Real.log_rpow hn_pos]
    have hlogX_pos : 0 < Real.log X := by
      rw [hlogX_eq]
      positivity
    have hlogX_le : Real.log X ≤ 2 * L := by
      rw [hlogX_eq]
      have hsmall : 1 + 1 / (104 * LL) ≤ 2 := by
        have : 0 ≤ 1 / (104 * LL) := by positivity
        have : 1 / (104 * LL) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        linarith
      nlinarith
    have hllX_le : Real.log (Real.log X) ≤ LL + 1 / (104 * LL) := by
      rw [hlogX_eq, Real.log_mul (by positivity) (by linarith)]
      have h1 : Real.log (1 + 1 / (104 * LL)) ≤ 1 / (104 * LL) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (104 * LL) by positivity)
        linarith
      change Real.log (1 + 1 / (104 * LL)) + LL ≤ LL + 1 / (104 * LL)
      linarith
    have h519_pos : 0 < 51.9 * Real.log (Real.log X) := by
      have hL_le_X : L ≤ Real.log X := by
        rw [hlogX_eq]
        have hinv0 : 0 ≤ 1 / (104 * LL) := by positivity
        nlinarith only [hl_ge, hinv0]
      have hll_le_llX : LL ≤ Real.log (Real.log X) := Real.log_le_log (by linarith only [hl_ge]) hL_le_X
      nlinarith only [hll_ge, hll_le_llX]
    have h519_le : 51.9 * Real.log (Real.log X) ≤ 51.95 * LL := by
      have h1 : 51.9 * (1 / (104 * LL)) ≤ 0.05 * LL := by
        have hinv : 1 / (104 * LL) ≤ 0.0005 * LL := by
          rw [div_le_iff₀ (by linarith only [hll_ge])]
          nlinarith only [hll_ge]
        nlinarith only [hinv, hll_ge]
      nlinarith only [hllX_le, h1]
    have hX_split : X / (n : ℝ) * X = (n : ℝ) * exp (L / (52 * LL)) := by
      have h1 : X * X = (n : ℝ) * exp (L / (52 * LL)) * (n : ℝ) := by
        have hex : X = exp ((1 + 1 / (104 * LL)) * L) := by
          dsimp [X]
          rw [Real.rpow_def_of_pos hn_pos, show Real.log (n : ℝ) = L from rfl]
          congr 1
          ring
        have hn_exp : (n : ℝ) = exp L := (Real.exp_log hn_pos).symm
        rw [hex, ← Real.exp_add]
        have heq : (1 + 1 / (104 * LL)) * L + (1 + 1 / (104 * LL)) * L =
            L + L / (52 * LL) + L := by
          field_simp
          ring
        rw [heq, Real.exp_add, Real.exp_add, ← hn_exp]
      calc
        X / (n : ℝ) * X = (X * X) / (n : ℝ) := by ring
        _ = ((n : ℝ) * exp (L / (52 * LL)) * (n : ℝ)) / (n : ℝ) := by rw [h1]
        _ = (n : ℝ) * exp (L / (52 * LL)) := by field_simp
    have hexp_diff : L / (52 * LL) - Real.log X / (51.9 * Real.log (Real.log X)) ≤
        -L / (60000 * LL) := by
      have hL_le_X : L ≤ Real.log X := by
        rw [hlogX_eq]
        have hinv0 : 0 ≤ 1 / (104 * LL) := by positivity
        nlinarith only [hl_ge, hinv0]
      have hquot : L / (51.95 * LL) ≤ Real.log X / (51.9 * Real.log (Real.log X)) := by
        rw [div_le_div_iff₀ (by linarith only [hll_ge]) h519_pos]
        exact mul_le_mul hL_le_X h519_le h519_pos.le hlogX_pos.le
      have hdiff : L / (52 * LL) - L / (51.95 * LL) ≤ -L / (60000 * LL) := by
        have heq1 : L / (52 * LL) - L / (51.95 * LL) =
            -(0.05 / (52 * 51.95)) * (L / LL) := by
          field_simp
          ring
        have heq2 : -L / (60000 * LL) = -(1 / 60000) * (L / LL) := by
          field_simp
        rw [heq1, heq2]
        have hLL_nonneg : 0 ≤ L / LL := div_nonneg (by linarith only [hl_ge]) (by linarith only [hll_ge])
        nlinarith only [hLL_nonneg]
      linarith only [hquot, hdiff]
    have hmain_exp : (1 / 10 : ℝ) * (n : ℝ) / L ≤
        (n : ℝ) * exp (-L / (60000 * LL)) * (2 * L ^ 2) := by
      refine hrhs_le.trans ?_
      have h1 : (X / (n : ℝ)) * (X * exp (-Real.log X / (51.9 * Real.log (Real.log X))) * log 2 * L * log X) =
          (n : ℝ) * (exp (L / (52 * LL)) * exp (-Real.log X / (51.9 * Real.log (Real.log X)))) *
            (log 2 * L * log X) := by
        calc
          (X / (n : ℝ)) * (X * exp (-Real.log X / (51.9 * Real.log (Real.log X))) * log 2 * L * log X)
              = (X / (n : ℝ) * X) * exp (-Real.log X / (51.9 * Real.log (Real.log X))) * (log 2 * L * log X) := by
                ring
          _ = (n : ℝ) * exp (L / (52 * LL)) * exp (-Real.log X / (51.9 * Real.log (Real.log X))) *
                (log 2 * L * log X) := by rw [hX_split]
          _ = (n : ℝ) * (exp (L / (52 * LL)) * exp (-Real.log X / (51.9 * Real.log (Real.log X)))) *
                (log 2 * L * log X) := by ring
      rw [h1]
      have h2 : exp (L / (52 * LL)) * exp (-Real.log X / (51.9 * Real.log (Real.log X))) ≤
          exp (-L / (60000 * LL)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hneg : L / (52 * LL) + -Real.log X / (51.9 * Real.log (Real.log X)) =
            L / (52 * LL) - Real.log X / (51.9 * Real.log (Real.log X)) := by ring
        linarith only [hexp_diff, hneg]
      have h3 : log 2 * L * log X ≤ 2 * L ^ 2 := by
        have h2L : log 2 * L ≤ 1 * L :=
          mul_le_mul_of_nonneg_right (by linarith only [hlog2_lt]) (by linarith only [hl_ge])
        nlinarith only [h2L, hlogX_le, hl_ge, hlogX_pos]
      have h12 : (n : ℝ) * (exp (L / (52 * LL)) * exp (-Real.log X / (51.9 * Real.log (Real.log X)))) ≤
          (n : ℝ) * exp (-L / (60000 * LL)) :=
        mul_le_mul_of_nonneg_left h2 hn_pos.le
      have hlog_prod_nn : 0 ≤ log 2 * L * log X :=
        mul_nonneg (mul_nonneg hlog2_pos.le (by linarith only [hl_ge])) hlogX_pos.le
      exact mul_le_mul h12 h3 hlog_prod_nn (mul_nonneg hn_pos.le (Real.exp_pos _).le)
    have hexp_pos : exp (L / (60000 * LL)) ≤ 20 * L ^ 3 := by
      have hneg : exp (-L / (60000 * LL)) = (exp (L / (60000 * LL)))⁻¹ := by
        rw [show -L / (60000 * LL) = -(L / (60000 * LL)) by ring, Real.exp_neg]
      rw [hneg] at hmain_exp
      have hep : 0 < exp (L / (60000 * LL)) := Real.exp_pos _
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      have hL_ne : L ≠ 0 := by linarith only [hl_ge]
      have hcancel : (1 / 10 : ℝ) / L ≤ (exp (L / (60000 * LL)))⁻¹ * (2 * L ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hmain_exp (inv_nonneg.mpr hn_pos.le)
        have hnn_inv : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn_ne
        have hL1 : (n : ℝ)⁻¹ * ((1 / 10 : ℝ) * (n : ℝ) / L) = (1 / 10 : ℝ) / L := by
          calc
            (n : ℝ)⁻¹ * ((1 / 10 : ℝ) * (n : ℝ) / L)
                = (1 / 10 : ℝ) * ((n : ℝ)⁻¹ * (n : ℝ)) / L := by ring
            _ = (1 / 10 : ℝ) / L := by rw [hnn_inv, mul_one]
        have hR1 : (n : ℝ)⁻¹ * ((n : ℝ) * (exp (L / (60000 * LL)))⁻¹ * (2 * L ^ 2)) =
            (exp (L / (60000 * LL)))⁻¹ * (2 * L ^ 2) := by
          rw [mul_assoc (n : ℝ), inv_mul_cancel_left₀ hn_ne]
        rw [hL1, hR1] at h
        exact h
      rw [← div_eq_inv_mul, le_div_iff₀ hep] at hcancel
      have h20 : exp (L / (60000 * LL)) * (1 / 10 : ℝ) ≤ 2 * L ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_right hcancel (show (0 : ℝ) ≤ L by linarith only [hl_ge])
        have hL2 : (1 / 10 : ℝ) / L * exp (L / (60000 * LL)) * L =
            exp (L / (60000 * LL)) * (1 / 10 : ℝ) := by
          rw [mul_right_comm, div_mul_cancel₀ _ hL_ne, mul_comm]
        rw [hL2] at hmul
        linarith only [hmul, show (2 * L ^ 2) * L = 2 * L ^ 3 by ring]
      linarith only [h20]
    have hlog_ineq : L / (60000 * LL) ≤ Real.log (20 * L ^ 3) := by
      have h := Real.log_le_log (Real.exp_pos _) hexp_pos
      rw [Real.log_exp] at h
      exact h
    have hlog20 : Real.log (20 * L ^ 3) < 4 * LL + 10 := by
      have hL3_ne : L ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith only [hl_ge])
      rw [Real.log_mul (by norm_num) hL3_ne, Real.log_pow]
      have h20 : Real.log 20 ≤ 5 * Real.log 2 := by
        have h := Real.log_le_log (by norm_num) (show (20 : ℝ) ≤ 2 ^ 5 by norm_num)
        rw [Real.log_pow] at h
        norm_num at h
        exact h
      have hcast : ((3 : ℕ) : ℝ) * Real.log L = 3 * LL := by
        norm_num
        rfl
      rw [hcast]
      linarith only [h20, hlog2_lt, hll_ge]
    linarith only [h5_bound, hlog_ineq, hlog20]

end OMA.Erdos977R1H4Proof

theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H4 :=
  OMA.Erdos977R1H4Proof.h4_proof
