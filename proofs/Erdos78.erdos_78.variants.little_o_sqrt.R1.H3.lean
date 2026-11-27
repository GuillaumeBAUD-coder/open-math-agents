import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Proof of `Erdos78.erdos_78.variants.little_o_sqrt.R1.H3`
-/

open Filter Topology
open scoped Asymptotics

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H3 := by
  refine ⟨fun n => 4 * (n : ℝ) ^ ((2 : ℝ) / 5), ?_, ?_⟩
  · refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn h0
      exfalso
      have hpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      linarith
    · have hlim : Tendsto (fun x : ℝ => 4 * x ^ (-(1 : ℝ) / 10)) atTop (𝓝 0) := by
        simpa [neg_div] using
          (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).const_mul 4
      refine (hlim.comp tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      simp only [Function.comp_apply, Real.sqrt_eq_rpow]
      rw [mul_div_assoc, ← Real.rpow_sub hn0]
      norm_num
  · rw [eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    set k := Nat.log 16 n
    refine ⟨k + 1, (Nat.lt_pow_succ_log_self (by decide : 1 < 16) n).le, ?_⟩
    have hk : 16 ^ k ≤ n := Nat.pow_log_le_self 16 (Nat.pos_iff_ne_zero.mp hn)
    have hnat : (3 ^ k) ^ 5 ≤ n ^ 2 := by
      calc (3 ^ k) ^ 5 = (3 ^ 5) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm k 5]
        _ ≤ (16 ^ 2) ^ k := Nat.pow_le_pow_left (by decide) k
        _ = (16 ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm 2 k]
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hk 2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hreal : ((3 ^ k : ℕ) : ℝ) ^ (5 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact_mod_cast hnat
    have hpow : ((3 ^ k : ℕ) : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := by
      calc ((3 ^ k : ℕ) : ℝ)
          = (((3 ^ k : ℕ) : ℝ) ^ (5 : ℝ)) ^ ((1 : ℝ) / 5) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _)]
            norm_num
        _ ≤ ((n : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 5) :=
            Real.rpow_le_rpow (by positivity) hreal (by norm_num)
        _ = (n : ℝ) ^ ((2 : ℝ) / 5) := by
            rw [← Real.rpow_mul hn0]
            norm_num
    push_cast at hpow
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) :=
      Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    have hle : ((3 ^ (k + 1) + 1 : ℕ) : ℝ) ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / 5) := by
      push_cast
      rw [pow_succ]
      linarith
    exact Nat.cast_le.mp (hle.trans (Nat.le_ceil _))
