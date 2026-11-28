import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R3
-- Credit: @LAPRAI
-- Bertrand series by Cauchy condensation: 2^k f(2^k) ≤ (k log 2)^(-(1+ε)).

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H2 := by
  intro ε hε
  have hl4 : 1 < Real.log 4 := by
    have := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hll : 0 < Real.log (Real.log 4) := Real.log_pos hl4
  set f : ℕ → ℝ := fun j => ((j : ℝ) * (Real.log ((j : ℝ) * Real.log 4)) ^ (1 + ε))⁻¹ with hf
  show Summable f
  have hpos : ∀ j : ℕ, 0 < j → 0 < Real.log ((j : ℝ) * Real.log 4) := fun j hj =>
    Real.log_pos (by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith)
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hf]
    · have := hpos j hj
      simp only [hf]
      exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg this.le _))
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hLm := hpos m hm
    have hLle : Real.log ((m : ℝ) * Real.log 4) ≤ Real.log ((n : ℝ) * Real.log 4) :=
      Real.log_le_log (mul_pos hm' (by linarith))
        (mul_le_mul_of_nonneg_right hmn' (by linarith))
    simp only [hf]
    apply inv_anti₀ (mul_pos hm' (Real.rpow_pos_of_pos hLm _))
    exact mul_le_mul hmn' (Real.rpow_le_rpow hLm.le hLle (by linarith))
      (Real.rpow_pos_of_pos hLm _).le (Nat.cast_nonneg _)
  rw [← summable_condensed_iff_of_nonneg hf0 hmono]
  refine Summable.of_norm_bounded_eventually_nat
    ((Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 1 + ε by linarith)).mul_left
      ((Real.log 2 ^ (1 + ε))⁻¹)) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = 2 ^ k := by push_cast; ring
  have hlog : Real.log (((2 ^ k : ℕ) : ℝ) * Real.log 4) = k * Real.log 2 + Real.log (Real.log 4) := by
    rw [Real.log_mul (by positivity) (by linarith : (0 : ℝ) < Real.log 4).ne', Nat.cast_pow,
      Real.log_pow]
    push_cast
    ring
  have hA : 0 < (k : ℝ) * Real.log 2 := by positivity
  have hB : (k : ℝ) * Real.log 2 ≤ Real.log (((2 ^ k : ℕ) : ℝ) * Real.log 4) := by
    rw [hlog]; linarith
  have hLpos : 0 < Real.log (((2 ^ k : ℕ) : ℝ) * Real.log 4) := lt_of_lt_of_le hA hB
  rw [Real.norm_of_nonneg (mul_nonneg h2k.le (hf0 _))]
  simp only [hf]
  calc (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ) *
        Real.log (((2 ^ k : ℕ) : ℝ) * Real.log 4) ^ (1 + ε))⁻¹
      = (Real.log (((2 ^ k : ℕ) : ℝ) * Real.log 4) ^ (1 + ε))⁻¹ := by
        rw [hcast, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2k.ne', one_mul]
    _ ≤ (((k : ℝ) * Real.log 2) ^ (1 + ε))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hA _) (Real.rpow_le_rpow hA.le hB (by linarith))
    _ = (Real.log 2 ^ (1 + ε))⁻¹ * ((k : ℝ) ^ (1 + ε))⁻¹ := by
        rw [Real.mul_rpow (by positivity) hl2.le, mul_inv]; ring
