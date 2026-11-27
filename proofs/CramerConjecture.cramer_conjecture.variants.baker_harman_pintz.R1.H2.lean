import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1
import Mathlib

open Finset Filter Real Asymptotics ArithmeticFunction
open scoped Topology

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H2 := by
  unfold OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H2
  have small : (fun x : ℝ => x.sqrt) =o[atTop] fun x : ℝ => x^(0.525:ℝ) := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · apply (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<0.025)).congr'
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      change x^(-(0.025:ℝ)) = x.sqrt / x^(0.525:ℝ)
      rw [sqrt_eq_rpow, ← rpow_sub hx]
      norm_num
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      exact fun h => ((rpow_pos_of_pos hx _).ne' h).elim
  apply IsBigO.trans_isLittleO _ (small.comp_tendsto tendsto_natCast_atTop_atTop)
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  apply IsBigO.of_bound (C * sqrt 5)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with x hx
  have hx' : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hpow : (x:ℝ)^(0.525:ℝ) ≤ x := by
    simpa using (rpow_le_rpow_of_exponent_le hx' (by norm_num : (0.525:ℝ) ≤ 1))
  have hceil : ⌈2*(x:ℝ)^(0.525:ℝ)⌉₊ ≤ 2*x := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  have hsub : ((Ico x (x+2*⌈2*(x:ℝ)^(0.525:ℝ)⌉₊)).filter (fun d => ¬ d.Prime)) ⊆
      (Ioc 0 (5*x)).filter (fun d => ¬ d.Prime) := by
    intro d hd
    obtain ⟨hd, hp⟩ := mem_filter.mp hd
    obtain ⟨hl,hu⟩ := mem_Ico.mp hd
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩,hp⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => (Λ d:ℝ)) hsub
    (fun _ _ _ => vonMangoldt_nonneg)
  have hg := hC ((5*x:ℕ):ℝ)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at hg
  change ‖∑ d ∈ _, (Λ d:ℝ)‖ ≤ _ * ‖sqrt (x:ℝ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun _ _ => vonMangoldt_nonneg)),
    Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _)]
  push_cast at hg
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 5), ← mul_assoc] at hg
  exact hs.trans hg
