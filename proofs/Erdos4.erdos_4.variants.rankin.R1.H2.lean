import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Real
open scoped Topology

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  let c : ℝ := Real.log 2 / 4
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hsmall : ∀ᶠ t : ℝ in atTop, Real.log t ≤ c * Real.sqrt t := by
    filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hc,
      eventually_ge_atTop (1 : ℝ)] with t ht h1
    have hz : 0 ≤ t := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
      abs_of_nonneg (Real.rpow_nonneg hz (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg t)] using ht
  have he : ∀ᶠ x : ℕ in atTop, 2 ≤ x ∧ Real.log x ≤ c * Real.sqrt x :=
    (eventually_ge_atTop (2 : ℕ)).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro x hx
  obtain ⟨hx2, hsmallx⟩ := hN x hx
  let X : ℝ := x
  have hX2 : 2 ≤ X := by exact_mod_cast hx2
  have hX0 : 0 ≤ X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hshift : Real.log (X + 1) ≤ 2 * Real.log X := by
    calc
      Real.log (X + 1) ≤ Real.log (2 * X) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log X := Real.log_mul (by norm_num) (by linarith)
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2]
  have hs0 := Real.sqrt_nonneg X
  have hs2 := Real.sq_sqrt hX0
  have hsle : Real.sqrt X ≤ X := by
    have h := Real.sqrt_le_sqrt (show X ≤ X ^ 2 by nlinarith [sq_nonneg (X - 1)])
    rwa [Real.sqrt_sq hX0] at h
  have hm := mul_le_mul_of_nonneg_right hsmallx hs0
  change Real.log X * Real.sqrt X ≤ (c * Real.sqrt X) * Real.sqrt X at hm
  rw [mul_assoc, ← pow_two, hs2] at hm
  have hlog_le : Real.log X ≤ c * X := hsmallx.trans (mul_le_mul_of_nonneg_left hsle hc.le)
  have hdiv : Real.sqrt X ≤ (X * Real.log 2 - Real.log (X + 1)) / Real.log X := by
    apply (le_div_iff₀ hlog).2
    have heq : Real.log 2 = 4 * c := by dsimp [c]; ring
    rw [heq]
    nlinarith [mul_nonneg hc.le hX0]
  have hpi : Real.sqrt X ≤ (Nat.primeCounting x : ℝ) := hdiv.trans (Chebyshev.pi_ge x)
  have hsquare := pow_le_pow_left₀ hs0 hpi 2
  rw [hs2] at hsquare
  exact_mod_cast hsquare
