import OMAReductions.R_Erdos392_erdos_392_variants_lower_R1
import Mathlib

/-! # Lower half of Erdős 392 (factors at most n)

If `n! = ∏ a i` with `t + 1` factors, each at most `n`, then `n! ≤ n ^ (t + 1)`.
The exponential series gives `n ^ n / n! ≤ exp n`, hence
`n log n ≤ n + (t + 1) log n`, which rearranges to `n - n / log n ≤ t + 1`. -/

open scoped Nat

theorem OMA.solution : OMA.R_Erdos392_erdos_392_variants_lower_R1.H1 := by
  unfold OMA.R_Erdos392_erdos_392_variants_lower_R1.H1
  intro n hn t a hprod hle
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hfac : n ! ≤ n ^ (t + 1) := by
    rw [hprod]
    calc ∏ i, a i ≤ n ^ (Finset.univ : Finset (Fin (t + 1))).card :=
          Finset.prod_le_pow_card _ _ _ (fun i _ => hle i)
      _ = n ^ (t + 1) := by simp
  have hfacR : ((n ! : ℕ) : ℝ) ≤ (n : ℝ) ^ (t + 1) := by exact_mod_cast hfac
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hexp : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp _ hnpos.le n
  have hfpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n : ℝ) ^ n ≤ Real.exp n * (n : ℝ) ^ (t + 1) := by
    rw [div_le_iff₀ hfpos] at hexp
    calc (n : ℝ) ^ n ≤ Real.exp n * (n ! : ℝ) := by linarith
      _ ≤ Real.exp n * (n : ℝ) ^ (t + 1) := by gcongr
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
    Real.log_pow] at h2
  push_cast at h2
  have h3 : (n : ℝ) - (t + 1) ≤ n / Real.log n := by
    rw [le_div_iff₀ hL]
    nlinarith
  linarith
