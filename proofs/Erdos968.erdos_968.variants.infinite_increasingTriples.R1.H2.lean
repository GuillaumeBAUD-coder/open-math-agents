import OMAReductions.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1
import Mathlib

/-!
# Chebyshev upper bound for the normalized n-th prime

Proves `OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1.H2`:
eventually `Erdos968.u n ≤ 2 * Real.log (Nat.nth Nat.Prime n)`.
Using `Chebyshev.pi_ge` at `p = Nat.nth Nat.Prime n` (where `p.primeCounting = n + 1`)
gives `p * log 2 ≤ (n + 3) * log p`, and since `2 * log 2 > 1.386`, we have
`(n + 3) ≤ 2 * (n + 1) * log 2` for all `n ≥ 5`.
-/

open Filter Real

theorem OMA.solution :
    OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1.H2 := by
  filter_upwards [eventually_ge_atTop 5] with n hn
  let p := Nat.nth Nat.Prime n
  have hp_prime : p.Prime := Nat.prime_nth_prime n
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpc : p.primeCounting = n + 1 := by
    change Nat.count Nat.Prime (p + 1) = n + 1
    rw [Nat.count_succ, if_pos hp_prime]
    exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)
  have hcheb := Chebyshev.pi_ge p
  rw [div_le_iff₀ hlogp, hpc] at hcheb
  have hlogp1 : Real.log ((p : ℝ) + 1) ≤ 2 * Real.log (p : ℝ) := by
    have hsq : (p : ℝ) + 1 ≤ (p : ℝ) ^ 2 := by nlinarith
    have h := Real.log_le_log (by positivity) hsq
    rwa [Real.log_pow] at h
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold Erdos968.u
  rw [div_le_iff₀ hn1]
  have hcoeff : ((n + 1 : ℕ) : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) * Real.log 2 := by
    push_cast
    nlinarith
  have hmul : (p : ℝ) * Real.log 2 ≤ (2 * Real.log (p : ℝ) * ((n : ℝ) + 1)) * Real.log 2 := by
    calc (p : ℝ) * Real.log 2
        ≤ (((n + 1 : ℕ) : ℝ) + 2) * Real.log (p : ℝ) := by linarith
      _ ≤ (2 * ((n : ℝ) + 1) * Real.log 2) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hcoeff hlogp.le
      _ = (2 * Real.log (p : ℝ) * ((n : ℝ) + 1)) * Real.log 2 := by ring
  exact le_of_mul_le_mul_right hmul (by linarith)
