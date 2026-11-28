import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1

-- Credit: first proof by Jonas Whidden (adapted from kimihiro64/Robin1984, Apache-2.0);
-- shorter proof by @conormcfarland

/-! Split the primes up to `b` into those up to `s` and the rest. For `p ≤ s` the term
`log p / (s² log s)` is below both arguments of the `min`; for `p > s` the term `p⁻²` is. Both
comparisons reduce to `p² log p` versus `s² log s`. -/

open Finset Real

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1.H3 := by
  intro H s b hH hs hsb hD
  have hS := Real.log_pos hs
  have key (p : ℕ) (hp : p.Prime) : log p / (s ^ 2 * log s) ≤ log p / (H * log H) ∧
      ((p : ℝ) ≤ s → log p / (s ^ 2 * log s) ≤ (p : ℝ)⁻¹ ^ 2) ∧
      (s ≤ p → (p : ℝ)⁻¹ ^ 2 ≤ log p / (s ^ 2 * log s)) := by
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hl := Real.log_pos h1
    refine ⟨div_le_div_of_nonneg_left hl.le (mul_pos (by linarith) (Real.log_pos hH)) hD,
      fun h => ?_, fun h => ?_⟩
    · rw [div_le_iff₀ (by positivity), inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul (pow_le_pow_left₀ (by linarith) h 2) (Real.log_le_log (by linarith) h)
        hl.le (by positivity)]
    · rw [le_div_iff₀ (by positivity), inv_pow, inv_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul (pow_le_pow_left₀ (by linarith) h 2) (Real.log_le_log (by linarith) h)
        hS.le (by positivity)]
  rw [Chebyshev.theta_eq_sum_primesLE, sum_div,
    ← sum_sdiff (Nat.primesLE_mono (Nat.floor_mono hsb))]
  have hI : Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊s⌋₊ = (Ioc ⌊s⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime <;> simp [Nat.mem_primesLE, hp] <;> omega
  rw [hI]
  refine (add_le_add (sum_le_sum fun p hp => ?_) (sum_le_sum fun p hp => ?_)).trans (add_comm _ _).le
  · have hp' := Nat.prime_of_mem_primesLE hp
    exact le_min (key p hp').1
      ((key p hp').2.1 ((Nat.le_floor_iff (by linarith)).1 (Nat.le_of_mem_primesLE hp)))
  · obtain ⟨hp, hp'⟩ := mem_filter.1 hp
    exact le_min (((key p hp').2.2 ((Nat.floor_lt (by linarith)).1 (mem_Ioc.1 hp).1).le).trans
      (key p hp').1) le_rfl
