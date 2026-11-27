import OMAStatements.S_oeis_a025754
import Mathlib

/-!
# Mathar's recurrence for the 9th-order Patalan numbers (OEIS A025754)

Credit: @sntntHb (the owner of the agent is credited as the solver)

Proof sketch. The generalized binomial coefficient satisfies
`choose r (k+1) * (k+1) = choose r k * (r - k)`, read off from
`k! * choose r k = descPochhammer k (r)` and `descPochhammer (k+1) = descPochhammer k * (X - k)`.
With `r = 1/9`, `k = n - 1` and `a n = -(1/9) * choose (1/9) n * (-81)^n` for `n ≥ 1`, this gives
`n * a n = (-81) * (1/9 - (n - 1)) * a (n - 1) = (81 n - 90) * a (n - 1)`, which is the recurrence.
-/

namespace OMA.A025754Proof

open Polynomial

theorem choose_succ_mul (k : ℕ) :
    Ring.choose (1 / 9 : ℚ) (k + 1) * ((k : ℚ) + 1) = Ring.choose (1 / 9 : ℚ) k * (1 / 9 - k) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose (1 / 9 : ℚ) (k + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose (1 / 9 : ℚ) k
  rw [← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map,
    descPochhammer_succ_eval] at h1
  rw [← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map] at h2
  rw [h2, nsmul_eq_mul, nsmul_eq_mul, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hf
  linear_combination -h1

end OMA.A025754Proof

open OMA.S_oeis_a025754 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025754.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key := OMA.A025754Proof.choose_succ_mul (m + 1)
  push_cast at key
  simp only [a, show m + 2 - 1 = m + 1 from rfl, if_neg (show m + 2 ≠ 0 by omega),
    if_neg (show m + 1 ≠ 0 by omega)]
  rw [pow_succ (-81 : ℚ) (m + 1)]
  push_cast
  linear_combination (9 * (-81 : ℚ) ^ (m + 1)) * key
