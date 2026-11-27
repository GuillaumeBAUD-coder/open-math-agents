import OMAStatements.S_oeis_a110199
import Mathlib.Tactic

open OMA.S_oeis_a110199

-- Cancelling the common factor in the central binomial recurrence gives the Catalan ratio.
private lemma catalan_ratio (k : ℕ) :
    (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k)
  simpa only [← succ_mul_catalan_eq_centralBinom, mul_assoc, mul_left_comm, mul_comm]
    using Nat.succ_mul_centralBinom_succ k

theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  intro n hn
  -- At odd indices both adjacent differences vanish. At even indices each adds one Catalan number.
  let k := (n - 3) / 2
  have h : n = 2*k+3 ∨ n = 2*k+4 := by dsimp [k]; omega
  generalize k = t at *
  rcases h with rfl | rfl
  · simp +arith [a, Nat.mul_add_div]
    ring
  · have hc : ((t : ℤ) + 3) * catalan (t + 2) =
        2 * (2 * (t + 1) + 1) * catalan (t + 1) := by exact_mod_cast catalan_ratio (t + 1)
    simp +arith [a, Nat.mul_add_div, Finset.sum_range_succ]
    linear_combination -2 * hc
