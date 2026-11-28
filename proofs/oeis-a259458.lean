import OMAStatements.S_oeis_a259458

-- Problem: A259458: From higher-order arithmetic progressions.
-- Upstream: formal-conjectures statements/oeis-a259458.lean:0 (declaration OMA.S_oeis_a259458.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Both sides satisfy the same first order recurrence: a(k+1) (k+1) (k+3) = a(k) (k+5)^3, and the
coefficient 18 (5)_k^3 / ((3)_k k!) is multiplied by (k+5)^3 / ((k+3) (k+1)) when k increases by one.
The values at k = 0 are both 18. -/

namespace A259458Aux

open OMA.S_oeis_a259458 PowerSeries

theorem rf_succ (c : ℚ) (n : ℕ) : rf c (n + 1) = rf c n * (c + (n : ℚ)) :=
  Finset.prod_range_succ _ _

theorem rf3_pos (n : ℕ) : 0 < rf 3 n :=
  Finset.prod_pos (fun i _ => by positivity)

theorem a_succ (k : ℕ) : a (k + 1) * (((k : ℚ) + 1) * ((k : ℚ) + 3)) = a k * ((k : ℚ) + 5) ^ 3 := by
  unfold a
  have e : k + 1 + 4 = k + 4 + 1 := by ring
  rw [e, Nat.factorial_succ]
  push_cast
  ring

theorem key (n : ℕ) : a n * (rf 3 n * (n.factorial : ℚ)) = 18 * rf 5 n ^ 3 := by
  induction n with
  | zero =>
    simp [a, rf]
    norm_num
  | succ k ih =>
    have s := a_succ k
    rw [rf_succ, rf_succ, Nat.factorial_succ]
    push_cast
    linear_combination (rf 3 k * (k.factorial : ℚ)) * s + ((k : ℚ) + 5) ^ 3 * ih

end A259458Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a259458.main := by
  ext n
  simp only [PowerSeries.coeff_mk]
  have hpos : (0 : ℚ) < OMA.S_oeis_a259458.rf 3 n * (n.factorial : ℚ) :=
    mul_pos (A259458Aux.rf3_pos n) (by positivity)
  rw [eq_div_iff (ne_of_gt hpos)]
  exact A259458Aux.key n
