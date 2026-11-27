import OMAStatements.S_oeis_a052227

-- Problem: A052227: a(n) = (4*n+1)*binomial(3*n,n)/(2*n+1).
-- Upstream: formal-conjectures statements/oeis-a052227.lean:0 (declaration OMA.S_oeis_a052227.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a052227

open OMA.S_oeis_a052227

/-- binomial(3(k+1), k+1) in terms of binomial(3k, k). -/
lemma ratio (k : ℕ) : 2 * ((k : ℚ) + 1) * (2 * k + 1) * ((3 * (k + 1)).choose (k + 1) : ℚ) =
    3 * (3 * (k : ℚ) + 2) * (3 * k + 1) * ((3 * k).choose k : ℚ) := by
  have e1 := Nat.add_one_mul_choose_eq (3 * k) k
  have e2 := Nat.choose_mul_succ_eq (3 * k + 1) (k + 1)
  have e3 := Nat.choose_mul_succ_eq (3 * k + 2) (k + 1)
  rw [show 3 * k + 1 + 1 - (k + 1) = 2 * k + 1 by omega] at e2
  rw [show 3 * k + 2 + 1 - (k + 1) = 2 * k + 2 by omega] at e3
  have q1 : ((3 * k + 1 : ℕ) : ℚ) * ((3 * k).choose k : ℚ) =
      ((3 * k + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) := by exact_mod_cast e1
  have q2 : ((3 * k + 1).choose (k + 1) : ℚ) * ((3 * k + 1 + 1 : ℕ) : ℚ) =
      ((3 * k + 1 + 1).choose (k + 1) : ℚ) * ((2 * k + 1 : ℕ) : ℚ) := by exact_mod_cast e2
  have q3 : ((3 * k + 2).choose (k + 1) : ℚ) * ((3 * k + 2 + 1 : ℕ) : ℚ) =
      ((3 * k + 2 + 1).choose (k + 1) : ℚ) * ((2 * k + 2 : ℕ) : ℚ) := by exact_mod_cast e3
  rw [show 3 * k + 1 + 1 = 3 * k + 2 by ring] at q2
  rw [show 3 * k + 2 + 1 = 3 * (k + 1) by ring] at q3
  push_cast at q1 q2 q3 ⊢
  linear_combination (-(2 * (k : ℚ) + 1)) * q3 + (-3 * ((k : ℚ) + 1)) * q2 +
    (-3 * (3 * (k : ℚ) + 2)) * q1

lemma solve : ∀ n : ℕ, 2 ≤ n →
    8 * (n : ℚ) * (2 * n + 1) * a n + 6 * (-8 * (n : ℚ) ^ 2 - 25 * n + 13) * a (n - 1) -
      45 * (3 * (n : ℚ) - 4) * (3 * n - 5) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have r1 := ratio m
  have r2 := ratio (m + 1)
  have hB1 : ((3 * (m + 1)).choose (m + 1) : ℚ) =
      3 * (3 * (m : ℚ) + 2) * (3 * m + 1) * ((3 * m).choose m : ℚ) /
        (2 * ((m : ℚ) + 1) * (2 * m + 1)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination r1
  have hB2 : ((3 * (m + 2)).choose (m + 2) : ℚ) =
      3 * (3 * ((m : ℚ) + 1) + 2) * (3 * ((m : ℚ) + 1) + 1) * ((3 * (m + 1)).choose (m + 1) : ℚ) /
        (2 * (((m : ℚ) + 1) + 1) * (2 * ((m : ℚ) + 1) + 1)) := by
    rw [eq_div_iff (by positivity)]
    push_cast at r2
    rw [show m + 1 + 1 = m + 2 by ring] at r2
    linear_combination r2
  unfold a
  push_cast
  rw [hB2, hB1]
  field_simp
  ring

end OMA.P_oeis_a052227

theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := OMA.P_oeis_a052227.solve
