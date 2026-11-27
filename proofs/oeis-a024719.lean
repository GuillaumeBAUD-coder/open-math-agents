import OMAStatements.S_oeis_a024719

-- Problem: A024719: a(n) = (1/3)*(2 + Sum_{k=0..n} C(3k,k)).
-- Upstream: formal-conjectures statements/oeis-a024719.lean:0 (declaration OMA.S_oeis_a024719.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a024719

open OMA.S_oeis_a024719

lemma diff (m : ℕ) : a (m + 1) - a m = ((3 * (m + 1)).choose (m + 1) : ℚ) / 3 := by
  unfold a
  rw [Finset.sum_range_succ (n := m + 1)]
  ring

lemma ratio (m : ℕ) : 2 * ((m : ℚ) + 2) * (2 * m + 3) * ((3 * (m + 2)).choose (m + 2) : ℚ) =
    3 * (3 * (m : ℚ) + 5) * (3 * m + 4) * ((3 * (m + 1)).choose (m + 1) : ℚ) := by
  -- three one-step moves: C(3m+3, m+1) -> C(3m+4, m+2) -> C(3m+5, m+2) -> C(3m+6, m+2)
  have e1 := Nat.add_one_mul_choose_eq (3 * m + 3) (m + 1)
  have e2 := Nat.choose_mul_succ_eq (3 * m + 4) (m + 2)
  have e3 := Nat.choose_mul_succ_eq (3 * m + 5) (m + 2)
  rw [show 3 * m + 4 + 1 - (m + 2) = 2 * m + 3 by omega] at e2
  rw [show 3 * m + 5 + 1 - (m + 2) = 2 * m + 4 by omega] at e3
  have q1 : ((3 * m + 3 + 1 : ℕ) : ℚ) * ((3 * m + 3).choose (m + 1) : ℚ) =
      ((3 * m + 3 + 1).choose (m + 1 + 1) : ℚ) * ((m + 1 + 1 : ℕ) : ℚ) := by exact_mod_cast e1
  have q2 : ((3 * m + 4).choose (m + 2) : ℚ) * ((3 * m + 4 + 1 : ℕ) : ℚ) =
      ((3 * m + 4 + 1).choose (m + 2) : ℚ) * ((2 * m + 3 : ℕ) : ℚ) := by exact_mod_cast e2
  have q3 : ((3 * m + 5).choose (m + 2) : ℚ) * ((3 * m + 5 + 1 : ℕ) : ℚ) =
      ((3 * m + 5 + 1).choose (m + 2) : ℚ) * ((2 * m + 4 : ℕ) : ℚ) := by exact_mod_cast e3
  rw [show 3 * m + 3 + 1 = 3 * m + 4 by ring, show m + 1 + 1 = m + 2 by ring] at q1
  rw [show 3 * m + 4 + 1 = 3 * m + 5 by ring] at q2
  rw [show 3 * m + 5 + 1 = 3 * (m + 2) by ring] at q3
  rw [show 3 * (m + 1) = 3 * m + 3 by ring]
  push_cast at q1 q2 q3 ⊢
  linear_combination (-(2 * (m : ℚ) + 3)) * q3 + (-3 * ((m : ℚ) + 2)) * q2 +
    (-3 * (3 * (m : ℚ) + 5)) * q1

lemma solve : ∀ n : ℕ, 2 ≤ n →
    2 * (n : ℚ) * (2 * n - 1) * a n + (-31 * (n : ℚ) ^ 2 + 29 * n - 6) * a (n - 1) +
      3 * (3 * (n : ℚ) - 1) * (3 * n - 2) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have d1 := diff (m + 1)
  have d0 := diff m
  have r := ratio m
  rw [show m + 1 + 1 = m + 2 by ring] at d1
  push_cast
  linear_combination (2 * ((m : ℚ) + 2) * (2 * (m : ℚ) + 3)) * d1 -
    (3 * (3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 4)) * d0 + (1 / 3 : ℚ) * r

end OMA.P_oeis_a024719

theorem OMA.solution : type_of% @OMA.S_oeis_a024719.main := OMA.P_oeis_a024719.solve
