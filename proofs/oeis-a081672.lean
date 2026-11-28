import OMAStatements.S_oeis_a081672

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: the powers of 2 satisfy the recurrence on their own. For the central binomial part
-- only two terms survive (by parity of n) and both cases reduce to
-- (m+1) * centralBinom (m+1) = 2 * (2m+1) * centralBinom m (Nat.succ_mul_centralBinom_succ).

namespace OMA.Sol_oeis_a081672

lemma cb (m : ℕ) : ((m + 1 : ℕ) : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℕ)
    = 2 * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℕ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  exact_mod_cast h

end OMA.Sol_oeis_a081672

open OMA.S_oeis_a081672 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081672.main := by
  intro n hn
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 4 ∨ n = 2 * j + 5 := ⟨(n - 4) / 2, by omega⟩
  · have e1 : 2 * j + 4 - 1 = 2 * j + 3 := by omega
    have e2 : 2 * j + 4 - 2 = 2 * (j + 1) := by omega
    have e3 : 2 * j + 4 - 3 = 2 * j + 1 := by omega
    rw [e1, e2, e3]
    simp only [a, show 2 * j + 4 ≠ 0 by omega, show 2 * j + 3 ≠ 0 by omega,
      show 2 * (j + 1) ≠ 0 by omega, show 2 * j + 1 ≠ 0 by omega, if_false,
      show (2 * j + 4) % 2 = 0 by omega, show (2 * j + 3) % 2 = 1 by omega,
      show (2 * (j + 1)) % 2 = 0 by omega, show (2 * j + 1) % 2 = 1 by omega, if_true,
      show (2 * j + 4) / 2 = j + 2 by omega, show (2 * (j + 1)) / 2 = j + 1 by omega,
      one_ne_zero]
    have h := OMA.Sol_oeis_a081672.cb (j + 1)
    rw [show 2 * (j + 1 + 1) = 2 * j + 4 by ring] at h
    push_cast at h ⊢
    rw [show (2 : ℤ) ^ (2 * j + 4) = 8 * 2 ^ (2 * j + 1) by ring,
      show (2 : ℤ) ^ (2 * j + 3) = 4 * 2 ^ (2 * j + 1) by ring,
      show (2 : ℤ) ^ (2 * (j + 1)) = 2 * 2 ^ (2 * j + 1) by ring]
    linear_combination 2 * h
  · have e1 : 2 * j + 5 - 1 = 2 * (j + 2) := by omega
    have e2 : 2 * j + 5 - 2 = 2 * j + 3 := by omega
    have e3 : 2 * j + 5 - 3 = 2 * (j + 1) := by omega
    rw [e1, e2, e3]
    simp only [a, show 2 * j + 5 ≠ 0 by omega, show 2 * j + 3 ≠ 0 by omega,
      show 2 * (j + 2) ≠ 0 by omega, show 2 * (j + 1) ≠ 0 by omega, if_false,
      show (2 * j + 5) % 2 = 1 by omega, show (2 * j + 3) % 2 = 1 by omega,
      show (2 * (j + 2)) % 2 = 0 by omega, show (2 * (j + 1)) % 2 = 0 by omega, if_true,
      show (2 * (j + 2)) / 2 = j + 2 by omega, show (2 * (j + 1)) / 2 = j + 1 by omega,
      one_ne_zero]
    have h := OMA.Sol_oeis_a081672.cb (j + 1)
    push_cast at h ⊢
    rw [show (2 : ℤ) ^ (2 * j + 5) = 8 * 2 ^ (2 * j + 2) by ring,
      show (2 : ℤ) ^ (2 * (j + 2)) = 4 * 2 ^ (2 * j + 2) by ring,
      show (2 : ℤ) ^ (2 * j + 3) = 2 * 2 ^ (2 * j + 2) by ring,
      show (2 : ℤ) ^ (2 * (j + 1)) = 2 ^ (2 * j + 2) by ring]
    linear_combination -4 * h
