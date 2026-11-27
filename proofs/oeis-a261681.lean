import OMAStatements.S_oeis_a261681

-- Problem: A261681: a(n) = 2^n + binomial(n, floor(n/2)) - 1.
-- Upstream: formal-conjectures statements/oeis-a261681.lean:0 (declaration OMA.S_oeis_a261681.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a261681

open OMA.S_oeis_a261681

/-- The central binomial coefficient recurrence: (n+1) c(n) = 2 c(n-1) + 4 (n-1) c(n-2). -/
lemma central_rec (m : ℕ) :
    ((m + 2 + 1 : ℕ) : ℤ) * ((m + 2).choose ((m + 2) / 2) : ℤ) =
      2 * ((m + 1).choose ((m + 1) / 2) : ℤ) + 4 * ((m + 1 : ℕ) : ℤ) * (m.choose (m / 2) : ℤ) := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · -- m = 2k
    rw [show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k / 2 = k by omega]
    have e1 := Nat.choose_mul_succ_eq (2 * k) k
    have e2 := Nat.add_one_mul_choose_eq (2 * k + 1) k
    rw [show 2 * k + 1 - k = k + 1 by omega] at e1
    have q1 : ((2 * k).choose k : ℤ) * ((2 * k + 1 : ℕ) : ℤ) =
        ((2 * k + 1).choose k : ℤ) * ((k + 1 : ℕ) : ℤ) := by exact_mod_cast e1
    have q2 : ((2 * k + 1 + 1 : ℕ) : ℤ) * ((2 * k + 1).choose k : ℤ) =
        ((2 * k + 1 + 1).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) := by exact_mod_cast e2
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at q2
    push_cast at q1 q2 ⊢
    nlinarith [q1, q2]
  · -- m = 2k+1
    rw [show (2 * k + 1 + 2) / 2 = k + 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (2 * k + 1) / 2 = k by omega]
    have e1 := Nat.add_one_mul_choose_eq (2 * k + 1) k
    have e2 := Nat.choose_mul_succ_eq (2 * k + 2) (k + 1)
    rw [show 2 * k + 2 + 1 - (k + 1) = k + 2 by omega] at e2
    have q1 : ((2 * k + 1 + 1 : ℕ) : ℤ) * ((2 * k + 1).choose k : ℤ) =
        ((2 * k + 1 + 1).choose (k + 1) : ℤ) * ((k + 1 : ℕ) : ℤ) := by exact_mod_cast e1
    have q2 : ((2 * k + 2).choose (k + 1) : ℤ) * ((2 * k + 2 + 1 : ℕ) : ℤ) =
        ((2 * k + 2 + 1).choose (k + 1) : ℤ) * ((k + 2 : ℕ) : ℤ) := by exact_mod_cast e2
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring] at q1
    rw [show 2 * k + 2 + 1 = 2 * k + 1 + 2 by ring] at q2
    push_cast at q1 q2 ⊢
    nlinarith [q1, q2]

lemma solve : ∀ n : ℕ, 4 ≤ n →
    -((n : ℤ) + 1) * ((n : ℤ) - 4) * a n + (3 * (n : ℤ) ^ 2 - 9 * n - 8) * a (n - 1) +
      2 * ((n : ℤ) ^ 2 - 9 * n + 16) * a (n - 2) + 4 * (-3 * (n : ℤ) ^ 2 + 18 * n - 25) * a (n - 3) +
      8 * ((n : ℤ) - 3) ^ 2 * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  have r0 := central_rec (m + 2)
  have r1 := central_rec (m + 1)
  have r2 := central_rec m
  rw [show m + 2 + 2 = m + 4 by ring, show m + 2 + 1 = m + 3 by ring] at r0
  rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at r1
  unfold a
  rw [show m + 4 = m + 3 + 1 by ring, show m + 3 = m + 2 + 1 by ring,
    show m + 2 = m + 1 + 1 by ring] at *
  simp only [pow_succ] at *
  push_cast at r0 r1 r2 ⊢
  linear_combination (-((m : ℤ) + 4 - 4)) * r0 + (3 * ((m : ℤ) + 4) - 11) * r1 +
    (-2 * ((m : ℤ) + 4 - 3)) * r2

end OMA.P_oeis_a261681

theorem OMA.solution : type_of% @OMA.S_oeis_a261681.main := OMA.P_oeis_a261681.solve
