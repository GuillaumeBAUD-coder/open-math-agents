import OMAStatements.S_oeis_a092634

-- Problem: A092634: a(n) = 1 - Sum_{k=2..n} k*k!.
-- Upstream: formal-conjectures statements/oeis-a092634.lean:0 (declaration OMA.S_oeis_a092634.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a092634

open OMA.S_oeis_a092634

lemma closed (n : ℕ) : a (n + 1) = 3 - ((n + 2).factorial : ℤ) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have h : a (n + 1 + 1) = a (n + 1) - ((n + 2 : ℕ) : ℤ) * ((n + 2).factorial : ℤ) := by
      unfold a
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    rw [h, ih, Nat.factorial_succ (n + 2)]
    push_cast
    ring

lemma solve : ∀ n : ℕ, 5 ≤ n →
    a n + (-(n : ℤ) - 3) * a (n - 1) + (2 * (n : ℤ) + 1) * a (n - 2) +
      (-(n : ℤ) + 1) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 = (m + 3) + 1 by ring, show m + 3 + 1 - 1 = (m + 2) + 1 by omega,
    show m + 3 + 1 - 2 = (m + 1) + 1 by omega, show m + 3 + 1 - 3 = m + 1 by omega,
    closed, closed, closed, closed]
  rw [show m + 3 + 2 = (m + 2) + 1 + 1 + 1 by ring, show m + 2 + 2 = (m + 2) + 1 + 1 by ring,
    show m + 1 + 2 = (m + 2) + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  ring

end OMA.P_oeis_a092634

theorem OMA.solution : type_of% @OMA.S_oeis_a092634.main := OMA.P_oeis_a092634.solve
