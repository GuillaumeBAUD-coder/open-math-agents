import OMAStatements.S_oeis_a097967

-- Problem: A097967: a(n) = Sum_{k=1..n} (P(n,k) + C(n,k)).
-- Upstream: formal-conjectures statements/oeis-a097967.lean:0 (declaration OMA.S_oeis_a097967.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Q(n) = Sum_{k=0..n} P(n,k) satisfies Q(n+1) = (n+1) Q(n) + 1 and a(n) = Q(n) + 2^n - 2; the recurrence is then a polynomial identity.

open OMA.S_oeis_a097967 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097967.main := by
  have bridge : ∀ (f : ℕ → ℤ) (n : ℕ),
      ∑ k ∈ Finset.range (n + 1), f k = f 0 + ∑ k ∈ Finset.Icc 1 n, f k := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      ring
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℤ,
      ∀ n, Q n = ∑ k ∈ Finset.range (n + 1), (n.descFactorial k : ℤ) := ⟨_, fun _ => rfl⟩
  have hqs : ∀ n : ℕ, Q (n + 1) = ((n : ℤ) + 1) * Q n + 1 := by
    intro n
    rw [hQ, hQ, Finset.sum_range_succ' (fun k => ((n + 1).descFactorial k : ℤ)) (n + 1),
      Finset.mul_sum]
    simp only [Nat.succ_descFactorial_succ, Nat.descFactorial_zero]
    push_cast
    rfl
  have ha : ∀ n : ℕ, a n = Q n + 2 ^ n - 2 := by
    intro n
    have h1 := bridge (fun k => (n.descFactorial k : ℤ)) n
    have h2 := bridge (fun k => (n.choose k : ℤ)) n
    have h3 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    simp only [Nat.descFactorial_zero, Nat.choose_zero_right, Nat.cast_one] at h1 h2
    rw [hQ]
    unfold a
    rw [Finset.sum_add_distrib]
    linarith
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [ha, hqs, Nat.add_sub_cancel, show m + 5 - 1 = m + 4 by omega,
    show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
    show m + 5 - 4 = m + 1 by omega]
  push_cast
  ring
