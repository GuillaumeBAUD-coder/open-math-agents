import OMAStatements.S_oeis_a093345

-- Problem: A093345: a(n) = n! * {1 + Sum[i=1..n, 1/i*Sum(j=0..i-1, 1/j!)]}.
-- Upstream: formal-conjectures statements/oeis-a093345.lean:0 (declaration OMA.S_oeis_a093345.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(k+2) = (2k+3) a(k+1) - (k+1)^2 a(k) + 1 for all k; the conjecture is the difference of two such lines.

open OMA.S_oeis_a093345 in
theorem OMA.solution : type_of% @OMA.S_oeis_a093345.main := by
  have h1 : ∀ k : ℕ, a (k + 1) = ((k : ℚ) + 1) * a k
      + (k.factorial : ℚ) * ∑ j ∈ Finset.range (k + 1), 1 / (j.factorial : ℚ) := by
    intro k
    have hk : ((k : ℚ) + 1) * (1 / ((k : ℚ) + 1)) = 1 := mul_one_div_cancel (by positivity)
    unfold a
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), Nat.factorial_succ]
    push_cast
    linear_combination
      ((k.factorial : ℚ) * ∑ j ∈ Finset.range (k + 1), 1 / (j.factorial : ℚ)) * hk
  have h2 : ∀ k : ℕ,
      a (k + 2) = (2 * (k : ℚ) + 3) * a (k + 1) - ((k : ℚ) + 1) ^ 2 * a k + 1 := by
    intro k
    have hf : ((k + 1).factorial : ℚ) * (1 / ((k + 1).factorial : ℚ)) = 1 :=
      mul_one_div_cancel (by positivity)
    have hfac : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have e := h1 (k + 1)
    rw [Finset.sum_range_succ, show k + 1 + 1 = k + 2 by omega] at e
    rw [e]
    push_cast
    linear_combination hf - ((k : ℚ) + 1) * h1 k
      + (∑ j ∈ Finset.range (k + 1), 1 / (j.factorial : ℚ)) * hfac
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have E1 := h2 (m + 1)
  have E0 := h2 m
  rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at E1
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast at E1 E0 ⊢
  linear_combination E1 - E0
