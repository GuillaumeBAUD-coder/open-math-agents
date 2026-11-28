import OMAStatements.S_oeis_a001653

-- Problem: A001653: Numbers k such that 2*k^2 - 1 is a square.
-- Upstream: formal-conjectures statements/oeis-a001653.lean:0 (declaration OMA.S_oeis_a001653.main)
-- Credit: @buzzchain (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Method: Vieta descent (m1, m2) -> (6*m1 - m2, m1), which preserves the form and strictly
-- decreases m1 as long as m1 >= 2; the only solution with m1 = 1 is (1, 5) = (a 0, a 1).

open OMA.S_oeis_a001653

theorem OMA.a_rec (n : ℕ) : a (n + 1 + 1) = 6 * a (n + 1) - a n := rfl

theorem OMA.a_inv (n : ℕ) : a n ^ 2 - 6 * a n * a (n + 1) + a (n + 1) ^ 2 = -4 := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [OMA.a_rec k]
    linear_combination ih

theorem OMA.desc : ∀ N : ℕ, ∀ m₁ m₂ : ℤ, 0 < m₁ → m₁ ≤ (N : ℤ) → m₁ < m₂ →
    m₁ ^ 2 - 6 * m₁ * m₂ + m₂ ^ 2 = -4 → ∃ n : ℕ, m₁ = a n ∧ m₂ = a (n + 1) := by
  intro N
  induction N with
  | zero =>
    intro m₁ m₂ h0 hN
    omega
  | succ k ih =>
    intro m₁ m₂ h0 hN h12 he
    rcases eq_or_lt_of_le (show (1 : ℤ) ≤ m₁ by omega) with h1 | h1
    · subst h1
      have h5 : (m₂ - 1) * (m₂ - 5) = 0 := by linear_combination he
      rcases mul_eq_zero.mp h5 with h | h
      · omega
      · have h6 : m₂ = 5 := by omega
        subst h6
        exact ⟨0, by decide, by decide⟩
    · have hm2 : 0 < m₂ := by omega
      have hA : m₂ < 6 * m₁ := by
        by_contra hc
        have hc' : 0 ≤ m₂ - 6 * m₁ := by omega
        nlinarith [mul_nonneg hm2.le hc', sq_nonneg m₁]
      have hB : 5 * m₁ < m₂ := by
        by_contra hc
        have h1' : 0 ≤ m₂ - m₁ := by omega
        have h2' : 0 ≤ 5 * m₁ - m₂ := by omega
        have h3' : 0 ≤ m₁ - 2 := by omega
        have h4' : 0 ≤ m₁ + 2 := by omega
        nlinarith [mul_nonneg h1' h2', mul_nonneg h3' h4']
      obtain ⟨n, hn1, hn2⟩ := ih (6 * m₁ - m₂) m₁ (by omega) (by omega) (by omega)
        (by linear_combination he)
      refine ⟨n + 1, hn2, ?_⟩
      have hr := OMA.a_rec n
      linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a001653.main := by
  intro m₁ m₂ h0 h12
  constructor
  · intro he
    exact OMA.desc m₁.toNat m₁ m₂ h0 (by omega) h12 he
  · rintro ⟨n, rfl, rfl⟩
    exact OMA.a_inv n
