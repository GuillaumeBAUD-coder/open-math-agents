import OMAStatements.S_oeis_a185020

namespace OMA.S_oeis_a185020



/-- `(n + 2) c(n+1) = 2 (2n+1) c(n)`. -/
lemma catalan_step (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.succ_mul_centralBinom_succ n
  have h : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * Nat.centralBinom (n + 1) := by
          rw [← h1]
      _ = 2 * (2 * n + 1) * Nat.centralBinom n := h3
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by rw [← h2]; ring
  have h' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1) h
  exact_mod_cast h'

/-- Mathar's recurrence, for every `n ≥ 2`. -/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) :
    (n : ℤ) * (n + 1) * a n - 4 * n * (2 * n - 1) * a (n - 1)
      - 8 * (2 * n - 1) * (2 * n - 3) * a (n - 2) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, a]
  have h1 := catalan_step m
  have h2 := catalan_step (m + 1)
  have hs : s (m + 2 + 1) = 2 * s (m + 2) + 2 * s (m + 1) := rfl
  rw [hs]
  push_cast at h1 h2 ⊢
  linear_combination ((m + 2 : ℤ) * (2 * s (m + 2) + 2 * s (m + 1))) * h2
    + (4 * (2 * (m : ℤ) + 3) * s (m + 1)) * h1

/-- Controls: the first listed terms 1, 2, 12, 80, 616, 5040. -/
example : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 12 ∧ a 3 = 80 ∧ a 4 = 616 ∧ a 5 = 5040 := by
  simp only [a, catalan_eq_centralBinom_div, Nat.centralBinom]
  decide

end OMA.S_oeis_a185020

theorem OMA.solution : type_of% @OMA.S_oeis_a185020.main :=
  fun n hn => OMA.S_oeis_a185020.conjecture n hn
