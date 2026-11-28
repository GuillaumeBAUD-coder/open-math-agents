import OMAStatements.S_oeis_a192744

namespace OMA.S_oeis_a192744

open Polynomial

private lemma hq_deg : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  have h1 : (X ^ 2 : ℤ[X]).degree = 2 := degree_X_pow 2
  have h2 : (X + 1 : ℤ[X]).degree < (X ^ 2 : ℤ[X]).degree := by
    rw [h1]
    calc (X + 1 : ℤ[X]).degree
        ≤ max (X : ℤ[X]).degree (1 : ℤ[X]).degree := degree_add_le _ _
      _ ≤ max 1 0 := max_le_max degree_X_le degree_one_le
      _ < 2 := by decide
  have hq : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [hq, degree_sub_eq_left_of_degree_lt h2, h1]

private lemma hq_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  rw [Monic, leadingCoeff, natDegree_eq_of_degree_eq_some hq_deg]
  simp [coeff_X_pow, coeff_X, coeff_one]

private lemma linear_degree_lt (u v : ℤ) :
    (C u + C v * X : ℤ[X]).degree < (X ^ 2 - X - 1 : ℤ[X]).degree := by
  rw [hq_deg]
  calc (C u + C v * X : ℤ[X]).degree
      ≤ max (C u : ℤ[X]).degree (C v * X : ℤ[X]).degree := degree_add_le _ _
    _ ≤ max 0 1 := by
        apply max_le_max
        · exact degree_C_le
        · calc (C v * X : ℤ[X]).degree
              ≤ (C v : ℤ[X]).degree + (X : ℤ[X]).degree := degree_mul_le _ _
            _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
            _ = 1 := by decide
    _ < 2 := by decide

private def ab : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((ab n).2 + ((n + 1).factorial : ℤ), (ab n).1 + (ab n).2)

private lemma p_decomp (n : ℕ) :
    ∃ s : ℤ[X], (C (ab n).1 + C (ab n).2 * X) + (X ^ 2 - X - 1) * s = p n := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp [ab, p]
  | succ n ih =>
    rcases ih with ⟨s, hs⟩
    refine ⟨X * s + C (ab n).2, ?_⟩
    rw [p, ← hs]
    simp only [ab, map_add]
    ring

private lemma p_mod (n : ℕ) :
    p n %ₘ (X ^ 2 - X - 1) = C (ab n).1 + C (ab n).2 * X := by
  rcases p_decomp n with ⟨s, hs⟩
  exact (div_modByMonic_unique s (C (ab n).1 + C (ab n).2 * X) hq_monic
    ⟨hs, linear_degree_lt _ _⟩).2

private lemma a_eq (n : ℕ) : a n = (ab n).1 := by
  rw [a, p_mod]
  simp [coeff_X]

private lemma a_step (k : ℕ) :
    a (k + 2) - a (k + 1) - a k = ((k : ℤ) + 1) * ((k + 1).factorial : ℤ) := by
  have hf : ((k + 2).factorial : ℤ) = ((k : ℤ) + 2) * ((k + 1).factorial : ℤ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  simp only [a_eq, ab]
  rw [hf]
  ring

private theorem main_proved :
    (∀ n : ℕ, 4 ≤ n →
      a n + (-(n : ℤ) - 2) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) + 3 * a (n - 3)
        + (-(n : ℤ) + 2) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      (-(n : ℤ) + 2) * a n + ((n : ℤ) ^ 2 - (n : ℤ) - 1) * a (n - 1)
        + (-(n : ℤ) ^ 2 + 3 * (n : ℤ) - 3) * a (n - 2) - ((n : ℤ) - 1) ^ 2 * a (n - 3) = 0) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h1 : k + 4 - 1 = k + 3 := by omega
    have h2 : k + 4 - 2 = k + 2 := by omega
    have h3 : k + 4 - 3 = k + 1 := by omega
    have h4 : k + 4 - 4 = k := by omega
    rw [h1, h2, h3, h4]
    have hs0 := a_step k
    have hs1 := a_step (k + 1)
    have hs2 := a_step (k + 2)
    have hf2 : ((k + 2).factorial : ℤ) = ((k : ℤ) + 2) * ((k + 1).factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hf3 : ((k + 3).factorial : ℤ) = ((k : ℤ) + 3) * ((k + 2).factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2] at hs1
    rw [hf3, hf2] at hs2
    push_cast at hs1 hs2 ⊢
    linear_combination hs2 - ((k : ℤ) + 5) * hs1 + ((k : ℤ) + 2) * hs0
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have h1 : k + 3 - 1 = k + 2 := by omega
    have h2 : k + 3 - 2 = k + 1 := by omega
    have h3 : k + 3 - 3 = k := by omega
    rw [h1, h2, h3]
    have hs0 := a_step k
    have hs1 := a_step (k + 1)
    have hf2 : ((k + 2).factorial : ℤ) = ((k : ℤ) + 2) * ((k + 1).factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2] at hs1
    push_cast at hs1 ⊢
    linear_combination (-((k : ℤ) + 1)) * hs1 + ((k : ℤ) + 2) ^ 2 * hs0

end OMA.S_oeis_a192744

theorem OMA.solution : type_of% @OMA.S_oeis_a192744.main :=
  OMA.S_oeis_a192744.main_proved
