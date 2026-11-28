import OMAStatements.S_oeis_a001653

namespace OeisA001653Proof

open OMA.S_oeis_a001653

private lemma a_eq (n : ℕ) : (a n) ^ 2 - 6 * a n * a (n + 1) + (a (n + 1)) ^ 2 = -4 := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hrec : a (k + 2) = 6 * a (k + 1) - a k := rfl
    rw [hrec]
    linear_combination ih

private lemma no_sol_two (m₂ : ℤ) : m₂ ^ 2 - 12 * m₂ + 8 ≠ 0 := by
  intro h
  have hsq : (m₂ - 6) ^ 2 = 28 := by linarith
  rcases le_or_gt (m₂ - 6) (-6) with h1 | h1
  · nlinarith
  · rcases le_or_gt (m₂ - 6) 5 with h2 | h2 <;> nlinarith

private lemma no_sol_three (m₂ : ℤ) : m₂ ^ 2 - 18 * m₂ + 13 ≠ 0 := by
  intro h
  have hsq : (m₂ - 9) ^ 2 = 68 := by linarith
  rcases le_or_gt (m₂ - 9) (-9) with h1 | h1
  · nlinarith
  · rcases le_or_gt (m₂ - 9) 8 with h2 | h2 <;> nlinarith

private lemma no_sol_four (m₂ : ℤ) : m₂ ^ 2 - 24 * m₂ + 20 ≠ 0 := by
  intro h
  have hsq : (m₂ - 12) ^ 2 = 124 := by linarith
  rcases le_or_gt (m₂ - 12) (-12) with h1 | h1
  · nlinarith
  · rcases le_or_gt (m₂ - 12) 11 with h2 | h2 <;> nlinarith

private lemma sol_imp_exists : ∀ (k : ℕ) (m₁ m₂ : ℤ), m₁.toNat = k →
    0 < m₁ → m₁ < m₂ → m₁ ^ 2 - 6 * m₁ * m₂ + m₂ ^ 2 = -4 →
    ∃ n : ℕ, m₁ = a n ∧ m₂ = a (n + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m₁ m₂ hk hm1 hlt heq
    by_cases h1 : m₁ = 1
    · subst h1
      have hfac : (m₂ - 1) * (m₂ - 5) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · exact ⟨0, rfl, by change m₂ = 5; linarith⟩
    · set m₀ : ℤ := 6 * m₁ - m₂
      have hprod : m₀ * m₂ = m₁ ^ 2 + 4 := by
        dsimp [m₀]
        linarith
      have hm0_pos : 0 < m₀ := by nlinarith
      have hm0_lt : m₀ < m₁ := by
        by_contra hge
        push Not at hge
        have hm1_le4 : m₁ ≤ 4 := by nlinarith
        have hm1_ge2 : 2 ≤ m₁ := by omega
        interval_cases m₁
        · exact no_sol_two m₂ (by linarith)
        · exact no_sol_three m₂ (by linarith)
        · exact no_sol_four m₂ (by linarith)
      have heq0 : m₀ ^ 2 - 6 * m₀ * m₁ + m₁ ^ 2 = -4 := by
        dsimp [m₀]
        linear_combination heq
      have hlt_nat : m₀.toNat < k := by omega
      obtain ⟨n, hn0, hn1⟩ := ih m₀.toNat hlt_nat m₀ m₁ rfl hm0_pos hm0_lt heq0
      refine ⟨n + 1, hn1, ?_⟩
      have hrec : a (n + 2) = 6 * a (n + 1) - a n := rfl
      rw [hrec, ← hn0, ← hn1]
      dsimp [m₀]
      ring

theorem main_proof :
    ∀ m₁ m₂ : ℤ, 0 < m₁ → m₁ < m₂ →
      (m₁ ^ 2 - 6 * m₁ * m₂ + m₂ ^ 2 = -4 ↔ ∃ n : ℕ, m₁ = a n ∧ m₂ = a (n + 1)) := by
  intro m₁ m₂ hm1 hlt
  constructor
  · intro heq
    exact sol_imp_exists m₁.toNat m₁ m₂ rfl hm1 hlt heq
  · rintro ⟨n, rfl, rfl⟩
    exact a_eq n

end OeisA001653Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001653.main :=
  OeisA001653Proof.main_proof
