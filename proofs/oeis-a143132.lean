import OMAStatements.S_oeis_a143132

-- Problem: A143132: Binomial transform of [1, 5, 15, 35, 70, 0, 0, 0, ...].
-- Upstream: formal-conjectures statements/oeis-a143132.lean:0 (declaration OMA.S_oeis_a143132.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a143132

open OMA.S_oeis_a143132

/-- The terms with `k > 4` vanish, so `a (m + 1)` is a five-term sum. -/
lemma a_succ (m : ℕ) : a (m + 1) = 1 + 5 * m.choose 1 + 15 * m.choose 2 + 35 * m.choose 3 +
    70 * m.choose 4 := by
  unfold a
  rw [Nat.add_sub_cancel]
  have h1 : ∑ k ∈ Finset.range (m + 1), m.choose k * b k =
      ∑ k ∈ Finset.range (m + 6), m.choose k * b k := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have h2 : ∑ k ∈ Finset.range 5, m.choose k * b k =
      ∑ k ∈ Finset.range (m + 6), m.choose k * b k := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx
      simp only [Finset.mem_range, not_lt] at hx
      unfold b
      rw [if_neg (by omega), mul_zero]
  rw [h1, ← h2]
  have c6 : Nat.choose 6 4 = 15 := by decide
  have c7 : Nat.choose 7 4 = 35 := by decide
  have c8 : Nat.choose 8 4 = 70 := by decide
  simp [Finset.sum_range_succ, b, c6, c7, c8]
  ring

lemma choose2_mod (m : ℕ) : m.choose 2 % 2 = if m % 4 = 2 ∨ m % 4 = 3 then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    rw [Nat.choose_one_right] at h
    rw [h]
    split_ifs at ih ⊢ <;> omega

lemma f_mod (m : ℕ) : a (m + 1) % 10 = if m % 4 = 0 then 1 else 6 := by
  induction m with
  | zero => simp [a_succ]
  | succ m ih =>
    have e : a (m + 1 + 1) = a (m + 1) + 5 + 15 * m + 35 * m.choose 2 + 70 * m.choose 3 := by
      rw [a_succ, a_succ, Nat.choose_succ_succ (m) 0, Nat.choose_succ_succ m 1,
        Nat.choose_succ_succ m 2, Nat.choose_succ_succ m 3]
      simp only [Nat.choose_zero_right, Nat.choose_one_right]
      ring
    have hc := choose2_mod m
    rw [e]
    split_ifs at ih hc ⊢ <;> omega

lemma solve : ∀ n : ℕ, 1 ≤ n → a n % 10 = if n % 4 = 1 then 1 else 6 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [f_mod]
  have : (m % 4 = 0) ↔ ((m + 1) % 4 = 1) := by omega
  simp only [this]

end OMA.P_oeis_a143132

theorem OMA.solution : type_of% @OMA.S_oeis_a143132.main := OMA.P_oeis_a143132.solve
