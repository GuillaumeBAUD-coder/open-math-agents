import OMAStatements.S_oeis_a051524

open OMA.S_oeis_a051524

theorem OMA.solution : type_of% @OMA.S_oeis_a051524.main := by
  have key : ∀ n : ℕ, ∃ u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ T n 0 = (-1) ^ n * u ∧
      T n 1 = -(-1) ^ n * v := by
    intro n
    induction n with
    | zero => exact ⟨1, 0, by norm_num, le_rfl, by simp [T], by simp [T]⟩
    | succ n ih =>
      obtain ⟨u, v, hu, hv, h0, h1⟩ := ih
      refine ⟨(n + 6) * u, u + (n + 6) * v, by positivity, by positivity, ?_, ?_⟩
      · rw [show T (n + 1) 0 = -((n + 1 + 5 : ℕ) : ℤ) * T n 0 from rfl, h0]
        push_cast
        ring
      · rw [show T (n + 1) 1 = T n 0 - ((n + 1 + 5 : ℕ) : ℤ) * T n 1 from rfl, h0, h1]
        push_cast
        ring
  intro n
  obtain ⟨u, v, hu, hv, h0, h1⟩ := key n
  have t1 : T (n + 1) 1 = (-1) ^ n * (u + (n + 6) * v) := by
    rw [show T (n + 1) 1 = T n 0 - ((n + 1 + 5 : ℕ) : ℤ) * T n 1 from rfl, h0, h1]
    push_cast
    ring
  have t2 : T (n + 2) 1 = -(-1) ^ n * ((n + 6) * u + (n + 7) * (u + (n + 6) * v)) := by
    rw [show T (n + 2) 1 = T (n + 1) 0 - ((n + 1 + 1 + 5 : ℕ) : ℤ) * T (n + 1) 1 from rfl, t1,
      show T (n + 1) 0 = -((n + 1 + 5 : ℕ) : ℤ) * T n 0 from rfl, h0]
    push_cast
    ring
  have h : ∀ x w : ℤ, 0 ≤ w → x = (-1) ^ n * w ∨ x = -(-1) ^ n * w → |x| = w := by
    rintro x w hw (rfl | rfl) <;> rcases neg_one_pow_eq_or ℤ n with e | e <;>
      simp [e, abs_of_nonneg hw]
  simp only [a, h _ _ (by positivity) (Or.inr t2), h _ _ (by positivity) (Or.inl t1),
    h _ _ hv (Or.inr h1)]
  push_cast
  ring
