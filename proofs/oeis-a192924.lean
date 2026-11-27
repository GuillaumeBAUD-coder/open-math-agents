import OMAStatements.S_oeis_a192924

namespace OMA.P192924

open Polynomial OMA.S_oeis_a192924

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 => (((n : ℤ) + 2) * (w (n + 1)).1 + (w n).1 + (w n).2,
      ((n : ℤ) + 2) * (w (n + 1)).2 + (w n).1 + 2 * (w n).2)

lemma wrec (n : ℕ) : w (n + 2) = (((n : ℤ) + 2) * (w (n + 1)).1 + (w n).1 + (w n).2,
    ((n : ℤ) + 2) * (w (n + 1)).2 + (w n).1 + 2 * (w n).2) := by
  rw [w]

lemma p_rec (n : ℕ) : p (n + 2) = C ((n : ℤ) + 2) * p (n + 1) + X ^ 2 * p n := by
  rw [p]
  push_cast
  rfl

lemma red : ∀ n : ℕ,
    (∃ s : ℤ[X], p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1)) ∧
    (∃ s : ℤ[X], p (n + 1) = (X ^ 2 - X - 1) * s + (C (w (n + 1)).2 * X + C (w (n + 1)).1)) := by
  intro n
  induction n with
  | zero => exact ⟨⟨0, by simp [w, p]⟩, ⟨0, by simp [w, p]⟩⟩
  | succ n ih =>
    obtain ⟨⟨s0, h0⟩, ⟨s1, h1⟩⟩ := ih
    refine ⟨⟨s1, h1⟩, ?_⟩
    refine ⟨C ((n : ℤ) + 2) * s1 + X ^ 2 * s0 + C (w n).2 * X + C ((w n).1 + (w n).2), ?_⟩
    show p (n + 2) = _
    rw [p_rec, h0, h1, wrec]
    simp only [map_add, map_mul, map_ofNat]
    ring

lemma q_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  norm_num

lemma q_degree : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e, degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow] <;> try rfl
  rw [degree_X_add_C]
  norm_num

lemma rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1) = C (w n).2 * X + C (w n).1 := by
  obtain ⟨s, hs⟩ := (red n).1
  refine (div_modByMonic_unique s _ q_monic ⟨?_, ?_⟩).2
  · rw [hs]; ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma a_eq (n : ℕ) : a n = (w n).1 := by
  unfold a
  rw [rem]; simp

end OMA.P192924

open OMA.S_oeis_a192924 OMA.P192924 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192924.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  have e4 : k + 4 - 4 = k := by omega
  rw [e1, e2, e3, e4]
  simp only [a_eq]
  have h4 : w (k + 4) = _ := wrec (k + 2)
  have h3 : w (k + 3) = _ := wrec (k + 1)
  have h2 : w (k + 2) = _ := wrec k
  rw [h4, h3, h2]
  push_cast
  ring
