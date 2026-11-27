import OMAStatements.S_oeis_a192745

namespace OMA.P192745

open Polynomial OMA.S_oeis_a192745

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).2 + ((n + 1).factorial : ℤ), (w n).1 + (w n).2)

lemma red (n : ℕ) : ∃ s : ℤ[X],
    p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w, p]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨X * s + C (w n).2, ?_⟩
    rw [p, hs]
    simp only [w, map_add]
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
  obtain ⟨s, hs⟩ := red n
  refine (div_modByMonic_unique s _ q_monic ⟨?_, ?_⟩).2
  · rw [hs]; ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma a_eq (n : ℕ) : a n = (w n).2 := by
  unfold a
  rw [rem, coeff_add, coeff_C_mul, coeff_X_one, coeff_C_of_ne_zero one_ne_zero, mul_one, add_zero]

lemma hrel_u (m : ℕ) : (w (m + 2)).1 = (w (m + 1)).1 + (w m).1
    + ((m : ℤ) + 1) * ((m + 1).factorial : ℤ) := by
  simp only [w]
  push_cast [Nat.factorial_succ]
  ring

lemma hrel_v (m : ℕ) : (w (m + 2)).2 = (w (m + 1)).2 + (w m).2 + ((m + 1).factorial : ℤ) := by
  simp only [w]
  ring

lemma f2 (k : ℕ) : ((k + 2).factorial : ℤ) = ((k : ℤ) + 2) * ((k + 1).factorial : ℤ) := by
  push_cast [Nat.factorial_succ]
  ring

lemma f3 (k : ℕ) : ((k + 3).factorial : ℤ)
    = ((k : ℤ) + 3) * (((k : ℤ) + 2) * ((k + 1).factorial : ℤ)) := by
  push_cast [Nat.factorial_succ]
  ring

end OMA.P192745

open OMA.S_oeis_a192745 OMA.P192745 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192745.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : k + 3 - 2 = k + 1 := by omega
  have e3 : k + 3 - 3 = k := by omega
  rw [e1, e2, e3]
  simp only [a_eq]
  have h1 := hrel_v (k + 1)
  have h0 := hrel_v k
  rw [f2] at h1
  push_cast at h1 h0 ⊢
  linear_combination h1 - ((k : ℤ) + 2) * h0
