import OMAStatements.S_oeis_a192939

namespace OMA.P192939

open Polynomial OMA.S_oeis_a192939

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (2 * ((n : ℤ) + 1) * (w n).1 + (w n).2, (w n).1 + (2 * ((n : ℤ) + 1) + 1) * (w n).2)

lemma p_succ (n : ℕ) : p (n + 1) = p n * (X + C (2 * ((n : ℤ) + 1))) := by
  unfold p
  rw [Finset.prod_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma red (n : ℕ) : ∃ s : ℤ[X],
    p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w, p]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s * (X + C (2 * ((n : ℤ) + 1))) + C (w n).2, ?_⟩
    rw [p_succ, hs]
    simp only [w, map_add, map_mul, map_one, map_ofNat]
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

lemma a_eq (n : ℕ) : a n = (w n).1 := by
  unfold a
  rw [rem]; simp

end OMA.P192939

open OMA.S_oeis_a192939 OMA.P192939 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192939.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2, a_eq, a_eq, a_eq]
  simp only [w]
  push_cast
  ring
