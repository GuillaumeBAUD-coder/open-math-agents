import OMAStatements.S_oeis_a192250

namespace OMA.P192250

open Polynomial OMA.S_oeis_a192250

/-- Coordinates of the reduction of `x^n` in the basis `1, x`. -/
def e : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((e n).2, (e n).1 + (e n).2)

/-- Coordinates of the reduction of `p n` in the basis `1, x`. -/
def w : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((w n).1 + ((n + 1).centralBinom : ℤ) * (e (n + 1)).1,
      (w n).2 + ((n + 1).centralBinom : ℤ) * (e (n + 1)).2)

lemma w_succ (n : ℕ) : w (n + 1) = ((w n).1 + ((n + 1).centralBinom : ℤ) * (e (n + 1)).1,
    (w n).2 + ((n + 1).centralBinom : ℤ) * (e (n + 1)).2) := by rw [w]

lemma e_add_two (n : ℕ) : e (n + 2) = ((e (n + 1)).1 + (e n).1, (e (n + 1)).2 + (e n).2) := by
  simp only [e]
  ext <;> simp <;> ring

lemma redX (n : ℕ) : ∃ s : ℤ[X],
    (X : ℤ[X]) ^ n = (X ^ 2 - X - 1) * s + (C (e n).2 * X + C (e n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [e]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s * X + C (e n).2, ?_⟩
    rw [pow_succ, hs]
    simp only [e, map_add]
    ring

lemma p_succ (n : ℕ) : p (n + 1) = p n + C ((n + 1).centralBinom : ℤ) * X ^ (n + 1) := by
  unfold p
  rw [Finset.sum_range_succ]

lemma red (n : ℕ) : ∃ s : ℤ[X],
    p n = (X ^ 2 - X - 1) * s + (C (w n).2 * X + C (w n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w, p]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := redX (n + 1)
    refine ⟨s + C ((n + 1).centralBinom : ℤ) * t, ?_⟩
    rw [p_succ, hs, ht, w_succ]
    simp only [map_add, map_mul]
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

lemma b_eq (m : ℕ) : a (m + 1) = (w m).1 := by
  unfold a
  have e : m + 1 - 1 = m := by omega
  rw [e]
  rw [rem]; simp

lemma cb (n : ℕ) : ((n : ℤ) + 1) * ((n + 1).centralBinom : ℤ)
    = 2 * (2 * (n : ℤ) + 1) * (n.centralBinom : ℤ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

end OMA.P192250

open OMA.S_oeis_a192250 OMA.P192250 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192250.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3]
  have i0 : a (k + 4) = (w (k + 3)).1 := b_eq (k + 3)
  have i1 : a (k + 3) = (w (k + 2)).1 := b_eq (k + 2)
  have i2 : a (k + 2) = (w (k + 1)).1 := b_eq (k + 1)
  have i3 : a (k + 1) = (w k).1 := b_eq k
  rw [i0, i1, i2, i3]
  have d3 : (w (k + 3)).1 = (w (k + 2)).1 + ((k + 3).centralBinom : ℤ) * (e (k + 3)).1 := by
    have h : w (k + 3) = _ := w_succ (k + 2)
    rw [h]
  have d2 : (w (k + 2)).1 = (w (k + 1)).1 + ((k + 2).centralBinom : ℤ) * (e (k + 2)).1 := by
    have h : w (k + 2) = _ := w_succ (k + 1)
    rw [h]
  have d1 : (w (k + 1)).1 = (w k).1 + ((k + 1).centralBinom : ℤ) * (e (k + 1)).1 := by
    have h : w (k + 1) = _ := w_succ k
    rw [h]
  have hf : (e (k + 3)).1 = (e (k + 2)).1 + (e (k + 1)).1 := by
    have h : e (k + 3) = _ := e_add_two (k + 1)
    rw [h]
  have h1 : ((k : ℤ) + 3) * ((k + 3).centralBinom : ℤ)
      = 2 * (2 * (k : ℤ) + 5) * ((k + 2).centralBinom : ℤ) := by
    have := cb (k + 2)
    push_cast at this
    linarith
  have h2 : ((k : ℤ) + 2) * ((k + 2).centralBinom : ℤ)
      = 2 * (2 * (k : ℤ) + 3) * ((k + 1).centralBinom : ℤ) := by
    have := cb (k + 1)
    push_cast at this
    linarith
  push_cast
  linear_combination (((k : ℤ) + 3) * ((k : ℤ) + 2)) * d3
    + (-2 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 5)) * d2
    + (-4 * (2 * (k : ℤ) + 5) * (2 * (k : ℤ) + 3)) * d1
    + (((k : ℤ) + 2) * (e (k + 3)).1) * h1
    + (2 * (2 * (k : ℤ) + 5) * (e (k + 1)).1) * h2
    + (2 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 5) * ((k + 2).centralBinom : ℤ)) * hf
