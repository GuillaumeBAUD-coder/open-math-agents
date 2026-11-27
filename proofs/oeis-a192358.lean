import OMAStatements.S_oeis_a192358

namespace OMA.P192358

open Polynomial OMA.S_oeis_a192358

/-- Coordinates of `(φ + 3)^n` in the basis `1, φ` where `φ^2 = φ + 1`. -/
def w1 : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (3 * (w1 n).1 + (w1 n).2, (w1 n).1 + 4 * (w1 n).2)

/-- Coordinates of `(φ - 3)^n` in the basis `1, φ`. -/
def w2 : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (-3 * (w2 n).1 + (w2 n).2, (w2 n).1 - 2 * (w2 n).2)

lemma pow1 (n : ℕ) : ∃ s : ℚ[X],
    (X + C 3 : ℚ[X]) ^ n = (X ^ 2 - X - 1) * s + (C (w1 n).2 * X + C (w1 n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w1]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s * (X + C 3) + C (w1 n).2, ?_⟩
    rw [pow_succ, hs]
    simp only [w1, map_add, map_mul, map_ofNat]
    ring

lemma pow2 (n : ℕ) : ∃ s : ℚ[X],
    (X - C 3 : ℚ[X]) ^ n = (X ^ 2 - X - 1) * s + (C (w2 n).2 * X + C (w2 n).1) := by
  induction n with
  | zero => exact ⟨0, by simp [w2]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s * (X - C 3) + C (w2 n).2, ?_⟩
    rw [pow_succ, hs]
    simp only [w2, map_add, map_mul, map_sub, map_neg, map_ofNat]
    ring

lemma q_monic : (X ^ 2 - X - 1 : ℚ[X]).Monic := by
  have e : (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  norm_num

lemma q_degree : (X ^ 2 - X - 1 : ℚ[X]).degree = 2 := by
  have e : (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + C 1) := by simp; ring
  rw [e, degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow] <;> try rfl
  rw [degree_X_add_C]
  norm_num

lemma rem (n : ℕ) : p n %ₘ (X ^ 2 - X - 1)
    = C (((w1 n).2 + (w2 n).2) / 2) * X + C (((w1 n).1 + (w2 n).1) / 2) := by
  obtain ⟨s1, h1⟩ := pow1 n
  obtain ⟨s2, h2⟩ := pow2 n
  refine (div_modByMonic_unique (C (1 / 2) * (s1 + s2)) _ q_monic ⟨?_, ?_⟩).2
  · have hc : ∀ x y : ℚ, (C ((x + y) / 2) : ℚ[X]) = C (1 / 2) * (C x + C y) := by
      intro x y
      rw [← map_add, ← map_mul]
      congr 1
      ring
    unfold p
    rw [h1, h2, hc, hc]
    ring
  · rw [q_degree]
    exact lt_of_le_of_lt (degree_linear_le) (by norm_num)

lemma coeff0 (n : ℕ) : (p n %ₘ (X ^ 2 - X - 1)).coeff 0 = ((w1 n).1 + (w2 n).1) / 2 := by
  rw [rem]; simp

lemma coeff1 (n : ℕ) : (p n %ₘ (X ^ 2 - X - 1)).coeff 1 = ((w1 n).2 + (w2 n).2) / 2 := by
  rw [rem]; simp

lemma r1 (n : ℕ) : (w1 (n + 2)).1 = 7 * (w1 (n + 1)).1 - 11 * (w1 n).1 ∧
    (w1 (n + 2)).2 = 7 * (w1 (n + 1)).2 - 11 * (w1 n).2 := by
  simp only [w1]; constructor <;> ring

lemma r2 (n : ℕ) : (w2 (n + 2)).1 = -5 * (w2 (n + 1)).1 - 5 * (w2 n).1 ∧
    (w2 (n + 2)).2 = -5 * (w2 (n + 1)).2 - 5 * (w2 n).2 := by
  simp only [w2]; constructor <;> ring

end OMA.P192358

open OMA.S_oeis_a192358 OMA.P192358 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192358.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  unfold a
  have e0 : k + 5 - 1 = k + 4 := by omega
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 5 - 2 - 1 = k + 2 := by omega
  have e3 : k + 5 - 3 - 1 = k + 1 := by omega
  have e4 : k + 5 - 4 - 1 = k := by omega
  rw [e0, e1, e2, e3, e4]
  simp only [coeff1]
  have a1 := (r1 (k + 2)).2
  have a2 := (r1 (k + 1)).2
  have a3 := (r1 k).2
  have b1 := (r2 (k + 2)).2
  have b2 := (r2 (k + 1)).2
  have b3 := (r2 k).2
  linarith
