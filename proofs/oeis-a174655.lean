import OMAStatements.S_oeis_a174655
import Mathlib

-- Problem: oeis-a174655 (Barker's closed form and g.f.)
-- Credit: @Aijy0264561
-- tail satisfies a recurrence with characteristic polynomial (x-1)^3 (x+1), so
-- 2 tail n = 4(n+3)^2 - 8(n+3) + 9 - (-1)^n; summing gives the closed form of a, and the g.f.
-- identity follows coefficientwise from the closed form and the first seven values.

namespace OMA.A174655proof

open OMA.S_oeis_a174655 PowerSeries

lemma tail_eq (n : ℕ) : 2 * tail n = 4 * ((n : ℤ) + 3) ^ 2 - 8 * ((n : ℤ) + 3) + 9 - (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [tail]
    | 1, _ => simp [tail]
    | 2, _ => simp [tail]
    | 3, _ => simp [tail]
    | m + 4, ih =>
      have h3 := ih (m + 3) (by omega)
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      rw [show tail (m + 4) = 2 * tail (m + 3) - 2 * tail (m + 1) + tail m from rfl]
      push_cast at h3 h1 h0 ⊢
      rw [pow_succ, pow_succ, pow_succ, pow_succ] ; rw [pow_succ, pow_succ, pow_succ] at h3
      rw [pow_succ] at h1
      linear_combination 2 * h3 - 2 * h1 + h0

lemma a_succ (n : ℕ) : a (n + 1) = a n + b (n + 1) := by
  unfold a; rw [Finset.sum_range_succ]

lemma a_closed (n : ℕ) (hn : 2 ≤ n) :
    12 * a n = 3 * (-9 + (-1 : ℤ) ^ n) + 34 * (n : ℤ) - 12 * (n : ℤ) ^ 2 + 8 * (n : ℤ) ^ 3 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [a_succ]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hb : b (k + 2 + 1) = tail k := rfl
    rw [hb]
    have ht := tail_eq k
    push_cast at ih ⊢
    rw [pow_succ, pow_succ, pow_succ] at *
    linear_combination ih + 6 * ht

lemma vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 15 ∧ a 4 = 36 ∧ a 5 = 70 ∧ a 6 = 123 := by
  decide

lemma denom_eq : ((X - 1) ^ 4 * (X + 1) : PowerSeries ℤ) =
    1 - C 3 * X + C 2 * X ^ 2 + C 2 * X ^ 3 - C 3 * X ^ 4 + X ^ 5 := by
  simp only [map_ofNat]; ring

lemma numer_eq : (X * (X ^ 5 - X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 2 * X + 1) : PowerSeries ℤ) =
    X + C 2 * X ^ 2 + C 2 * X ^ 3 + C 3 * X ^ 4 - X ^ 5 + X ^ 6 := by
  simp only [map_ofNat]; ring

lemma coeff_mul_X1 (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n (φ * X) = if 1 ≤ n then coeff (n - 1) φ else 0 := by
  simpa using coeff_mul_X_pow' φ 1 n

lemma coeff_X1 (n : ℕ) : coeff n (X : PowerSeries ℤ) = if n = 1 then 1 else 0 := by
  rw [coeff_X]

theorem a174655 : type_of% @OMA.S_oeis_a174655.main := by
  refine ⟨fun n hn => a_closed n hn, ?_⟩
  rw [mul_comm, denom_eq, numer_eq]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mul_X1, coeff_mk, coeff_X_pow, coeff_C, coeff_X1]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := vals
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have c : ∀ k, k ≤ 6 → k ≤ m + 7 := fun k hk => by omega
    have d : ∀ k, 1 ≤ k → k ≤ 6 → m + 7 ≠ k := fun k h1 h2 => by omega
    have z : ∀ k, k ≤ 6 → m + 7 - k ≠ 0 := fun k hk => by omega
    have s1 : m + 7 - 1 = m + 6 := by omega
    have s2 : m + 7 - 2 = m + 5 := by omega
    have s3 : m + 7 - 3 = m + 4 := by omega
    have s4 : m + 7 - 4 = m + 3 := by omega
    have s5 : m + 7 - 5 = m + 2 := by omega
    have e0 := a_closed (m + 7) (by norm_num)
    have e1 := a_closed (m + 6) (by norm_num)
    have e2 := a_closed (m + 5) (by norm_num)
    have e3 := a_closed (m + 4) (by norm_num)
    have e4 := a_closed (m + 3) (by norm_num)
    have e5 := a_closed (m + 2) (by norm_num)
    generalize a = f at e0 e1 e2 e3 e4 e5 ⊢
    rw [if_pos (c 1 (by norm_num)), if_pos (c 2 (by norm_num)), if_pos (c 3 (by norm_num)),
      if_pos (c 4 (by norm_num)), if_pos (c 5 (by norm_num))]
    rw [if_neg (d 1 (by norm_num) (by norm_num)), if_neg (d 5 (by norm_num) (by norm_num)),
      if_neg (d 6 (by norm_num) (by norm_num))]
    rw [if_pos (c 2 (by norm_num)), if_pos (c 3 (by norm_num)), if_pos (c 4 (by norm_num)),
      if_neg (z 2 (by norm_num)), if_neg (z 3 (by norm_num)), if_neg (z 4 (by norm_num))]
    rw [s1, s2, s3, s4, s5]
    push_cast at e0 e1 e2 e3 e4 e5
    have p : ∀ k : ℕ, (-1 : ℤ) ^ (m + k) = (-1) ^ m * (-1) ^ k := fun k => pow_add _ _ _
    simp only [p] at e0 e1 e2 e3 e4 e5
    norm_num at e0 e1 e2 e3 e4 e5
    linarith

end OMA.A174655proof

theorem OMA.solution : type_of% @OMA.S_oeis_a174655.main := OMA.A174655proof.a174655
