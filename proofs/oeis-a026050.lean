import OMAStatements.S_oeis_a026050

-- Problem: A026050: a(n) = (d(n)-r(n))/2, where d = A026049 and r is the periodic sequence with fundamental period (1,0,0,1).
-- Upstream: formal-conjectures statements/oeis-a026050.lean:0 (declaration OMA.S_oeis_a026050.main)
-- Credit: @antonumias24-tech (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Idea: for m >= 0, 6 * d(m+6) = m(m+1)(2m+19) + 126m + 546 (split the dot product at the
-- rotation point). From d(m+7) = d(m+6) + (m+1)(m+7) + 21 one gets the parity of d by
-- induction, so 2 * a(N) + r(N) = d(N) for N >= 7, i.e. 12 * a(m+7) is an explicit cubic in m
-- minus 6 times a 4-periodic 0/1 sequence. The denominator (X^2+1)(X-1)^4 kills cubics (factor
-- (1-X)^4) and the period (1,0,0,1) (factor (1-X)(1+X^2)), so all coefficients from n = 13 on
-- vanish; the coefficients n < 13 are checked by computation.

namespace OMA.H_a026050

open OMA.S_oeis_a026050 PowerSeries

lemma S_closed (m : ℕ) : 6 * ∑ i ∈ Finset.range m, (i + 1) * (i + 7) = m * (m + 1) * (2 * m + 19) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

lemma d_closed (m : ℕ) : 6 * d (m + 6) = m * (m + 1) * (2 * m + 19) + 126 * m + 546 := by
  unfold d
  rw [Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range m, (i + 1) * (if i + 7 ≤ m + 6 then i + 7 else i + 7 - (m + 6))
      = ∑ i ∈ Finset.range m, (i + 1) * (i + 7) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  rw [h1, mul_add, S_closed]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  have e0 : m + 0 + 7 - (m + 6) = 1 := by omega
  have e1 : m + 1 + 7 - (m + 6) = 2 := by omega
  have e2 : m + 2 + 7 - (m + 6) = 3 := by omega
  have e3 : m + 3 + 7 - (m + 6) = 4 := by omega
  have e4 : m + 4 + 7 - (m + 6) = 5 := by omega
  have e5 : m + 5 + 7 - (m + 6) = 6 := by omega
  rw [e0, e1, e2, e3, e4, e5]
  ring

lemma d_step (m : ℕ) : d (m + 7) = d (m + 6) + (m + 1) * (m + 7) + 21 := by
  have h1 := d_closed m
  have h2 := d_closed (m + 1)
  rw [show m + 1 + 6 = m + 7 from rfl] at h2
  linarith

lemma sq_mod_two (x : ℕ) : (x * x) % 2 = x % 2 := by
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · ring_nf; omega
  · ring_nf; omega

lemma d_par (m : ℕ) : d (m + 6) % 2 = if m % 4 = 0 ∨ m % 4 = 1 then 1 else 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 6 = m + 7 by ring, d_step]
    have hs := sq_mod_two (m + 1)
    have : (m + 1) * (m + 7) = (m + 1) * (m + 1) + 6 * (m + 1) := by ring
    rw [this]
    split_ifs at ih ⊢ <;> omega

lemma a_eq (m : ℕ) : 2 * a (m + 7) + (if m % 4 = 0 ∨ m % 4 = 3 then 1 else 0) = d (m + 7) := by
  have hp := d_par (m + 1)
  unfold a r
  rw [show m + 7 - 7 = m by omega]
  rw [show m + 1 + 6 = m + 7 by ring] at hp
  split_ifs at hp ⊢ <;> omega


def rr (m : ℕ) : ℕ := if m % 4 = 0 ∨ m % 4 = 3 then 1 else 0

lemma key (m : ℕ) : 12 * (a (m + 7) : ℤ) =
    ((m : ℤ) + 1) * ((m : ℤ) + 2) * (2 * (m : ℤ) + 21) + 126 * ((m : ℤ) + 1) + 546 - 6 * (rr m : ℤ) := by
  have h1 := a_eq m
  have h2 := d_closed (m + 1)
  rw [show m + 1 + 6 = m + 7 from rfl] at h2
  unfold rr
  split_ifs at h1 ⊢
  all_goals
    have h3 := congrArg (Nat.cast : ℕ → ℤ) h1
    have h4 := congrArg (Nat.cast : ℕ → ℤ) h2
    push_cast at h3 h4 ⊢
    linear_combination 6 * h3 + h4

lemma rr_sum (k : ℕ) : (rr (k + 6) : ℤ) - 4 * rr (k + 5) + 7 * rr (k + 4) - 8 * rr (k + 3) + 7 * rr (k + 2)
    - 4 * rr (k + 1) + rr k = 0 := by
  unfold rr
  split_ifs <;> omega

lemma a7 : a 7 = 59 := by decide
lemma a8 : a 8 = 78 := by decide
lemma a9 : a 9 = 102 := by decide
lemma a10 : a 10 = 132 := by decide
lemma a11 : a 11 = 170 := by decide
lemma a12 : a 12 = 217 := by decide

theorem gf :
    A * ((X ^ 2 + 1) * (X - 1) ^ 4) =
      X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) := by
  have hL : A * ((X ^ 2 + 1) * (X - 1) ^ 4) = X ^ 0 * A - C 4 * (X ^ 1 * A) + C 7 * (X ^ 2 * A)
      - C 8 * (X ^ 3 * A) + C 7 * (X ^ 4 * A) - C 4 * (X ^ 5 * A) + X ^ 6 * A := by
    simp only [map_ofNat]; ring
  have hR : (X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) : ℤ⟦X⟧) =
      C 59 * X ^ 7 - C 158 * X ^ 8 + C 203 * X ^ 9 - C 202 * X ^ 10 + C 145 * X ^ 11 - C 45 * X ^ 12 := by
    simp only [map_ofNat]; ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, A, coeff_mk]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;> simp [a7, a8, a9, a10, a11, a12]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    have c0 : 0 ≤ k + 13 := by omega
    have c1 : 1 ≤ k + 13 := by omega
    have c2 : 2 ≤ k + 13 := by omega
    have c3 : 3 ≤ k + 13 := by omega
    have c4 : 4 ≤ k + 13 := by omega
    have c5 : 5 ≤ k + 13 := by omega
    have c6 : 6 ≤ k + 13 := by omega
    have s0 : k + 13 - 0 = k + 6 + 7 := by omega
    have s1 : k + 13 - 1 = k + 5 + 7 := by omega
    have s2 : k + 13 - 2 = k + 4 + 7 := by omega
    have s3 : k + 13 - 3 = k + 3 + 7 := by omega
    have s4 : k + 13 - 4 = k + 2 + 7 := by omega
    have s5 : k + 13 - 5 = k + 1 + 7 := by omega
    have s6 : k + 13 - 6 = k + 7 := by omega
    have t0 : ¬ (k + 6 + 7 < 7) := by omega
    have t1 : ¬ (k + 5 + 7 < 7) := by omega
    have t2 : ¬ (k + 4 + 7 < 7) := by omega
    have t3 : ¬ (k + 3 + 7 < 7) := by omega
    have t4 : ¬ (k + 2 + 7 < 7) := by omega
    have t5 : ¬ (k + 1 + 7 < 7) := by omega
    have t6 : ¬ (k + 7 < 7) := by omega
    have u7 : ¬ (k + 13 = 7) := by omega
    have u8 : ¬ (k + 13 = 8) := by omega
    have u9 : ¬ (k + 13 = 9) := by omega
    have u10 : ¬ (k + 13 = 10) := by omega
    have u11 : ¬ (k + 13 = 11) := by omega
    have u12 : ¬ (k + 13 = 12) := by omega
    rw [if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6,
      s0, s1, s2, s3, s4, s5, s6, if_neg t0, if_neg t1, if_neg t2, if_neg t3, if_neg t4, if_neg t5,
      if_neg t6, if_neg u7, if_neg u8, if_neg u9, if_neg u10, if_neg u11, if_neg u12]
    have k0 := key k
    have k1 := key (k + 1)
    have k2 := key (k + 2)
    have k3 := key (k + 3)
    have k4 := key (k + 4)
    have k5 := key (k + 5)
    have k6 := key (k + 6)
    have hr := rr_sum k
    push_cast at k0 k1 k2 k3 k4 k5 k6
    apply mul_left_cancel₀ (show (12 : ℤ) ≠ 0 by norm_num)
    linear_combination k6 - 4 * k5 + 7 * k4 - 8 * k3 + 7 * k2 - 4 * k1 + k0 - 6 * hr

end OMA.H_a026050

theorem OMA.solution : type_of% @OMA.S_oeis_a026050.main := by
  exact OMA.H_a026050.gf
