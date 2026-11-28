import OMAReductions.R_mo_144208_R1

-- Step mo-144208.R1.H2: hypothesis H2 of reduction mo-144208.R1
-- Credit: @futurum-dev

/-! The case `n = 3`: `(1 + 2^a + 3^a)^b = 1 + 2^c + 3^c`. If `c ≤ ab` the left side exceeds
`1 + 2^(ab) + 3^(ab) ≥ 1 + 2^c + 3^c`, so `c > ab`. If `b ≥ 3` then `8` divides the left side
(its base is even) and `2^c`, while `3^c + 1 ≡ 2, 4 (mod 8)`. So `b = 2`. For `a ≥ 2`,
`9(1 + 2^a) ≤ 5·3^a` gives `(1 + 2^a + 3^a)^2 < 3^(2a+1) ≤ 3^c`, impossible; for `a = 1`,
`1 + 2^c + 3^c = 36` gives `c = 3`. -/

namespace OMA.Mo144208H2

theorem three_pow_mod_eight (c : ℕ) : 3 ^ c % 8 = 1 ∨ 3 ^ c % 8 = 3 := by
  induction c with
  | zero => simp
  | succ c ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- `(u + v)^b > u^b + v^b` for positive `u, v` and `b ≥ 2`. -/
theorem pow_add_gt (u v b : ℕ) (hu : 0 < u) (hv : 0 < v) (hb : 2 ≤ b) :
    u ^ b + v ^ b < (u + v) ^ b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  have h := pow_add_pow_le (Nat.zero_le u) (Nat.zero_le v) (show k ≠ 0 by omega)
  have hk : 0 < u * v ^ k := by positivity
  calc u ^ (k + 1) + v ^ (k + 1) < (u + v) * (u ^ k + v ^ k) := by
        rw [pow_succ, pow_succ]; nlinarith [pow_pos hu k, pow_pos hv k]
    _ ≤ (u + v) * (u + v) ^ k := Nat.mul_le_mul_left _ h
    _ = (u + v) ^ (k + 1) := by ring

theorem nine_le (a : ℕ) (ha : 2 ≤ a) : 9 * (1 + 2 ^ a) ≤ 5 * 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih => rw [pow_succ, pow_succ]; omega

theorem case_three (a b c : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (_hc : 0 < c)
    (h : (1 + 2 ^ a + 3 ^ a) ^ b = 1 + 2 ^ c + 3 ^ c) : (a, b, c) = (1, 2, 3) := by
  -- c > a * b
  have hcab : a * b < c := by
    by_contra hle
    push Not at hle
    have h1 : 1 + 2 ^ c + 3 ^ c ≤ 1 + 2 ^ (a * b) + 3 ^ (a * b) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hle
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hle
      omega
    have h2 : (2 ^ a) ^ b + (3 ^ a) ^ b < (2 ^ a + 3 ^ a) ^ b :=
      pow_add_gt _ _ _ (by positivity) (by positivity) hb
    have h3 := pow_add_pow_le (Nat.zero_le 1) (Nat.zero_le (2 ^ a + 3 ^ a)) (show b ≠ 0 by omega)
    rw [← pow_mul, ← pow_mul] at h2
    rw [one_pow, ← add_assoc] at h3
    omega
  -- b = 2
  have hb2 : b = 2 := by
    by_contra hne
    have hb3 : 3 ≤ b := by omega
    have heven : 2 ∣ 1 + 2 ^ a + 3 ^ a := by
      have : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
      have : 3 ^ a % 2 = 1 := by rw [Nat.pow_mod]; norm_num
      omega
    have h8 : 8 ∣ (1 + 2 ^ a + 3 ^ a) ^ b := by
      have := pow_dvd_pow_of_dvd heven b
      exact (pow_dvd_pow 2 hb3).trans this |> fun h => by norm_num at h ⊢; exact h
    have h8' : 8 ∣ 2 ^ c := by
      have : 2 ^ 3 ∣ 2 ^ c := pow_dvd_pow 2 (by nlinarith)
      simpa using this
    rw [h] at h8
    rcases three_pow_mod_eight c with h3 | h3 <;> omega
  subst hb2
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · have : a = 1 := by omega
    subst this
    have h' : 1 + 2 ^ c + 3 ^ c = 36 := by rw [← h]; norm_num
    have hc4 : c < 4 := by
      by_contra hc4
      push Not at hc4
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hc4
      norm_num at this
      linarith [h', Nat.zero_le (2 ^ c)]
    interval_cases c <;> simp_all
  · exfalso
    have h9 := nine_le a ha2
    have h10 : 9 * (1 + 2 ^ a + 3 ^ a) ≤ 14 * 3 ^ a := by omega
    have h11 := Nat.mul_le_mul h10 h10
    have h12 : 0 < 3 ^ a := by positivity
    have hs : (1 + 2 ^ a + 3 ^ a) ^ 2 < 3 * (3 ^ a) ^ 2 := by nlinarith
    have hc' : 3 * (3 ^ a) ^ 2 ≤ 3 ^ c := by
      rw [← pow_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    linarith [h, hs, hc', Nat.zero_le (2 ^ c)]

end OMA.Mo144208H2

theorem OMA.solution : OMA.R_mo_144208_R1.H2 := OMA.Mo144208H2.case_three
