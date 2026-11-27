import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R2

-- Sylvester 1888: no odd perfect number is divisible by 105.
-- Original Lean proof of the classical theorem. Write n = 3^a 5^b 7^c m with m coprime to 105 and a, b, c >= 1.
-- The divisor sum is multiplicative, sigma(n) = 2n and n is odd, so sigma(n) is not divisible by 4; but 4 divides
-- 1 + 3 + ... + 3^a for odd a and 8 divides 1 + 7 + ... + 7^c for odd c, so a and c are even, hence at least 2.
-- Then sigma(n) / n >= (13/9)(6/5)(57/49) = 4446/2205 > 2, a contradiction.
-- A classical theorem, not progress on the odd perfect number problem.

namespace OMA.Sylvester

open ArithmeticFunction Finset

lemma geom' (c : ℕ) : ∀ i : ℕ, (∑ k ∈ range (i + 1), (c + 1) ^ k) * c + 1 = (c + 1) ^ (i + 1) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (c + 1) ^ (i + 1 + 1) = (c + 1) ^ (i + 1) * (c + 1) := pow_succ _ _
    rw [Finset.sum_range_succ, e]
    nlinarith [ih]

lemma geom (p : ℕ) (hp : 1 ≤ p) (i : ℕ) : (∑ k ∈ range (i + 1), p ^ k) * (p - 1) + 1 = p ^ (i + 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
  simpa using geom' c i

/-- `S p a = 1 + p + ... + p^a`, the divisor sum of `p^a`. -/
def S (p a : ℕ) : ℕ := ∑ i ∈ range (a + 1), p ^ i

lemma S_succ (p a : ℕ) : S p (a + 1) = p * S p a + 1 := by
  unfold S
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ']

lemma S_upper (p a : ℕ) (hp : 1 ≤ p) : S p a * (p - 1) + 1 = p * p ^ a := by
  have h := geom p hp a
  rw [pow_succ'] at h
  exact h

lemma S_lower (p k : ℕ) : ∀ d : ℕ, S p k * p ^ (k + d) ≤ S p (k + d) * p ^ k := by
  intro d
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    rw [← add_assoc, S_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_right p ih, Nat.zero_le (p ^ k)]

lemma S_odd_dvd (p : ℕ) : ∀ m : ℕ, (p + 1) ∣ S p (2 * m + 1) := by
  intro m
  induction m with
  | zero =>
    have h : S p (2 * 0 + 1) = p + 1 := by
      simp [S, Finset.sum_range_succ]
      ring
    rw [h]
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e, S_succ, S_succ]
    obtain ⟨t, ht⟩ := ih
    exact ⟨p * p * t + 1, by rw [ht]; ring⟩

lemma S_parity (p a : ℕ) (hp : p % 2 = 1) : S p a % 2 = (a + 1) % 2 := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
    rw [S_succ]
    have h1 : (p * S p a) % 2 = S p a % 2 := by
      rw [Nat.mul_mod, hp]
      simp
    omega

lemma sigma_pp (p a : ℕ) (hp : p.Prime) : sigma 1 (p ^ a) = S p a :=
  sigma_one_apply_prime_pow hp

lemma le_sigma (m : ℕ) (hm : 0 < m) : m ≤ sigma 1 m := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self m hm.ne')

/-- Sylvester 1888: an odd number divisible by `3`, `5` and `7` is not perfect. -/
theorem sylvester (n : ℕ) (hodd : Odd n) (hs : sigma 1 n = 2 * n) : ¬ 105 ∣ n := by
  intro h105
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hn0 : n ≠ 0 := by omega
  have p5 : Nat.Prime 5 := by norm_num
  have p7 : Nat.Prime 7 := by norm_num
  -- split off the powers of 3, 5 and 7
  obtain ⟨a, n1, h3n1, hn1⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hn10 : n1 ≠ 0 := by
    rintro rfl
    simp at hn1
    exact hn0 hn1
  obtain ⟨b, n2, h5n2, hn2'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn10 5 (by norm_num)
  have hn20 : n2 ≠ 0 := by
    rintro rfl
    simp at hn2'
    exact hn10 hn2'
  obtain ⟨c, m, h7m, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn20 7 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    exact hn20 hm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn1
    exact h3n1 (hn1 ▸ (by omega : 3 ∣ n))
  have h5n1 : 5 ∣ n1 := by
    have h5 : 5 ∣ 3 ^ a * n1 := hn1 ▸ (by omega : 5 ∣ n)
    exact (Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_right a (by decide : Nat.Coprime 5 3))).mp h5
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hn2'
    exact h5n2 (hn2' ▸ h5n1)
  have h7n1 : 7 ∣ n1 := by
    have h7 : 7 ∣ 3 ^ a * n1 := hn1 ▸ (by omega : 7 ∣ n)
    exact (Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_right a (by decide : Nat.Coprime 7 3))).mp h7
  have h7n2 : 7 ∣ n2 := by
    have h7 : 7 ∣ 5 ^ b * n2 := hn2' ▸ h7n1
    exact (Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_right b (by decide : Nat.Coprime 7 5))).mp h7
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hm
    exact h7m (hm ▸ h7n2)
  -- the divisor sum factors
  have c3 : Nat.Coprime (3 ^ a) n1 :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3n1)
  have c5 : Nat.Coprime (5 ^ b) n2 :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd p5).mpr h5n2)
  have c7 : Nat.Coprime (7 ^ c) m :=
    Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd p7).mpr h7m)
  have hform : n = 3 ^ a * (5 ^ b * (7 ^ c * m)) := by rw [hn1, hn2', hm]
  have hsig : S 3 a * (S 5 b * (S 7 c * sigma 1 m)) = 2 * (3 ^ a * (5 ^ b * (7 ^ c * m))) := by
    rw [← sigma_pp 3 a Nat.prime_three, ← sigma_pp 5 b p5, ← sigma_pp 7 c p7,
      ← isMultiplicative_sigma.map_mul_of_coprime c7, ← hm,
      ← isMultiplicative_sigma.map_mul_of_coprime c5, ← hn2',
      ← isMultiplicative_sigma.map_mul_of_coprime c3, ← hn1]
    exact hs
  have hform2 : (3 ^ a * (5 ^ b * (7 ^ c * m))) % 2 = 1 := by rw [← hform]; exact hn2
  -- the exponents of 3 and 7 are even
  have ha_even : a % 2 = 0 := by
    by_contra hne
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
    obtain ⟨t, ht⟩ := S_odd_dvd 3 k
    rw [ht] at hsig
    have e : (3 + 1) * t * (S 5 b * (S 7 c * sigma 1 m)) = 4 * (t * (S 5 b * (S 7 c * sigma 1 m))) := by
      ring
    rw [e] at hsig
    omega
  have hc_even : c % 2 = 0 := by
    by_contra hne
    obtain ⟨k, rfl⟩ : ∃ k, c = 2 * k + 1 := ⟨c / 2, by omega⟩
    obtain ⟨t, ht⟩ := S_odd_dvd 7 k
    rw [ht] at hsig
    have e : S 3 a * (S 5 b * ((7 + 1) * t * sigma 1 m)) = 4 * (2 * (S 3 a * (S 5 b * (t * sigma 1 m)))) := by
      ring
    rw [e] at hsig
    omega
  have ha2 : 2 ≤ a := by omega
  have hc2 : 2 ≤ c := by omega
  have hb1 : 1 ≤ b := by omega
  have v32 : S 3 2 = 13 := by decide
  have v51 : S 5 1 = 6 := by decide
  have v72 : S 7 2 = 57 := by decide
  have l3 := S_lower 3 2 (a - 2)
  rw [show 2 + (a - 2) = a by omega, v32] at l3
  have l5 := S_lower 5 1 (b - 1)
  rw [show 1 + (b - 1) = b by omega, v51] at l5
  have l7 := S_lower 7 2 (c - 2)
  rw [show 2 + (c - 2) = c by omega, v72] at l7
  have lm := le_sigma m (Nat.pos_of_ne_zero hm0)
  -- abundant: 13 * 6 * 57 > 2 * 9 * 5 * 49
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul l3 l5) l7) lm
  have e1 : S 3 a * 3 ^ 2 * (S 5 b * 5 ^ 1) * (S 7 c * 7 ^ 2) * sigma 1 m =
      2205 * (S 3 a * (S 5 b * (S 7 c * sigma 1 m))) := by ring
  have e2 : 13 * 3 ^ a * (6 * 5 ^ b) * (57 * 7 ^ c) * m =
      4446 * (3 ^ a * (5 ^ b * (7 ^ c * m))) := by ring
  rw [e1, e2, hsig] at h1
  have hpos : 0 < 3 ^ a * (5 ^ b * (7 ^ c * m)) := by rw [← hform]; omega
  omega

end OMA.Sylvester

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2.H1 := by
  intro n hperf hodd
  have hs : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
  exact OMA.Sylvester.sylvester n hodd hs
