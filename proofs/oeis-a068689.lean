import OMAStatements.S_oeis_a068689

/-!
A068689: the numbers `9 d d ... d 9` (with `k ≥ 1` inner digits `d`) can only be prime for
`d = 1, 2, 8`.

Clearing the repunit division gives `9 * sandwich d k = (810 + 10 d) * 10 ^ k + (81 - 10 d)`.
* `d = 0, 3, 6, 9`: every summand of `sandwich d k` is divisible by 3.
* `d = 7`: `880 * 10 ^ k + 11` is divisible by 11 for every `k`.
* `d = 4` and `d = 5`: a covering system of period 6 with the primes 3, 7, 11, 13
  (`k ≡ 0, 3`: 3; `k ≡ 2, 4`: 11; `k ≡ 1, 5`: 13 and 7 for `d = 4`, 7 and 13 for `d = 5`).
Since `sandwich d k ≥ 900`, such a divisor is proper, so the number is not prime.
-/

namespace OMA.A068689Proof

open OMA.S_oeis_a068689

/-- Clearing the repunit division: `9 * sandwich d k = (810 + 10 d) * 10 ^ k + (81 - 10 d)`. -/
lemma nine_mul_sandwich (d k : ℕ) :
    (9 : ℤ) * (sandwich d k : ℤ) =
      (810 + 10 * (d : ℤ)) * (10 : ℤ) ^ k + (81 - 10 * (d : ℤ)) := by
  have h9 : 9 ∣ 10 ^ k - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 10 1 k
    rw [one_pow] at h
    exact h
  obtain ⟨R, hR⟩ := h9
  have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hnat : 10 ^ k = 9 * R + 1 := by omega
  have hR' : (10 : ℤ) ^ k - 1 = 9 * (R : ℤ) := by
    have h2 : ((10 ^ k : ℕ) : ℤ) = ((9 * R + 1 : ℕ) : ℤ) := by rw [hnat]
    push_cast at h2
    linarith
  have hdiv : (10 ^ k - 1) / 9 = R := by
    rw [hR]
    exact Nat.mul_div_cancel_left R (by norm_num)
  unfold sandwich
  rw [hdiv]
  push_cast
  linear_combination (-10 * (d : ℤ)) * hR'

/-- Periodicity of powers of ten modulo `m`. -/
lemma dvd_of_period (m A B : ℤ) (p c t : ℕ) (hp : m ∣ (10 : ℤ) ^ p - 1)
    (hc : m ∣ A * (10 : ℤ) ^ c + B) : m ∣ A * (10 : ℤ) ^ (p * t + c) + B := by
  have h1 : (10 : ℤ) ^ p - 1 ∣ ((10 : ℤ) ^ p) ^ t - 1 := by
    have h := sub_dvd_pow_sub_pow ((10 : ℤ) ^ p) 1 t
    rw [one_pow] at h
    exact h
  have h2 : m ∣ ((10 : ℤ) ^ p) ^ t - 1 := dvd_trans hp h1
  have e : A * (10 : ℤ) ^ (p * t + c) + B =
      A * (10 : ℤ) ^ c * (((10 : ℤ) ^ p) ^ t - 1) + (A * (10 : ℤ) ^ c + B) := by
    rw [pow_add, pow_mul]
    ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left h2 _) hc

lemma dvd_sandwich (m d k : ℕ) (A B : ℤ) (hA : A = 810 + 10 * (d : ℤ))
    (hB : B = 81 - 10 * (d : ℤ)) (hcop : Nat.Coprime m 9)
    (h : (m : ℤ) ∣ A * (10 : ℤ) ^ k + B) : m ∣ sandwich d k := by
  have h9 := nine_mul_sandwich d k
  rw [← hA, ← hB] at h9
  rw [← h9] at h
  have h' : m ∣ 9 * sandwich d k := by exact_mod_cast h
  exact (Nat.Coprime.dvd_mul_left hcop).mp h'

lemma three_dvd_sandwich (d k : ℕ) (A B : ℤ) (hA : A = 810 + 10 * (d : ℤ))
    (hB : B = 81 - 10 * (d : ℤ)) (h : (27 : ℤ) ∣ A * (10 : ℤ) ^ k + B) :
    3 ∣ sandwich d k := by
  have h9 := nine_mul_sandwich d k
  rw [← hA, ← hB] at h9
  rw [← h9] at h
  have h' : 9 * 3 ∣ 9 * sandwich d k := by exact_mod_cast h
  exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h'

lemma three_dvd_of_three_dvd (d k : ℕ) (hd : 3 ∣ d) : 3 ∣ sandwich d k := by
  unfold sandwich
  exact dvd_add (dvd_add (Dvd.dvd.mul_right (by norm_num) _)
    (Dvd.dvd.mul_left (Dvd.dvd.mul_right hd _) _)) (by norm_num)

lemma not_prime_of_dvd (m d k : ℕ) (hm : 1 < m) (hm' : m < 900) (hk : 1 ≤ k)
    (h : m ∣ sandwich d k) : ¬ (sandwich d k).Prime := by
  intro hp
  have hpow : 100 ≤ 10 ^ (k + 1) := by
    calc 100 = 10 ^ 2 := by norm_num
      _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : 900 ≤ sandwich d k := by
    unfold sandwich
    omega
  rcases (Nat.dvd_prime hp).mp h with h1 | h1
  · omega
  · omega

/-- Inner digit 4: covering set `{3, 7, 11, 13}` with period 6. -/
lemma small_factor_four (k : ℕ) : ∃ m : ℕ, 1 < m ∧ m < 900 ∧ m ∣ sandwich 4 k := by
  obtain ⟨t, c, hc, rfl⟩ : ∃ t c, c < 6 ∧ k = 6 * t + c :=
    ⟨k / 6, k % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 6).symm⟩
  interval_cases c
  · exact ⟨3, by norm_num, by norm_num, three_dvd_sandwich 4 _ 850 41 (by norm_num) (by norm_num)
      (dvd_of_period 27 850 41 6 0 t (by norm_num) (by norm_num))⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_sandwich 13 4 _ 850 41 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 13 850 41 6 1 t (by norm_num) (by norm_num))⟩
  · exact ⟨11, by norm_num, by norm_num, dvd_sandwich 11 4 _ 850 41 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 11 850 41 6 2 t (by norm_num) (by norm_num))⟩
  · exact ⟨3, by norm_num, by norm_num, three_dvd_sandwich 4 _ 850 41 (by norm_num) (by norm_num)
      (dvd_of_period 27 850 41 6 3 t (by norm_num) (by norm_num))⟩
  · exact ⟨11, by norm_num, by norm_num, dvd_sandwich 11 4 _ 850 41 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 11 850 41 6 4 t (by norm_num) (by norm_num))⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_sandwich 7 4 _ 850 41 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 7 850 41 6 5 t (by norm_num) (by norm_num))⟩

/-- Inner digit 5: covering set `{3, 7, 11, 13}` with period 6. -/
lemma small_factor_five (k : ℕ) : ∃ m : ℕ, 1 < m ∧ m < 900 ∧ m ∣ sandwich 5 k := by
  obtain ⟨t, c, hc, rfl⟩ : ∃ t c, c < 6 ∧ k = 6 * t + c :=
    ⟨k / 6, k % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 6).symm⟩
  interval_cases c
  · exact ⟨3, by norm_num, by norm_num, three_dvd_sandwich 5 _ 860 31 (by norm_num) (by norm_num)
      (dvd_of_period 27 860 31 6 0 t (by norm_num) (by norm_num))⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_sandwich 7 5 _ 860 31 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 7 860 31 6 1 t (by norm_num) (by norm_num))⟩
  · exact ⟨11, by norm_num, by norm_num, dvd_sandwich 11 5 _ 860 31 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 11 860 31 6 2 t (by norm_num) (by norm_num))⟩
  · exact ⟨3, by norm_num, by norm_num, three_dvd_sandwich 5 _ 860 31 (by norm_num) (by norm_num)
      (dvd_of_period 27 860 31 6 3 t (by norm_num) (by norm_num))⟩
  · exact ⟨11, by norm_num, by norm_num, dvd_sandwich 11 5 _ 860 31 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 11 860 31 6 4 t (by norm_num) (by norm_num))⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_sandwich 13 5 _ 860 31 (by norm_num) (by norm_num)
      (by decide) (by exact_mod_cast dvd_of_period 13 860 31 6 5 t (by norm_num) (by norm_num))⟩

/-- Inner digit 7: always divisible by 11. -/
lemma eleven_dvd_seven (k : ℕ) : 11 ∣ sandwich 7 k := by
  refine dvd_sandwich 11 7 k 880 11 (by norm_num) (by norm_num) (by decide) ?_
  have h : (11 : ℤ) ∣ 880 * (10 : ℤ) ^ k + 11 :=
    dvd_add (Dvd.dvd.mul_right (by norm_num) _) (by norm_num)
  exact_mod_cast h

end OMA.A068689Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a068689.main := by
  intro d k hd hk hp
  by_contra hne
  have hd' : d = 0 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 9 := by omega
  rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact OMA.A068689Proof.not_prime_of_dvd 3 0 k (by norm_num) (by norm_num) hk
      (OMA.A068689Proof.three_dvd_of_three_dvd 0 k (by norm_num)) hp
  · exact OMA.A068689Proof.not_prime_of_dvd 3 3 k (by norm_num) (by norm_num) hk
      (OMA.A068689Proof.three_dvd_of_three_dvd 3 k (by norm_num)) hp
  · obtain ⟨m, h1, h2, h3⟩ := OMA.A068689Proof.small_factor_four k
    exact OMA.A068689Proof.not_prime_of_dvd m 4 k h1 h2 hk h3 hp
  · obtain ⟨m, h1, h2, h3⟩ := OMA.A068689Proof.small_factor_five k
    exact OMA.A068689Proof.not_prime_of_dvd m 5 k h1 h2 hk h3 hp
  · exact OMA.A068689Proof.not_prime_of_dvd 3 6 k (by norm_num) (by norm_num) hk
      (OMA.A068689Proof.three_dvd_of_three_dvd 6 k (by norm_num)) hp
  · exact OMA.A068689Proof.not_prime_of_dvd 11 7 k (by norm_num) (by norm_num) hk
      (OMA.A068689Proof.eleven_dvd_seven k) hp
  · exact OMA.A068689Proof.not_prime_of_dvd 3 9 k (by norm_num) (by norm_num) hk
      (OMA.A068689Proof.three_dvd_of_three_dvd 9 k (by norm_num)) hp
