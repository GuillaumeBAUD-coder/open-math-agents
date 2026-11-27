import OMAReductions.R_Erdos384_erdos_384_R1

-- Step Erdos384.erdos_384.R1.H3: hypothesis H3 of reduction Erdos384.erdos_384.R1
-- Credit: @koolkao
-- Original proof. k = 2: a prime factor of n/2 or (n-1)/2. k = 3: if n ≢ 3 (mod 4) then 2 divides C(n,3);
-- otherwise (n-1)/2 is odd and either has a prime factor q ≥ 5 (which divides C(n,3)) or is a power of 3,
-- and then 9 | n - 1 forces 3 | C(n,3) unless n = 7.

namespace OMA384H3

lemma choose_two_mul (m : ℕ) : (m + 4).choose 2 * 2 = (m + 4) * (m + 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (m + 4) 2
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  linarith

lemma choose_three_mul (m : ℕ) : (m + 6).choose 3 * 6 = (m + 6) * (m + 5) * (m + 4) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (m + 6) 3
  simp [Nat.descFactorial_succ, Nat.factorial] at h
  linarith

lemma case_two (n : ℕ) (hn : 4 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 2 ∧ 2 * p ≤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hC := choose_two_mul m
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hCe : (m + 4).choose 2 = (t + 2) * (2 * t + 3) := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [hC, ht]; ring
    have ha : (t + 2) ≠ 1 := by omega
    refine ⟨(t + 2).minFac, Nat.minFac_prime ha, ?_, ?_⟩
    · rw [hCe]; exact Dvd.dvd.mul_right (Nat.minFac_dvd _) _
    · have := Nat.minFac_le (show 0 < t + 2 by omega)
      omega
  · have hCe : (m + 4).choose 2 = (2 * t + 5) * (t + 2) := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [hC, ht]; ring
    have ha : (t + 2) ≠ 1 := by omega
    refine ⟨(t + 2).minFac, Nat.minFac_prime ha, ?_, ?_⟩
    · rw [hCe]; exact Dvd.dvd.mul_left (Nat.minFac_dvd _) _
    · have := Nat.minFac_le (show 0 < t + 2 by omega)
      omega

lemma case_three (n : ℕ) (hn : 6 ≤ n) (h7 : n ≠ 7) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 3 ∧ 2 * p ≤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have hC := choose_three_mul m
  set C := (m + 6).choose 3 with hCdef
  by_cases h4 : (m + 6) % 4 = 3
  · -- write m + 5 = 2 * a with a odd
    obtain ⟨a, ha⟩ : ∃ a, m + 5 = 2 * a := ⟨(m + 5) / 2, by omega⟩
    have ha5 : 5 ≤ a := by omega
    have haodd : ¬ 2 ∣ a := by omega
    by_cases hq : ∃ q : ℕ, q.Prime ∧ q ∣ a ∧ q ≠ 3
    · obtain ⟨q, hqp, hqa, hq3⟩ := hq
      have hq2 : q ≠ 2 := by
        rintro rfl; exact haodd hqa
      have hcop : Nat.Coprime q 6 := by
        have h6 : (6 : ℕ) = 2 * 3 := by norm_num
        rw [h6]
        apply Nat.Coprime.mul_right
        · exact (Nat.coprime_primes hqp Nat.prime_two).mpr hq2
        · exact (Nat.coprime_primes hqp Nat.prime_three).mpr hq3
      have hdvd6 : q ∣ C * 6 := by
        rw [hC, ha]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.dvd.mul_left hqa 2) _) _
      refine ⟨q, hqp, hcop.dvd_of_dvd_mul_right hdvd6, ?_⟩
      have := Nat.le_of_dvd (by omega) hqa
      omega
    · push Not at hq
      obtain ⟨b, hpow⟩ : ∃ b, a = 3 ^ b :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun hd hda => hq _ hd hda)⟩
      have hb : 2 ≤ b := by
        by_contra hlt
        have : b ≤ 1 := by omega
        have h3 : 3 ^ b ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        omega
      have h9 : 9 ∣ a := by
        rw [hpow]
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hb
        rw [hc, pow_add]
        exact Dvd.dvd.mul_right (by norm_num) _
      have hdvd : 9 ∣ C * 6 := by
        rw [hC, ha]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.dvd.mul_left h9 2) _) _
      refine ⟨3, Nat.prime_three, ?_, by omega⟩
      omega
  · have h4dvd : 4 ∣ (m + 6) * (m + 5) * (m + 4) := by
      have hr : (m + 6) % 4 = 0 ∨ (m + 6) % 4 = 1 ∨ (m + 6) % 4 = 2 := by omega
      rcases hr with hr | hr | hr
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hr) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _
      · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    rw [← hC] at h4dvd
    refine ⟨2, Nat.prime_two, ?_, by omega⟩
    omega

theorem h3 : ∀ n k : ℕ, 2 ≤ k → k ≤ 3 → 2 * k ≤ n → (n, k) ≠ (7, 3) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  intro n k hk2 hk3 hkn h73
  interval_cases k
  · exact case_two n (by omega)
  · exact case_three n (by omega) (fun h => h73 (by rw [h]))

end OMA384H3

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := OMA384H3.h3
