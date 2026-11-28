import OMAReductions.R_oeis_a284760_R1

/-! Write n = 4k + 2. For k = 0 the sum is 1. For k ≥ 1 the exponent n - 2 = 4k is positive, so
i^(n-2) ≡ i (mod 2), and the sum is congruent to 1 + 2 + ... + (n-1) = (2k+1)(4k+1), which is
odd. Since n^4 is even, it cannot divide an odd number. -/

theorem OMA.solution : OMA.R_oeis_a284760_R1.H1 := by
  intro n hn h0
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  have hS : (∑ i ∈ Finset.Ico 1 (4 * k + 2), i ^ (4 * k + 2 - 2)) % 2 = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · have hpow : ∀ i, i ^ (4 * k + 2 - 2) % 2 = i % 2 := by
        intro i
        rw [show 4 * k + 2 - 2 = 4 * k by omega, Nat.pow_mod]
        rcases Nat.mod_two_eq_zero_or_one i with h | h
        · rw [h, zero_pow (by omega)]
          norm_num
        · rw [h, one_pow]
          norm_num
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => hpow i), ← Finset.sum_nat_mod]
      have h1 := Finset.sum_range_id (4 * k + 2)
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add] at h1
      rw [h1, show 4 * k + 2 - 1 = 4 * k + 1 by omega]
      have e : (4 * k + 2) * (4 * k + 1) = 2 * (8 * k ^ 2 + 6 * k + 1) := by ring
      rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
      omega
  have h2 : 2 ∣ (4 * k + 2) ^ 4 := dvd_pow ⟨2 * k + 1, by ring⟩ (by norm_num)
  have h3 : 2 ∣ ∑ i ∈ Finset.Ico 1 (4 * k + 2), i ^ (4 * k + 2 - 2) :=
    h2.trans (Nat.dvd_of_mod_eq_zero h0)
  omega
