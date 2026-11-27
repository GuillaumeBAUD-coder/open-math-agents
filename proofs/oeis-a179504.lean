import OMAStatements.S_oeis_a179504

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a179504.main := by
  intro n hn
  obtain ⟨v, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 n = v := by
    have hn0 : n ≠ 0 := hn.ne'
    have h3 : ¬ 2 ^ (v + 1) ∣ n := by
      rw [hnm, pow_succ, mul_comm (2 ^ v) 2, mul_comm (2 ^ v) m]
      exact fun h => hm (Nat.dvd_of_mul_dvd_mul_right (by positivity) h)
    have h4 : 2 ^ v ∣ n := by rw [hnm]; exact Dvd.intro _ rfl
    first
      | (rw [padicValNat_dvd_iff_le hn0] at h3 h4; omega)
      | (rw [Nat.padicValNat_def]; rw [padicValNat_dvd_iff_le hn0] at h3 h4; omega)
  have hcop : ∀ j, Nat.Coprime (2 ^ j) m := fun j =>
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have hsig : ∀ j, (sigma n (2 ^ j) : ℚ) = ∑ i ∈ Finset.range (j + 1), ((2 : ℚ) ^ n) ^ i := by
    intro j
    rw [sigma_apply_prime_pow Nat.prime_two]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, mul_comm]
  have h1 : sigma n (2 ^ (v + 1) * m) = sigma n (2 ^ (v + 1)) * sigma n m :=
    (isMultiplicative_sigma (k := n)).map_mul_of_coprime (hcop (v + 1))
  have h2 : sigma n n = sigma n (2 ^ v) * sigma n m := by
    have := (isMultiplicative_sigma (k := n)).map_mul_of_coprime (hcop v)
    rw [← hnm] at this
    exact this
  have hX2 : (2 : ℚ) ≤ 2 ^ n := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hX : (2 : ℚ) ^ n ≠ 1 := by linarith
  have hXv : ((2 : ℚ) ^ n) ^ (v + 1) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ ((2 : ℚ) ^ n) ^ (v + 1) := by
      calc (2 : ℚ) ≤ 2 ^ n := hX2
        _ = (2 ^ n) ^ 1 := by ring
        _ ≤ ((2 : ℚ) ^ n) ^ (v + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hX1 : (2 : ℚ) ^ n - 1 ≠ 0 := sub_ne_zero.mpr hX
  unfold OMA.S_oeis_a179504.a
  rw [if_neg hn.ne', hv, show 2 * n = 2 ^ (v + 1) * m by rw [hnm]; ring, h1, h2]
  push_cast
  rw [hsig, hsig, geom_sum_eq hX, geom_sum_eq hX, pow_mul]
  field_simp
  ring
