import OMAStatements.S_oeis_a274536

-- Problem: oeis-a274536
-- Credit: @anmolspace
-- Proof: if 5 ∤ n, σ(5n) = σ(5)σ(n) = 6σ(n) by multiplicativity. If 5 ∣ n, write n = 5^e m with
-- e ≥ 1, 5 ∤ m; then σ(5n) = (5σ(5^e) + 1)σ(m) while 6σ(n) = 6σ(5^e)σ(m), and σ(5^e) ≥ 5.

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a274536.main := by
  intro n hn
  unfold OMA.S_oeis_a274536.a
  have h5 : sigma 1 5 = 6 := by decide
  have p5 : Nat.Prime 5 := by norm_num
  constructor
  · intro h hdvd
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0
        simp at hdvd
        exact absurd hdvd hm
      · exact h0
    have hcop : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd p5).mpr hm
    have hc1 : Nat.Coprime (5 ^ e) m := Nat.Coprime.pow_left _ hcop
    have hc2 : Nat.Coprime (5 ^ (e + 1)) m := Nat.Coprime.pow_left _ hcop
    rw [show 5 * (5 ^ e * m) = 5 ^ (e + 1) * m by ring,
      isMultiplicative_sigma.map_mul_of_coprime hc1,
      isMultiplicative_sigma.map_mul_of_coprime hc2] at h
    have hs : sigma 1 (5 ^ (e + 1)) = 5 * sigma 1 (5 ^ e) + 1 := by
      rw [sigma_one_apply_prime_pow p5, sigma_one_apply_prime_pow p5,
        Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      all_goals first
        | (apply Finset.sum_congr rfl; intro i _; ring)
        | simp
    have hge : 5 ≤ sigma 1 (5 ^ e) := by
      rw [sigma_one_apply_prime_pow p5]
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he
        _ ≤ ∑ k ∈ Finset.range (e + 1), 5 ^ k :=
          Finset.single_le_sum (f := fun k => 5 ^ k) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
    have hm0 : 0 < sigma 1 m := by
      have : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp at hm
        · exact h0
      rw [sigma_one_apply]
      exact Finset.sum_pos (fun i hi => Nat.pos_of_mem_divisors hi)
        ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, this.ne'⟩⟩
    rw [hs, ← mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_right hm0 h
    omega
  · intro hnd
    have hc : Nat.Coprime 5 n := (Nat.Prime.coprime_iff_not_dvd p5).mpr hnd
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, h5]
