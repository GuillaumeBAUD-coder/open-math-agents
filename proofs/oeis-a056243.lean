import OMAStatements.S_oeis_a056243

-- Credit: @mjsechrest2

namespace OMA.P_oeis_a056243

open OMA.S_oeis_a056243
open scoped Polynomial

private lemma eight_mul_a (m : ℕ) :
    8 * a (m + 3) = (2 : ℤ) ^ m * (9 * (m : ℤ) ^ 2 + 19 * m + 8) := by
  have ha : a (m + 3) =
      ∑ j ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * ((m + 2 + 2 * j).choose (m + 2) : ℤ) := by
    unfold a T
    rw [if_neg (by omega)]
    have hsub : m + 3 - 2 = m + 1 := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : m + 1 - 1 - j = m - j := by omega
    have h2 : m + 1 - 1 = m := by omega
    have h3 : m + 3 + 2 * j - 1 = m + 2 + 2 * j := by omega
    rw [h1, h2, h3]
    congr 1
    have hsym := Nat.choose_symm (show 2 * j ≤ m + 2 + 2 * j by omega)
    have hsub2 : m + 2 + 2 * j - 2 * j = m + 2 := by omega
    rw [hsub2] at hsym
    exact_mod_cast hsym.symm
  have hpoly_eq :
      (∑ j ∈ Finset.range (m + 1),
        (-1 : ℤ[X]) ^ (m - j) * (m.choose j : ℤ[X]) * (Polynomial.X + 1 : ℤ[X]) ^ (m + 2 + 2 * j)) =
      Polynomial.X ^ m * ((Polynomial.X + 1 : ℤ[X]) ^ (m + 2) * (Polynomial.X + 2 : ℤ[X]) ^ m) := by
    have hbin := add_pow ((Polynomial.X + 1 : ℤ[X]) ^ 2) (-1 : ℤ[X]) m
    have hsimp : (Polynomial.X + 1 : ℤ[X]) ^ 2 + (-1 : ℤ[X]) =
        Polynomial.X * (Polynomial.X + 2) := by ring
    rw [hsimp, mul_pow] at hbin
    calc
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ[X]) ^ (m - j) * (m.choose j : ℤ[X]) * (Polynomial.X + 1 : ℤ[X]) ^ (m + 2 + 2 * j)
        = (Polynomial.X + 1 : ℤ[X]) ^ (m + 2) *
          ∑ j ∈ Finset.range (m + 1),
            ((Polynomial.X + 1 : ℤ[X]) ^ 2) ^ j * (-1 : ℤ[X]) ^ (m - j) * (m.choose j : ℤ[X]) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_add, pow_mul]
          ring
      _ = (Polynomial.X + 1 : ℤ[X]) ^ (m + 2) *
          (Polynomial.X ^ m * (Polynomial.X + 2 : ℤ[X]) ^ m) := by rw [← hbin]
      _ = Polynomial.X ^ m * ((Polynomial.X + 1 : ℤ[X]) ^ (m + 2) * (Polynomial.X + 2 : ℤ[X]) ^ m) := by
          ring
  have hcoeff : a (m + 3) =
      ((Polynomial.X + 1 : ℤ[X]) ^ (m + 2) * (Polynomial.X + 2 : ℤ[X]) ^ m).coeff 2 := by
    rw [ha]
    have h1 :
        (∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * (m.choose j : ℤ) * ((m + 2 + 2 * j).choose (m + 2) : ℤ)) =
        (∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ[X]) ^ (m - j) * (m.choose j : ℤ[X]) * (Polynomial.X + 1 : ℤ[X]) ^ (m + 2 + 2 * j)).coeff (m + 2) := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro j _
      have hc : ((-1 : ℤ[X]) ^ (m - j) * (m.choose j : ℤ[X])) =
          Polynomial.C ((-1 : ℤ) ^ (m - j) * (m.choose j : ℤ)) := by
        simp [map_mul, map_pow]
      rw [hc, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
    rw [h1, hpoly_eq, show m + 2 = 2 + m by omega, Polynomial.coeff_X_pow_mul]
  rw [hcoeff, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h1c : ∀ r : ℕ, ((Polynomial.X + 1 : ℤ[X]) ^ (m + 2)).coeff r = ((m + 2).choose r : ℤ) := by
    intro r
    simpa using Polynomial.coeff_X_add_one_pow ℤ (m + 2) r
  have h2c : ∀ r : ℕ, ((Polynomial.X + 2 : ℤ[X]) ^ m).coeff r =
      (2 : ℤ) ^ (m - r) * (m.choose r : ℤ) := by
    intro r
    have := Polynomial.coeff_X_add_C_pow (2 : ℤ) m r
    simpa [mul_comm] using this
  rw [h1c 0, h1c 1, h1c 2, h2c 0, h2c 1, h2c 2]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero]
  have hc2m : 2 * ((m + 2).choose 2 : ℤ) = ((m : ℤ) + 2) * (m + 1) := by
    have := Nat.choose_two_right (m + 2)
    have hdiv : 2 ∣ (m + 2) * (m + 1) := by
      rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
      · exact ⟨(2 * k + 3) * (k + 1), by ring⟩
    have hnat : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
      rw [this, show m + 2 - 1 = m + 1 by omega, Nat.mul_div_cancel' hdiv]
    exact_mod_cast hnat
  have hcm2 : 2 * (m.choose 2 : ℤ) = (m : ℤ) * (m - 1) := by
    cases m with
    | zero => simp
    | succ k =>
      have := Nat.choose_two_right (k + 1)
      have hdiv : 2 ∣ (k + 1) * k := by
        rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact ⟨(2 * t + 1) * t, by ring⟩
        · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
      have hnat : 2 * (k + 1).choose 2 = (k + 1) * k := by
        rw [this, show k + 1 - 1 = k by omega, Nat.mul_div_cancel' hdiv]
      push_cast
      have hz : 2 * ((k + 1).choose 2 : ℤ) = ((k : ℤ) + 1) * k := by exact_mod_cast hnat
      linarith
  cases m with
  | zero => norm_num
  | succ k =>
    cases k with
    | zero => norm_num
    | succ t =>
      have hpow1 : (2 : ℤ) ^ (t + 2) = 4 * (2 : ℤ) ^ t := by rw [pow_add]; ring
      have hpow2 : (2 : ℤ) ^ (t + 2 - 1) = 2 * (2 : ℤ) ^ t := by
        rw [show t + 2 - 1 = t + 1 by omega, pow_succ]; ring
      have hpow3 : (2 : ℤ) ^ (t + 2 - 2) = (2 : ℤ) ^ t := by
        rw [show t + 2 - 2 = t by omega]
      rw [hpow1, hpow2, hpow3]
      push_cast at hc2m hcm2 ⊢
      linear_combination 4 * (2 : ℤ) ^ t * hcm2 + 16 * (2 : ℤ) ^ t * hc2m

private lemma a_rec (n : ℕ) (hn : 6 ≤ n) :
    a n - 6 * a (n - 1) + 12 * a (n - 2) - 8 * a (n - 3) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h0 := eight_mul_a (k + 3)
  have h1 := eight_mul_a (k + 2)
  have h2 := eight_mul_a (k + 1)
  have h3 := eight_mul_a k
  have hs1 : k + 6 - 1 = k + 2 + 3 := by omega
  have hs2 : k + 6 - 2 = k + 1 + 3 := by omega
  have hs3 : k + 6 - 3 = k + 3 := by omega
  have hs0 : k + 6 = k + 3 + 3 := by omega
  rw [hs0, hs1, hs2, hs3]
  have hp1 : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by rw [pow_succ]; ring
  have hp2 : (2 : ℤ) ^ (k + 2) = 4 * (2 : ℤ) ^ k := by rw [pow_add]; ring
  have hp3 : (2 : ℤ) ^ (k + 3) = 8 * (2 : ℤ) ^ k := by rw [pow_add]; ring
  rw [hp3] at h0
  rw [hp2] at h1
  rw [hp1] at h2
  push_cast at h0 h1 h2 h3
  linarith

private lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * (1 - 2 * PowerSeries.X) ^ 3) =
      a n - (if 1 ≤ n then 6 * a (n - 1) else 0) +
        (if 2 ≤ n then 12 * a (n - 2) else 0) -
        (if 3 ≤ n then 8 * a (n - 3) else 0) := by
  have hpoly : ((1 - 2 * PowerSeries.X : PowerSeries ℤ) ^ 3) =
      1 - 6 * PowerSeries.X + 12 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 := by
    ring
  rw [hpoly, mul_sub, mul_add, mul_sub, mul_one, map_sub, map_add, map_sub, PowerSeries.coeff_mk]
  have hc (c : ℤ) (k : ℕ) :
      PowerSeries.coeff n (PowerSeries.mk a * (c • PowerSeries.X ^ k)) =
        if k ≤ n then c * a (n - k) else 0 := by
    rw [mul_smul_comm, map_smul, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  have h1 : PowerSeries.mk a * (6 * PowerSeries.X) =
      PowerSeries.mk a * ((6 : ℤ) • PowerSeries.X ^ 1) := by
    rw [pow_one, zsmul_eq_mul]; rfl
  have h2 : PowerSeries.mk a * (12 * PowerSeries.X ^ 2) =
      PowerSeries.mk a * ((12 : ℤ) • PowerSeries.X ^ 2) := by
    rw [zsmul_eq_mul]; rfl
  have h3 : PowerSeries.mk a * (8 * PowerSeries.X ^ 3) =
      PowerSeries.mk a * ((8 : ℤ) • PowerSeries.X ^ 3) := by
    rw [zsmul_eq_mul]; rfl
  rw [h1, h2, h3, hc 6 1, hc 12 2, hc 8 3]

end OMA.P_oeis_a056243

theorem OMA.solution : type_of% @OMA.S_oeis_a056243.main := by
  open OMA.S_oeis_a056243 OMA.P_oeis_a056243 PowerSeries in
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h8 : (8 : ℚ) * (a (m + 3) : ℚ) =
        (2 : ℚ) ^ m * (9 * (m : ℚ) ^ 2 + 19 * (m : ℚ) + 8) := by
      exact_mod_cast eight_mul_a m
    have hzpow : (2 : ℚ) ^ (((m + 3 : ℕ) : ℤ) - 6) = (2 : ℚ) ^ m / 8 := by
      have hexp : ((m + 3 : ℕ) : ℤ) - 6 = (m : ℤ) - 3 := by omega
      rw [hexp, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      norm_num
    rw [hzpow]
    push_cast
    linarith
  · ext n
    rw [coeff_lhs]
    have hrhs : (X ^ 3 * (1 + 3 * X - X ^ 2) : PowerSeries ℤ) =
        X ^ 3 + PowerSeries.C (3 : ℤ) * X ^ 4 - X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [hrhs]
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow]
    by_cases hn : 6 ≤ n
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), a_rec n hn]
      have h3 : n ≠ 3 := by omega
      have h4 : n ≠ 4 := by omega
      have h5 : n ≠ 5 := by omega
      simp [h3, h4, h5]
    · have ha0 : a 0 = 0 := by decide
      have ha1 : a 1 = 0 := by decide
      have ha2 : a 2 = 0 := by decide
      have ha3 : a 3 = 1 := by decide
      have ha4 : a 4 = 9 := by decide
      have ha5 : a 5 = 41 := by decide
      interval_cases n <;> simp [ha0, ha1, ha2, ha3, ha4, ha5]
