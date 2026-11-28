import OMAStatements.S_oeis_a006519

/-! Factor out the odd part and use the geometric sum for the powers of two. -/

open ArithmeticFunction OMA.S_oeis_a006519

theorem OMA.solution : type_of% @OMA.S_oeis_a006519.main := by
  intro n hn
  let k := n.factorization 2
  let m := ordCompl[2] n
  have hm : 2 ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hc : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two (by omega)
  have hs (j : ℕ) : (sigma 1 (2 ^ j * m) : ℚ) = (2 ^ j * 2 - 1) * (sigma 1 m : ℚ) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left j),
      sigma_one_apply_prime_pow Nat.prime_two]
    push_cast
    rw [geom_sum_eq (by norm_num : (2 : ℚ) ≠ 1)]
    norm_num [pow_succ]
  have hσ : (sigma 1 m : ℚ) ≠ 0 := by
    have hmpos : 0 < m := Nat.pos_of_ne_zero fun hz => by
      rw [hz, mul_zero] at hm
      omega
    exact_mod_cast (sigma_pos_iff.mpr hmpos).ne'
  have hd : 2 * n = 2 ^ (k + 1) * m := by rw [← hm, pow_succ']; ring
  change (↑(2 ^ k : ℕ) : ℚ) = _
  rw [hd, hs, ← hm, hs, mul_div_mul_right _ _ hσ, pow_succ]
  push_cast
  have hpow : 1 ≤ (2 : ℚ) ^ k := one_le_pow₀ (by norm_num)
  have e : ((2 : ℚ) ^ k * 2 * 2 - 1) / (2 ^ k * 2 - 1) - 2 = 1 / (2 ^ k * 2 - 1) := by
    field_simp [show (2 : ℚ) ^ k * 2 - 1 ≠ 0 by linarith]
    ring
  rw [e, one_div_one_div]
  ring
