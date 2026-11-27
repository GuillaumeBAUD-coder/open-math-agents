import OMAReductions.R_RegularPrimes_infinitude_of_irregularprimes_R1

-- Step RegularPrimes.infinitude_of_irregularprimes.R1.H1: hypothesis H1 of reduction RegularPrimes.infinitude_of_irregularprimes.R1

/-!
Take `n = 20 d = 2 k`. Euler's formula `ζ(2k) = (-1)^(k+1) 2^(2k-1) π^(2k) B_{2k} / (2k)!` and
`ζ(2k) ≥ 1` give `(2k)! ≤ 2^(2k-1) π^(2k) |B_{2k}| ≤ (7^n / 2) |B_n|`. Since `7^n ≤ (n-1)!` for
`n ≥ 20`, this yields `|B_n| ≥ 2 n`, so `|B_n / n| > 1`.
-/

namespace OMA

theorem seven_pow_le : ∀ n : ℕ, 20 ≤ n → 7 ^ n ≤ (n - 1).factorial := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have e : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [e, Nat.factorial_succ, pow_succ]
    have h7 : 7 ≤ n - 1 + 1 := by omega
    calc 7 ^ n * 7 ≤ (n - 1).factorial * (n - 1 + 1) := Nat.mul_le_mul ih h7
      _ = (n - 1 + 1) * (n - 1).factorial := Nat.mul_comm _ _

end OMA

theorem OMA.solution : OMA.R_RegularPrimes_infinitude_of_irregularprimes_R1.H1 := by
  unfold OMA.R_RegularPrimes_infinitude_of_irregularprimes_R1.H1
  intro d hd
  refine ⟨2 * (10 * d), by omega, ⟨10 * d, by ring⟩, ⟨20, by ring⟩, ?_⟩
  have hk : 10 * d ≠ 0 := by omega
  have hs := hasSum_zeta_nat hk
  have h1 : (1 : ℝ) ≤ (-1 : ℝ) ^ (10 * d + 1) * (2 : ℝ) ^ (2 * (10 * d) - 1) *
      Real.pi ^ (2 * (10 * d)) * (bernoulli (2 * (10 * d)) : ℝ) /
        ((2 * (10 * d)).factorial : ℝ) := by
    have h := le_hasSum hs 1 (fun j _ => by positivity)
    simpa using h
  generalize hn : 2 * (10 * d) = n at h1 ⊢
  have hn20 : 20 ≤ n := by omega
  generalize hB : ((bernoulli n : ℚ) : ℝ) = B at h1
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  -- absolute values
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (n - 1) * Real.pi ^ n * |B| / (n.factorial : ℝ) := by
    have habs := le_trans h1 (le_abs_self _)
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, abs_of_pos hfact] at habs
    exact habs
  rw [le_div_iff₀ hfact, one_mul] at h2
  -- 2^(n-1) π^n ≤ 7^n / 2
  have hpi : Real.pi ≤ 7 / 2 := by
    have := Real.pi_lt_d2
    linarith
  have hpow : (2 : ℝ) ^ (n - 1) * Real.pi ^ n ≤ (7 : ℝ) ^ n / 2 := by
    have e : (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : Real.pi ^ n ≤ (7 / 2 : ℝ) ^ n := pow_le_pow_left₀ Real.pi_pos.le hpi n
    have h4 : (2 : ℝ) ^ (n - 1) * Real.pi ^ n ≤ 2 ^ (n - 1) * (7 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (2 : ℝ) ^ (n - 1) * (7 / 2 : ℝ) ^ n = (7 : ℝ) ^ n / 2 := by
      rw [div_pow, e]
      field_simp
    linarith
  have h7 : ((7 : ℝ)) ^ n ≤ ((n - 1).factorial : ℝ) := by
    exact_mod_cast OMA.seven_pow_le n hn20
  have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    have e : n = (n - 1) + 1 := by omega
    conv_lhs => rw [e, Nat.factorial_succ]
    push_cast
    have e2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : (n - 1 + 1 : ℕ) = n := by omega
      exact_mod_cast this
    rw [e2]
  have hBnn : 0 ≤ |B| := abs_nonneg B
  have hm : (0 : ℝ) < ((n - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
  have hnr : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn20
  -- n * (n-1)! ≤ (7^n / 2) |B| ≤ ((n-1)! / 2) |B|
  have h8 : (n : ℝ) * ((n - 1).factorial : ℝ) ≤ ((n - 1).factorial : ℝ) / 2 * |B| := by
    rw [← hfac]
    calc (n.factorial : ℝ) ≤ (2 : ℝ) ^ (n - 1) * Real.pi ^ n * |B| := h2
      _ ≤ (7 : ℝ) ^ n / 2 * |B| := mul_le_mul_of_nonneg_right hpow hBnn
      _ ≤ ((n - 1).factorial : ℝ) / 2 * |B| :=
          mul_le_mul_of_nonneg_right (by linarith) hBnn
  have h9 : 2 * (n : ℝ) ≤ |B| := by
    have h10 : (n : ℝ) * ((n - 1).factorial : ℝ) ≤ (|B| / 2) * ((n - 1).factorial : ℝ) := by
      linarith
    have := le_of_mul_le_mul_right h10 hm
    linarith
  have hcast : (((bernoulli n / n : ℚ)) : ℝ) = B / (n : ℝ) := by
    push_cast
    rw [hB]
  rw [hcast, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ)), lt_div_iff₀ (by linarith)]
  linarith
