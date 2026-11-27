import OMAReductions.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1

-- Step LegendreConjecture.legendre_conjecture.ferreira_large_n.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1.H2 := by
  intro N hgap m hm
  classical
  have hex : ∃ k : ℕ, m ^ 2 < k.nth Nat.Prime := by
    obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (m ^ 2 + 1)
    exact ⟨Nat.count Nat.Prime p, by rw [Nat.nth_count hp]; omega⟩
  let k := Nat.find hex
  have hk_gt : m ^ 2 < k.nth Nat.Prime := Nat.find_spec hex
  have hk_pos : 0 < k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.nth_prime_zero_eq_two] at hk_gt
    have hpN : 2 ≤ N.nth Nat.Prime := (Nat.prime_nth_prime N).two_le
    omega
  let n := k - 1
  have hn_succ : n + 1 = k := by omega
  have hn_le : n.nth Nat.Prime ≤ m ^ 2 := by
    by_contra! hgt
    have := Nat.find_min hex (show n < k by omega)
    exact this hgt
  have hNn : N ≤ n := by
    by_contra! hlt
    have hkN : k ≤ N := by omega
    have hmono : k.nth Nat.Prime ≤ N.nth Nat.Prime :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hkN
    omega
  have hstep := hgap n hNn
  rw [hn_succ] at hstep
  have hsqrt_le : Real.sqrt (n.nth Nat.Prime : ℝ) ≤ (m : ℝ) := by
    have hle : (n.nth Nat.Prime : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hn_le
    rw [← Real.sqrt_sq (Nat.cast_nonneg m)]
    exact Real.sqrt_le_sqrt hle
  have hsqrt_lt : Real.sqrt (k.nth Nat.Prime : ℝ) < (m : ℝ) + 1 := by linarith
  have hk_lt_real : (k.nth Nat.Prime : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := by
    have hsq : Real.sqrt (k.nth Nat.Prime : ℝ) ^ 2 < ((m : ℝ) + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (k.nth Nat.Prime : ℝ)]
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    push_cast
    exact hsq
  have hk_lt : k.nth Nat.Prime < (m + 1) ^ 2 := by exact_mod_cast hk_lt_real
  exact ⟨k.nth Nat.Prime, ⟨hk_gt, hk_lt⟩, Nat.prime_nth_prime k⟩
