import OMAReductions.R_oeis_a368207_R1

open Filter Topology

namespace DivBound

lemma pow4_le (a : ℕ) : (a + 1) ^ 4 ≤ 41 * 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rcases Nat.lt_or_ge a 6 with h | h
    · interval_cases a <;> norm_num
    · have h2 : (a + 2) ^ 4 ≤ 2 * (a + 1) ^ 4 := by
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
        have e : (6 + b + 2) ^ 4 + (b ^ 4 + 24 * b ^ 3 + 204 * b ^ 2 + 696 * b + 706) =
            2 * (6 + b + 1) ^ 4 := by ring
        omega
      calc (a + 1 + 1) ^ 4 = (a + 2) ^ 4 := by ring
        _ ≤ 2 * (a + 1) ^ 4 := h2
        _ ≤ 2 * (41 * 2 ^ a) := by omega
        _ = 41 * 2 ^ (a + 1) := by ring

lemma local_bound (p a : ℕ) (hp : 2 ≤ p) :
    (a + 1) ^ 4 ≤ (if p < 16 then 41 else 1) * p ^ a := by
  split_ifs with h
  · calc (a + 1) ^ 4 ≤ 41 * 2 ^ a := pow4_le a
      _ ≤ 41 * p ^ a := by gcongr
  · have h1 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    calc (a + 1) ^ 4 ≤ (2 ^ a) ^ 4 := by gcongr
      _ = 16 ^ a := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ p ^ a := by gcongr; omega
      _ = 1 * p ^ a := by ring

lemma card_pow4_le (n : ℕ) (hn : n ≠ 0) : n.divisors.card ^ 4 ≤ 41 ^ 16 * n := by
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  have hn' : n = n.primeFactors.prod (fun p => p ^ n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rfl
  calc n.primeFactors.prod (fun p => (n.factorization p + 1) ^ 4)
      ≤ n.primeFactors.prod (fun p => (if p < 16 then 41 else 1) * p ^ n.factorization p) := by
        apply Finset.prod_le_prod'
        intro p hp
        exact local_bound p _ (Nat.prime_of_mem_primeFactors hp).two_le
    _ = n.primeFactors.prod (fun p => (if p < 16 then 41 else 1)) *
          n.primeFactors.prod (fun p => p ^ n.factorization p) := Finset.prod_mul_distrib
    _ ≤ 41 ^ 16 * n := by
        rw [← hn']
        gcongr
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply Nat.pow_le_pow_right (by norm_num)
        calc (n.primeFactors.filter (fun p => p < 16)).card ≤ (Finset.range 16).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter] at hx
              simpa using hx.2
          _ = 16 := Finset.card_range 16

theorem tendsto_div_sqrt :
    Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  set C : ℝ := 41 ^ 16
  have hy : Tendsto (fun n : ℕ => ((n.divisors.card : ℝ) / Real.sqrt n) ^ 4) atTop (𝓝 0) := by
    have hC : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hC
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n ^ 4 = (n : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hnr.le]
    have hb : ((n.divisors.card ^ 4 : ℕ) : ℝ) ≤ ((41 ^ 16 * n : ℕ) : ℝ) := by
      exact_mod_cast card_pow4_le n hn.ne'
    push_cast at hb
    rw [div_pow, hs, div_le_div_iff₀ (by positivity) hnr]
    calc (n.divisors.card : ℝ) ^ 4 * n ≤ (41 ^ 16 * n) * n := by
          gcongr
          norm_num at hb ⊢
          exact hb
      _ = C * (n : ℝ) ^ 2 := by ring
  have hr := (hy.rpow_const (p := (1 / 4 : ℝ)) (Or.inr (by norm_num)))
  rw [Real.zero_rpow (by norm_num)] at hr
  refine hr.congr fun n => ?_
  have h0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) / Real.sqrt n := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

end DivBound

theorem OMA.solution : OMA.R_oeis_a368207_R1.H2 := DivBound.tendsto_div_sqrt
