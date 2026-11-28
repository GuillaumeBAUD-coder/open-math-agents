import OMAReductions.R_OeisA110835_conjecture_R1

-- Step OeisA110835.conjecture.R1.H1: for 1 ≤ m ≤ 5 and m < n there is a prime in [n m, n (m + 1)].
-- Proof: Nagura (1952), a prime in (x, 6x/5] for x ≥ 25, proved here from Chebyshev-type bounds
-- (log N! = Σ Λ(n) ⌊N/n⌋, weights 1, 1/2, 1/3, 1/5, 1/30 and one bootstrap step), a chain of
-- 75 primes below 9·10^6, and a decide table for n m < 25.


/-!
# Nagura's theorem (1952): for every natural `x ≥ 25` there is a prime `p` with `x < p ≤ 6x/5`.

Proof route: Chebyshev's identity `log N! = ∑_{n ≤ N} Λ(n) ⌊N/n⌋`, Chebyshev's weights
`1, -1/2, -1/3, -1/5, +1/30`, and one bootstrap step (the weight is also `1` on `[7, 10)`),
which improves Chebyshev's upper constant `6A/5` to `(1026/875) A < 6A/5`.
-/

open Real Finset ArithmeticFunction

namespace Nagura

/-- `T N = log N!`. -/
noncomputable def T (N : ℕ) : ℝ := Real.log (N.factorial : ℝ)

/-- `S N = ψ(N) = ∑_{0 < n ≤ N} Λ n`. -/
noncomputable def S (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, Λ n

theorem psi_nat (N : ℕ) : Chebyshev.psi N = S N := by
  simp [Chebyshev.psi, S]

theorem S_nonneg (N : ℕ) : 0 ≤ S N :=
  Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

theorem divisors_eq_filter (m : ℕ) (hm : m ≠ 0) :
    m.divisors = (Ioc 0 m).filter (· ∣ m) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hm), Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h⟩, h⟩
  · rintro ⟨-, h⟩
    exact ⟨h, hm⟩

/-- Chebyshev's identity: `log N! = ∑_{n ≤ N} Λ(n) ⌊N/n⌋`. -/
theorem T_eq (N : ℕ) : T N = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  induction N with
  | zero => simp [T]
  | succ N ih =>
    have h1 : T (N + 1) = Real.log ((N + 1 : ℕ) : ℝ) + T N := by
      simp only [T, Nat.factorial_succ, Nat.cast_mul]
      rw [Real.log_mul (by positivity) (by positivity)]
    have h2 : ∀ n ∈ Ioc 0 (N + 1), Λ n * (((N + 1) / n : ℕ) : ℝ)
        = Λ n * ((N / n : ℕ) : ℝ) + (if n ∣ N + 1 then Λ n else 0) := by
      intro n _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [h1, ih, Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_filter,
      ← divisors_eq_filter (N + 1) (Nat.succ_ne_zero N), ArithmeticFunction.vonMangoldt_sum,
      Finset.sum_Ioc_succ_top (Nat.zero_le N), Nat.div_eq_of_lt (Nat.lt_succ_self N)]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    ring

theorem T_div (N d : ℕ) (hd : 0 < d) :
    T (N / d) = ∑ n ∈ Ioc 0 N, Λ n * (((N / n) / d : ℕ) : ℝ) := by
  rw [T_eq]
  have hc : ∀ n, (N / d) / n = (N / n) / d := by
    intro n; rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hc]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (Nat.div_le_self N d)⟩
  · intro n hn hn'
    simp only [Finset.mem_Ioc, not_and, not_le] at hn hn'
    have : N / d < n := hn' hn.1
    rw [← hc, Nat.div_eq_of_lt this]
    simp

/-- Chebyshev's weight function. -/
def fC (k : ℕ) : ℤ := (k : ℤ) - ((k / 2 : ℕ) : ℤ) - ((k / 3 : ℕ) : ℤ) - ((k / 5 : ℕ) : ℤ)
  + ((k / 30 : ℕ) : ℤ)

theorem fC_nonneg (k : ℕ) : 0 ≤ fC k := by unfold fC; omega
theorem fC_le_one (k : ℕ) : fC k ≤ 1 := by unfold fC; omega
theorem fC_eq_one_a (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ 5) : fC k = 1 := by unfold fC; omega
theorem fC_eq_one_b (k : ℕ) (h1 : 7 ≤ k) (h2 : k ≤ 9) : fC k = 1 := by unfold fC; omega

theorem fC_cast (k : ℕ) : ((fC k : ℤ) : ℝ) = (k : ℝ) - ((k / 2 : ℕ) : ℝ) - ((k / 3 : ℕ) : ℝ)
    - ((k / 5 : ℕ) : ℝ) + ((k / 30 : ℕ) : ℝ) := by
  unfold fC
  rw [Int.cast_add, Int.cast_sub, Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]

/-- Chebyshev's combination. -/
noncomputable def C (N : ℕ) : ℝ := T N - T (N / 2) - T (N / 3) - T (N / 5) + T (N / 30)

theorem C_eq (N : ℕ) : C N = ∑ n ∈ Ioc 0 N, Λ n * (fC (N / n) : ℝ) := by
  rw [C, T_eq N, T_div N 2 (by norm_num), T_div N 3 (by norm_num), T_div N 5 (by norm_num),
    T_div N 30 (by norm_num), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [fC_cast]
  simp only [Nat.div_div_eq_div_mul]
  ring

theorem C_le_S (N : ℕ) : C N ≤ S N := by
  rw [C_eq, S]
  apply Finset.sum_le_sum
  intro n _
  have h1 : (fC (N / n) : ℝ) ≤ 1 := by exact_mod_cast fC_le_one (N / n)
  have h2 : 0 ≤ Λ n := vonMangoldt_nonneg
  nlinarith

theorem sum_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc a c, f n = ∑ n ∈ Ioc a b, f n + ∑ n ∈ Ioc b c, f n :=
  (Finset.sum_Ioc_consecutive f hab hbc).symm

theorem S_sub (a b : ℕ) (hab : a ≤ b) : S b - S a = ∑ n ∈ Ioc a b, Λ n := by
  rw [S, S, sum_split 0 a b (Nat.zero_le a) hab]; ring

/-- The telescoping comparison used for the upper bounds. -/
theorem S_upper_aux (N : ℕ) : (S N - S (N / 6)) + (S (N / 7) - S (N / 10)) ≤ C N := by
  have h10_7 : N / 10 ≤ N / 7 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have h7_6 : N / 7 ≤ N / 6 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have h6 : N / 6 ≤ N := Nat.div_le_self N 6
  rw [S_sub _ _ h6, S_sub _ _ h10_7, C_eq, sum_split 0 (N / 10) N (Nat.zero_le _) (h10_7.trans (h7_6.trans h6)),
    sum_split (N / 10) (N / 7) N h10_7 (h7_6.trans h6), sum_split (N / 7) (N / 6) N h7_6 h6]
  have hA : 0 ≤ ∑ n ∈ Ioc 0 (N / 10), Λ n * (fC (N / n) : ℝ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by exact_mod_cast fC_nonneg _)
  have hC : 0 ≤ ∑ n ∈ Ioc (N / 7) (N / 6), Λ n * (fC (N / n) : ℝ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg vonMangoldt_nonneg (by exact_mod_cast fC_nonneg _)
  have hB : ∑ n ∈ Ioc (N / 10) (N / 7), Λ n * (fC (N / n) : ℝ) = ∑ n ∈ Ioc (N / 10) (N / 7), Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have k1 : 7 ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr (by
      have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 7)).mp hn.2; linarith)
    have k2 : N / n < 10 := (Nat.div_lt_iff_lt_mul hn0).mpr (by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).mp hn.1; linarith)
    rw [fC_eq_one_b _ k1 (by omega)]; simp
  have hD : ∑ n ∈ Ioc (N / 6) N, Λ n * (fC (N / n) : ℝ) = ∑ n ∈ Ioc (N / 6) N, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have k1 : 1 ≤ N / n := Nat.div_pos hn.2 hn0
    have k2 : N / n < 6 := (Nat.div_lt_iff_lt_mul hn0).mpr (by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).mp hn.1; linarith)
    rw [fC_eq_one_a _ k1 (by omega)]; simp
  rw [hB, hD]
  linarith

theorem S_upper_aux1 (N : ℕ) : S N - S (N / 6) ≤ C N := by
  have := S_upper_aux N
  have : 0 ≤ S (N / 7) - S (N / 10) := by
    rw [S_sub _ _ (Nat.div_le_div_left (by norm_num) (by norm_num))]
    exact Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  linarith

end Nagura

namespace Nagura

/-- `g y = y log y - y`. -/
noncomputable def g (y : ℝ) : ℝ := y * Real.log y - y

/-- Tangent-line inequality for the convex function `g`. -/
theorem g_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : g a + Real.log a * (b - a) ≤ g b := by
  unfold g
  rcases hb.eq_or_lt with rfl | hb
  · simp; nlinarith [Real.log_le_sub_one_of_pos ha]
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne', inv_div] at h
    have h2 : b * (1 - a / b) = b - a := by field_simp
    have h3 : b * (1 - a / b) ≤ b * (Real.log b - Real.log a) := mul_le_mul_of_nonneg_left h hb.le
    nlinarith

theorem g_ge_neg_one (y : ℝ) (hy : 0 ≤ y) : -1 ≤ g y := by
  have := g_tangent (a := 1) one_pos hy
  simp [g] at this ⊢; linarith

theorem T_zero : T 0 = 0 := by simp [T]

theorem T_ge (M : ℕ) : g M ≤ T M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [g, T]
  · have h := Stirling.le_log_factorial_stirling (Nat.pos_iff_ne_zero.mp hM)
    have h1 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.two_le_pi])
    unfold g T; linarith

theorem T_le (M : ℕ) (hM : 1 ≤ M) : T M ≤ g M + Real.log M / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have h := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at h
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [Real.log_mul (by norm_num) hk.ne', Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  unfold g T
  push_cast at h ⊢
  linarith

theorem log_nat_mono {m N : ℕ} (h : m ≤ N) : Real.log m ≤ Real.log N := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

theorem T_div_ge (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    g ((N : ℝ) / d) - Real.log N ≤ T (N / d) := by
  set y : ℝ := (N : ℝ) / d with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyN : y ≤ N := by
    rw [hy]; exact div_le_self (by positivity) (by exact_mod_cast hd)
  have hMle : ((N / d : ℕ) : ℝ) ≤ y := Nat.cast_div_le
  have hMge : y - 1 < ((N / d : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor y
    rwa [hy, Nat.floor_div_eq_div] at this
  have ht := g_tangent hy0 (Nat.cast_nonneg (N / d))
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have key : -Real.log N ≤ Real.log y * (((N / d : ℕ) : ℝ) - y) := by
    rcases le_or_gt 1 y with h1 | h1
    · have hl : 0 ≤ Real.log y := Real.log_nonneg h1
      have hl2 : Real.log y ≤ Real.log N := Real.log_le_log hy0 hyN
      nlinarith
    · have hl : Real.log y < 0 := Real.log_neg hy0 h1
      nlinarith
  have := T_ge (N / d)
  linarith

theorem T_div_le (N d : ℕ) (hN : 1 ≤ N) (hd : 1 ≤ d) :
    T (N / d) ≤ g ((N : ℝ) / d) + Real.log N / 2 + 1 := by
  set y : ℝ := (N : ℝ) / d with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hMle : ((N / d : ℕ) : ℝ) ≤ y := Nat.cast_div_le
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rcases Nat.eq_zero_or_pos (N / d) with h0 | hpos
  · rw [h0, T_zero]
    have := g_ge_neg_one y hy0.le
    linarith
  · have hM : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hpos
    have ht := g_tangent hM hy0.le
    have hl : 0 ≤ Real.log ((N / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hpos)
    have hl2 : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N d)
    have h1 := T_le (N / d) hpos
    nlinarith

/-- Chebyshev's constant `A = log(2^{1/2} 3^{1/3} 5^{1/5} / 30^{1/30}) ≈ 0.92129`. -/
noncomputable def A : ℝ := 7 / 15 * Real.log 2 + 3 / 10 * Real.log 3 + 1 / 6 * Real.log 5

theorem g_comb (N : ℝ) (hN : 0 < N) :
    g N - g (N / 2) - g (N / 3) - g (N / 5) + g (N / 30) = A * N := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  unfold g A
  rw [Real.log_div hN.ne' (by norm_num), Real.log_div hN.ne' (by norm_num),
    Real.log_div hN.ne' (by norm_num), Real.log_div hN.ne' (by norm_num), h30]
  ring

theorem C_ge (N : ℕ) (hN : 1 ≤ N) : A * N - 5 / 2 * Real.log N - 3 ≤ C N := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e := g_comb N h0
  have a1 := T_ge N
  have a2 := T_div_le N 2 hN (by norm_num)
  have a3 := T_div_le N 3 hN (by norm_num)
  have a5 := T_div_le N 5 hN (by norm_num)
  have a30 := T_div_ge N 30 hN (by norm_num)
  push_cast at a2 a3 a5 a30
  unfold C
  linarith

theorem C_le (N : ℕ) (hN : 1 ≤ N) : C N ≤ A * N + 4 * Real.log N + 2 := by
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e := g_comb N h0
  have a1 := T_le N hN
  have a2 := T_div_ge N 2 hN (by norm_num)
  have a3 := T_div_ge N 3 hN (by norm_num)
  have a5 := T_div_ge N 5 hN (by norm_num)
  have a30 := T_div_le N 30 hN (by norm_num)
  push_cast at a2 a3 a5 a30
  unfold C
  linarith

/-- Chebyshev's lower bound, explicit: `ψ(N) ≥ A N - (5/2) log N - 3`. -/
theorem S_ge (N : ℕ) : A * N - 5 / 2 * Real.log N - 3 ≤ S N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  · exact (C_ge N hN).trans (C_le_S N)

end Nagura

namespace Nagura

theorem log2_gt : (0.6931 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
theorem log2_lt : Real.log 2 < (0.6932 : ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)

theorem log3_ge : 19 / 12 * Real.log 2 ≤ Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 19) ≤ Real.log ((3 : ℝ) ^ 12) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log3_le : Real.log 3 ≤ 65 / 41 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 41) ≤ Real.log ((2 : ℝ) ^ 65) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log5_ge : 65 / 28 * Real.log 2 ≤ Real.log 5 := by
  have h : Real.log ((2 : ℝ) ^ 65) ≤ Real.log ((5 : ℝ) ^ 28) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem log5_le : Real.log 5 ≤ 7 / 3 * Real.log 2 := by
  have h : Real.log ((5 : ℝ) ^ 3) ≤ Real.log ((2 : ℝ) ^ 7) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith

theorem A_ge : (0.92 : ℝ) ≤ A := by
  unfold A; nlinarith [log2_gt, log3_ge, log5_ge]

theorem A_le : A ≤ (0.93 : ℝ) := by
  unfold A; nlinarith [log2_lt, log3_le, log5_le, log2_gt]

theorem A_nonneg : 0 ≤ A := le_trans (by norm_num) A_ge

theorem sqrt_le_mul (m : ℝ) (N : ℝ) (k : ℝ) (hk : 0 ≤ k) (h : m ≤ k ^ 2 * N) :
    Real.sqrt m ≤ k * Real.sqrt N := by
  rcases le_or_gt 0 N with hN | hN
  · rw [show k * Real.sqrt N = Real.sqrt (k ^ 2 * N) by
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]]
    exact Real.sqrt_le_sqrt h
  · have : m ≤ 0 := by nlinarith [sq_nonneg k]
    rw [Real.sqrt_eq_zero'.mpr this]
    exact mul_nonneg hk (Real.sqrt_nonneg _)

theorem log_le_two_sqrt (N : ℕ) (hN : 1 ≤ N) : Real.log N ≤ 2 * (Real.sqrt N - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsq : (N : ℝ) = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0.le).symm
  have := Real.log_le_sub_one_of_pos hs
  calc Real.log N = Real.log (Real.sqrt N ^ 2) := by rw [← hsq]
    _ = 2 * Real.log (Real.sqrt N) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ 2 * (Real.sqrt N - 1) := by linarith

theorem cast_div_le' (N d : ℕ) : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le

theorem cast_div_gt (N d : ℕ) : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
  have := Nat.sub_one_lt_floor ((N : ℝ) / d)
  rwa [Nat.floor_div_eq_div] at this

/-- Chebyshev's upper bound, explicit: `ψ(N) ≤ (6/5) A N + 14 √N`. -/
theorem S_le_U1 (N : ℕ) : S N ≤ 6 / 5 * A * N + 14 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have hc := C_le N hN
  have hs := S_upper_aux1 N
  have hm : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := cast_div_le' N 6; push_cast at this; exact this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ 41 / 100 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have hlog := log_le_two_sqrt N hN
  have hA := mul_le_mul_of_nonneg_left hm A_nonneg
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

/-- Bootstrapped upper bound: `ψ(N) ≤ (1026/875) A N + 30 √N`, and `1026/875 < 6/5`. -/
theorem S_le_U2 (N : ℕ) : S N ≤ 1026 / 875 * A * N + 30 * Real.sqrt N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [S]
  have ih6 := ih (N / 6) (Nat.div_lt_self hN (by norm_num))
  have hl7 := S_ge (N / 7)
  have hu10 := S_le_U1 (N / 10)
  have hc := C_le N hN
  have hs := S_upper_aux N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have m6 : ((N / 6 : ℕ) : ℝ) ≤ (N : ℝ) / 6 := by
    have := cast_div_le' N 6; push_cast at this; exact this
  have m7 : (N : ℝ) / 7 - 1 < ((N / 7 : ℕ) : ℝ) := by
    have := cast_div_gt N 7; push_cast at this; exact this
  have m10 : ((N / 10 : ℕ) : ℝ) ≤ (N : ℝ) / 10 := by
    have := cast_div_le' N 10; push_cast at this; exact this
  have sq6 : Real.sqrt ((N / 6 : ℕ) : ℝ) ≤ 41 / 100 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have sq10 : Real.sqrt ((N / 10 : ℕ) : ℝ) ≤ 317 / 1000 * Real.sqrt N :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  have l7 : Real.log ((N / 7 : ℕ) : ℝ) ≤ Real.log N := log_nat_mono (Nat.div_le_self N 7)
  have hlog := log_le_two_sqrt N hN
  have a6 := mul_le_mul_of_nonneg_left m6 A_nonneg
  have a7 := mul_le_mul_of_nonneg_left m7.le A_nonneg
  have a10 := mul_le_mul_of_nonneg_left m10 A_nonneg
  have hAle := A_le
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

theorem theta_eq_of_no_prime (N M : ℕ) (hNM : N ≤ M) (h : ∀ p, p.Prime → N < p → M < p) :
    Chebyshev.theta M = Chebyshev.theta N := by
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, hpM⟩, hp⟩
    refine ⟨⟨h0, ?_⟩, hp⟩
    by_contra hc
    push_neg at hc
    exact absurd hpM (not_le.mpr (h p hp hc))
  · rintro ⟨⟨h0, hpN⟩, hp⟩
    exact ⟨⟨h0, hpN.trans hNM⟩, hp⟩

/-- Nagura's theorem for large `N` (`N ≥ 9 · 10^6`). -/
theorem nagura_large (N : ℕ) (hN : 9000000 ≤ N) : ∃ p, p.Prime ∧ N < p ∧ 5 * p ≤ 6 * N := by
  by_contra hcon
  push_neg at hcon
  set M := 6 * N / 5 with hMdef
  have hNM : N ≤ M := by omega
  have hth : Chebyshev.theta M = Chebyshev.theta N :=
    theta_eq_of_no_prime N M hNM (fun p hp hlt => by have := hcon p hp hlt; omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have h1 := Chebyshev.psi_sub_theta_le hM1
  have h2 := Chebyshev.theta_le_psi (N : ℝ)
  rw [psi_nat] at h1 h2
  have hL := S_ge M
  have hU := S_le_U2 N
  -- real-number bookkeeping
  have hN0 : (9000000 : ℝ) ≤ N := by exact_mod_cast hN
  set s := Real.sqrt (N : ℝ) with hs
  have hsN : (N : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hs3 : (3000 : ℝ) ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hMle : (M : ℝ) ≤ 6 / 5 * N := by
    have : 5 * M ≤ 6 * N := by omega
    have : (5 : ℝ) * M ≤ 6 * N := by exact_mod_cast this
    linarith
  have hMge : (6 * N - 4 : ℝ) / 5 ≤ M := by
    have : 6 * N ≤ 5 * M + 4 := by omega
    have : (6 : ℝ) * N ≤ 5 * M + 4 := by exact_mod_cast this
    linarith
  have hsqM : Real.sqrt (M : ℝ) ≤ 10955 / 10000 * s :=
    sqrt_le_mul _ _ _ (by norm_num) (by nlinarith)
  -- log M ≤ log 2 + 2 log s ≤ 0.7 + 2 (log 3000 + s/3000 - 1)
  have hlogM2 : Real.log M ≤ Real.log 2 + Real.log N := by
    have : M ≤ 2 * N := by omega
    have h := log_nat_mono this
    push_cast at h
    rwa [Real.log_mul (by norm_num) (by positivity)] at h
  have hspos : 0 < s := by linarith
  have hlogN : Real.log N = 2 * Real.log s := by
    rw [hsN, Real.log_pow]; push_cast; ring
  have hlog3000 : Real.log 3000 ≤ 12 * Real.log 2 := by
    have h : Real.log (3000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 12) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at h
  have hlogs : Real.log s ≤ Real.log 3000 + (s / 3000 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < s / 3000 by positivity)
    rw [Real.log_div hspos.ne' (by norm_num)] at h
    linarith
  have hlogMb : Real.log M ≤ 1534 / 100 + s / 1500 := by
    have := log2_lt
    nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hprod : Real.sqrt (M : ℝ) * Real.log M ≤ (10955 / 10000 * s) * (1534 / 100 + s / 1500) :=
    mul_le_mul hsqM hlogMb hlogM0 (by positivity)
  have hAM := mul_le_mul_of_nonneg_left hMge A_nonneg
  have hA := A_ge
  have hAN : 0.92 * (N : ℝ) ≤ A * N := mul_le_mul_of_nonneg_right hA (by linarith)
  have hss : 3000 * s ≤ s * s := by nlinarith
  rw [hsN] at hAN hAM hU
  nlinarith

end Nagura

namespace Nagura

/-- `Good x`: there is a prime `p` with `x < p ≤ 6x/5`. -/
def Good (x : ℕ) : Prop := ∃ p, p.Prime ∧ x < p ∧ 5 * p ≤ 6 * x

/-- `chainOK a l`: each element of `l` is at most `6/5` of its predecessor (starting from `a`). -/
def chainOK : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: t => decide (5 * b ≤ 6 * a) && chainOK b t

theorem chain_cover (l : List ℕ) : ∀ a : ℕ, (∀ p ∈ l, p.Prime) → chainOK a l = true →
    ∀ x, a ≤ x → (∃ p ∈ l, x < p) → Good x := by
  induction l with
  | nil => intro a _ _ x _ ⟨p, hp, _⟩; simp at hp
  | cons b t ih =>
    intro a hpr hch x hax hex
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hch
    by_cases hxb : x < b
    · exact ⟨b, hpr b (by simp), hxb, by omega⟩
    · push_neg at hxb
      apply ih b (fun p hp => hpr p (by simp [hp])) hch.2 x hxb
      obtain ⟨p, hp, hxp⟩ := hex
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · exact ⟨p, hp, hxp⟩

/-- The chain of primes `29, 31, 37, …, 10485721`, each at most `6/5` of the previous. -/
def primeChain : List ℕ := [29, 31, 37, 43, 47, 53, 61, 73, 83, 97, 113, 131, 157, 181, 211, 251, 293, 349, 409, 487, 577, 691, 829, 991, 1187, 1423, 1699, 2029, 2423, 2903, 3469, 4159, 4987, 5981, 7177, 8609, 10321, 12379, 14851, 17807, 21347, 25609, 30727, 36871, 44221, 53051, 63659, 76387, 91639, 109961, 131947, 158329, 189989, 227977, 273569, 328277, 393931, 472711, 567209, 680633, 816743, 980081, 1176089, 1411297, 1693553, 2032253, 2438693, 2926421, 3511693, 4214009, 5056781, 6068137, 7281751, 8738101, 10485721]

theorem primeChain_prime : ∀ p ∈ primeChain, p.Prime := by
  simp only [primeChain, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

theorem primeChain_chain : chainOK 25 primeChain = true := by decide

theorem nagura_small (x : ℕ) (h1 : 25 ≤ x) (h2 : x < 9000000) : Good x :=
  chain_cover primeChain 25 primeChain_prime primeChain_chain x h1
    ⟨10485721, by simp [primeChain], by omega⟩

/-- **Nagura (1952).** For every natural number `x ≥ 25` there is a prime `p`
with `x < p` and `5 p ≤ 6 x`, i.e. `x < p ≤ 6x/5`. -/
theorem nagura (x : ℕ) (hx : 25 ≤ x) : ∃ p, p.Prime ∧ x < p ∧ 5 * p ≤ 6 * x := by
  rcases lt_or_ge x 9000000 with h | h
  · exact nagura_small x hx h
  · exact nagura_large x h

end Nagura



/-! Small cases `n m < 25`, `m ≤ 5`, `m < n`: a prime in `[n m, n (m+1)]`, by `decide`. -/

namespace OMASmall

theorem small_cases_table : ∀ n ∈ Finset.range 25, ∀ m ∈ Finset.range 6,
    (0 < m ∧ m < n ∧ n * m < 25) → ∃ p ∈ Finset.Icc (n * m) (n * (m + 1)), p.Prime := by
  decide

theorem small_cases (n m : ℕ) (hn : n < 25) (hm : m < 6) (h0 : 0 < m) (hmn : m < n)
    (h25 : n * m < 25) : ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  obtain ⟨p, hp, hpr⟩ := small_cases_table n (Finset.mem_range.mpr hn) m
    (Finset.mem_range.mpr hm) ⟨h0, hmn, h25⟩
  rw [Finset.mem_Icc] at hp
  exact ⟨p, hpr, hp.1, hp.2⟩

end OMASmall


namespace OMAPartial

/-- The `m ≤ 5` cases: for `1 ≤ m ≤ 5` and `m < n` there is a prime in `[n m, n (m+1)]`. -/
theorem prime_in_window (n m : ℕ) (hm0 : 0 < m) (hm5 : m ≤ 5) (hmn : m < n) :
    ∃ p, p.Prime ∧ n * m ≤ p ∧ p ≤ n * (m + 1) := by
  by_cases hbig : 25 ≤ n * m
  · obtain ⟨p, hp, h1, h2⟩ := Nagura.nagura (n * m) hbig
    refine ⟨p, hp, h1.le, ?_⟩
    have : 6 * (n * m) ≤ 5 * (n * (m + 1)) := by nlinarith
    omega
  · have hn25 : n < 25 := by nlinarith
    exact OMASmall.small_cases n m hn25 (by omega) hm0 hmn (by omega)

end OMAPartial

theorem OMA.solution : OMA.R_OeisA110835_conjecture_R1.H1 :=
  fun n m h1 h5 hmn => OMAPartial.prime_in_window n m h1 h5 hmn
