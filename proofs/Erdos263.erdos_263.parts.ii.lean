import FormalConjectures.ErdosProblems.«263»

/-!
# Erdős Problem 263, part ii

An irrationality sequence need not satisfy `a n ^ (1 / n) → ∞`.

The sequence `OMAaux.seq` creeps upwards by one until `seq n ≤ 2 ^ n`, and then jumps to
`(2 * seq n) ^ (2 * (n + 1))`. The first rule fires infinitely often, so `seq n ^ (1 / n) ≤ 2`
infinitely often and the roots do not tend to infinity.

The jumps are large enough for the classical obstruction to rationality. Let `b` be positive with
`seq n / b n → 1`, and suppose `∑ 1 / b n = p / q`. If `N` is an index just before a jump, then
`q * (b 0 * ⋯ * b N) * ∑_{i > N} 1 / b i` is a positive integer. But the product is at most
`K * (2 * seq N) ^ (N + 1)`, while the tail is at most `(4 * (N + 1) ^ 2 + 4) / seq (N + 1)` with
`seq (N + 1) = (2 * seq N) ^ (2 * (N + 1))`, so this integer is less than one for large `N`.
-/

open Filter

namespace OMAaux

/-- Creep upwards by one until `seq n ≤ 2 ^ n`, then jump. -/
def seq : ℕ → ℕ
  | 0 => 2
  | n + 1 => if seq n ≤ 2 ^ n then (2 * seq n) ^ (2 * (n + 1)) else seq n + 1

lemma seq_zero : seq 0 = 2 := rfl

lemma seq_succ (n : ℕ) :
    seq (n + 1) = if seq n ≤ 2 ^ n then (2 * seq n) ^ (2 * (n + 1)) else seq n + 1 := rfl

lemma seq_jump {n : ℕ} (h : seq n ≤ 2 ^ n) : seq (n + 1) = (2 * seq n) ^ (2 * (n + 1)) := by
  rw [seq_succ, if_pos h]

lemma seq_creep {n : ℕ} (h : 2 ^ n < seq n) : seq (n + 1) = seq n + 1 := by
  rw [seq_succ, if_neg (not_le.mpr h)]

lemma two_le_seq (n : ℕ) : 2 ≤ seq n := by
  induction n with
  | zero => exact le_of_eq seq_zero.symm
  | succ n ih =>
    by_cases h : seq n ≤ 2 ^ n
    · rw [seq_jump h]
      calc 2 ≤ 2 * seq n := by omega
        _ = (2 * seq n) ^ 1 := (pow_one _).symm
        _ ≤ (2 * seq n) ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    · rw [seq_creep (not_le.mp h)]
      omega

lemma seq_lt_succ (n : ℕ) : seq n < seq (n + 1) := by
  have h2 := two_le_seq n
  by_cases h : seq n ≤ 2 ^ n
  · rw [seq_jump h]
    calc seq n < 2 * seq n := by omega
      _ = (2 * seq n) ^ 1 := (pow_one _).symm
      _ ≤ (2 * seq n) ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  · rw [seq_creep (not_le.mp h)]
    omega

lemma strictMono_seq : StrictMono seq := strictMono_nat_of_lt_succ seq_lt_succ

/-- The sequence never falls far below `2 ^ n`. -/
lemma two_pow_lt (n : ℕ) : 2 ^ n < 2 * seq n := by
  induction n with
  | zero =>
    rw [seq_zero]
    norm_num
  | succ n ih =>
    by_cases h : seq n ≤ 2 ^ n
    · rw [seq_jump h]
      have h2 := two_le_seq n
      have h3 : 2 ^ (n + 1) ≤ (2 * seq n) ^ (2 * (n + 1)) :=
        calc 2 ^ (n + 1) ≤ 2 ^ (2 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ (2 * seq n) ^ (2 * (n + 1)) := Nat.pow_le_pow_left (by omega) _
      have h4 : 0 < 2 ^ (n + 1) := by positivity
      omega
    · have h' := not_le.mp h
      rw [seq_creep h', pow_succ]
      omega

lemma two_mul_le_two_pow (m : ℕ) (hm : 1 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

/-- The creeping rule cannot go on for ever: infinitely often `seq n ≤ 2 ^ n`. -/
lemma exists_witness (N : ℕ) : ∃ n, N ≤ n ∧ seq n ≤ 2 ^ n := by
  by_contra hcon
  have hall : ∀ n, N ≤ n → 2 ^ n < seq n := by
    intro n hn
    by_contra h
    exact hcon ⟨n, hn, not_lt.mp h⟩
  have hk : ∀ k, seq (N + k) = seq N + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h1 : seq (N + k + 1) = seq (N + k) + 1 := seq_creep (hall _ (Nat.le_add_right _ _))
      rw [← add_assoc, h1, ih, add_assoc]
  have h1 := hall (N + seq N) (Nat.le_add_right _ _)
  rw [hk (seq N)] at h1
  have h2 : 2 * seq N ≤ 2 ^ seq N :=
    two_mul_le_two_pow _ (le_trans (by norm_num) (two_le_seq N))
  have h3 : 2 ^ seq N ≤ 2 ^ (N + seq N) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  omega

lemma not_tendsto :
    ¬ Tendsto (fun n : ℕ => (seq n : ℝ) ^ (1 / (n : ℝ))) atTop atTop := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_gt_atTop (2 : ℝ))
  obtain ⟨n, hn, hle⟩ := exists_witness (max N 1)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hlt := hN n (le_trans (le_max_left _ _) hn)
  have hle' : (seq n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hle
  have h1 : (seq n : ℝ) ^ (1 / (n : ℝ)) ≤ ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hle' (by positivity)
  have h2 : ((2 : ℝ) ^ n) ^ (1 / (n : ℝ)) = 2 := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by omega)
  linarith

lemma four_sq_lt (m : ℕ) (hm : 9 ≤ m) : 4 * m ^ 2 + 4 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2 m]
    nlinarith [ih, Nat.mul_le_mul_left m hm]

lemma poly_lt_exp (C : ℕ) :
    ∃ N₁, ∀ N, N₁ ≤ N → C * (4 * (N + 1) ^ 2 + 4) < 4 ^ (N + 1) := by
  refine ⟨max C 8, fun N hN => ?_⟩
  have hC : C ≤ N := le_trans (le_max_left _ _) hN
  have h8 : 8 ≤ N := le_trans (le_max_right _ _) hN
  have h1 : 4 * (N + 1) ^ 2 + 4 < 2 ^ (N + 1) := four_sq_lt (N + 1) (by omega)
  have h2 : C ≤ 2 ^ (N + 1) := by
    have := two_mul_le_two_pow (N + 1) (by omega)
    omega
  have h3 : (4 : ℕ) ^ (N + 1) = 2 ^ (N + 1) * 2 ^ (N + 1) := by
    rw [← mul_pow]
    norm_num
  calc C * (4 * (N + 1) ^ 2 + 4) ≤ 2 ^ (N + 1) * (4 * (N + 1) ^ 2 + 4) :=
        Nat.mul_le_mul_right _ h2
    _ < 2 ^ (N + 1) * 2 ^ (N + 1) := mul_lt_mul_of_pos_left h1 (by positivity)
    _ = 4 ^ (N + 1) := h3.symm

/-- A tail bound: the first `M` terms are bounded by `c`, the rest geometrically. -/
lemma tail_le (F : ℕ → ℝ) (hF : Summable F) (m M : ℕ) (c : ℝ)
    (h1 : ∀ n, m ≤ n → F n ≤ c) (h2 : ∀ n, m ≤ n → F n ≤ 4 * (1 / 2 : ℝ) ^ n) :
    ∑' j, F (j + m) ≤ M * c + 8 * (1 / 2 : ℝ) ^ (m + M) := by
  have hs1 : Summable (fun j => F (j + m)) := (summable_nat_add_iff m).mpr hF
  have hs2 : Summable (fun j => F (j + M + m)) := by
    have h := (summable_nat_add_iff (M + m)).mpr hF
    simpa [add_assoc] using h
  have hsplit := hs1.sum_add_tsum_nat_add M
  have hA : ∑ i ∈ Finset.range M, F (i + m) ≤ M * c := by
    calc ∑ i ∈ Finset.range M, F (i + m) ≤ ∑ _i ∈ Finset.range M, c :=
          Finset.sum_le_sum (fun i _ => h1 _ (Nat.le_add_left _ _))
      _ = M * c := by simp
  have hg : Summable (fun i : ℕ => 4 * (1 / 2 : ℝ) ^ (m + M) * (1 / 2 : ℝ) ^ i) :=
    summable_geometric_two.mul_left _
  have hB : ∑' i, F (i + M + m) ≤ 8 * (1 / 2 : ℝ) ^ (m + M) := by
    calc ∑' i, F (i + M + m)
          ≤ ∑' i : ℕ, 4 * (1 / 2 : ℝ) ^ (m + M) * (1 / 2 : ℝ) ^ i := by
          refine hs2.tsum_le_tsum (fun i => ?_) hg
          calc F (i + M + m) ≤ 4 * (1 / 2 : ℝ) ^ (i + M + m) := h2 _ (Nat.le_add_left _ _)
            _ = 4 * (1 / 2 : ℝ) ^ (m + M) * (1 / 2 : ℝ) ^ i := by
              rw [show i + M + m = (m + M) + i by omega, pow_add]
              ring
      _ = 4 * (1 / 2 : ℝ) ^ (m + M) * 2 := by rw [tsum_mul_left, tsum_geometric_two]
      _ = 8 * (1 / 2 : ℝ) ^ (m + M) := by ring
  linarith

/-- Every positive sequence asymptotic to `seq` has an irrational sum of reciprocals. -/
lemma irrational_of_asymp (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)
    (hab : Tendsto (fun n : ℕ => (seq n : ℝ) / (b n : ℝ)) atTop (nhds 1)) :
    Irrational (∑' n, 1 / (b n : ℝ)) := by
  have hbpos : ∀ n, (0 : ℝ) < b n := fun n => by exact_mod_cast hb n
  have hspos : ∀ n, (0 : ℝ) < seq n := fun n => by
    have h := two_le_seq n
    exact_mod_cast (by omega : 0 < seq n)
  -- eventually `seq n / 2 ≤ b n ≤ 2 * seq n`
  have hev : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) < (seq n : ℝ) / (b n : ℝ) ∧ (seq n : ℝ) / (b n : ℝ) < 2 :=
    (hab.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).and
      (hab.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  have hb_le : ∀ n, n₀ ≤ n → b n ≤ 2 * seq n := by
    intro n hn
    have h := (hn₀ n hn).1
    rw [lt_div_iff₀ (hbpos n)] at h
    have h' : (b n : ℝ) ≤ 2 * (seq n : ℝ) := by linarith
    exact_mod_cast h'
  have hb_ge : ∀ n, n₀ ≤ n → (seq n : ℝ) ≤ 2 * (b n : ℝ) := by
    intro n hn
    have h := (hn₀ n hn).2
    rw [div_lt_iff₀ (hbpos n)] at h
    linarith
  -- the terms of the series
  have hFpos : ∀ n, 0 < 1 / (b n : ℝ) := fun n => one_div_pos.mpr (hbpos n)
  have hF1 : ∀ n, n₀ ≤ n → 1 / (b n : ℝ) ≤ 2 / (seq n : ℝ) := by
    intro n hn
    rw [div_le_div_iff₀ (hbpos n) (hspos n)]
    linarith [hb_ge n hn]
  have hF2 : ∀ n, n₀ ≤ n → 1 / (b n : ℝ) ≤ 4 * (1 / 2 : ℝ) ^ n := by
    intro n hn
    have h1 := hF1 n hn
    have h2 : (2 : ℝ) ^ n < 2 * (seq n : ℝ) := by exact_mod_cast two_pow_lt n
    have h3 : 2 / (seq n : ℝ) ≤ 4 * (1 / 2 : ℝ) ^ n := by
      rw [one_div_pow, mul_one_div, div_le_div_iff₀ (hspos n) (by positivity)]
      linarith
    linarith
  have hsum : Summable (fun n => 1 / (b n : ℝ)) := by
    rw [← summable_nat_add_iff n₀]
    refine Summable.of_nonneg_of_le (fun k => (hFpos _).le)
      (fun k => hF2 _ (Nat.le_add_left _ _)) ?_
    exact (summable_nat_add_iff n₀).mpr (summable_geometric_two.mul_left 4)
  -- suppose the sum is rational
  rintro ⟨q, hq⟩
  obtain ⟨N₁, hN₁⟩ := poly_lt_exp (q.den * ∏ i ∈ Finset.range n₀, b i)
  obtain ⟨N, hN, hwit⟩ := exists_witness (max n₀ N₁)
  have hN0 : n₀ ≤ N := le_trans (le_max_left _ _) hN
  have hkey := hN₁ N (le_trans (le_max_right _ _) hN)
  have hA4 : 4 ≤ 2 * seq N := by
    have h := two_le_seq N
    omega
  have hApos : (0 : ℝ) < ((2 * seq N : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * seq N)
  have hAp : (0 : ℝ) < ((2 * seq N : ℕ) : ℝ) ^ (N + 1) := pow_pos hApos _
  have hGpos : (0 : ℝ) < ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := pow_pos hApos _
  have hG : seq (N + 1) = (2 * seq N) ^ (2 * (N + 1)) := seq_jump hwit
  -- the product of the first `N + 1` terms of `b`
  have hDle : ∏ i ∈ Finset.range (N + 1), b i
      ≤ (∏ i ∈ Finset.range n₀, b i) * (2 * seq N) ^ (N + 1) := by
    rw [← Finset.prod_range_mul_prod_Ico b (show n₀ ≤ N + 1 by omega)]
    refine Nat.mul_le_mul_left _ ?_
    calc ∏ i ∈ Finset.Ico n₀ (N + 1), b i ≤ ∏ _i ∈ Finset.Ico n₀ (N + 1), 2 * seq N := by
          refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i hi => ?_)
          have hi' := Finset.mem_Ico.mp hi
          have h1 := hb_le i hi'.1
          have h2 : seq i ≤ seq N := strictMono_seq.monotone (by omega)
          omega
      _ = (2 * seq N) ^ (N + 1 - n₀) := by simp
      _ ≤ (2 * seq N) ^ (N + 1) := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  -- the tail after index `N`
  have hT1 : ∀ n, N + 1 ≤ n →
      1 / (b n : ℝ) ≤ 2 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
    intro n hn
    have ha := hF1 n (by omega)
    have hmono : seq (N + 1) ≤ seq n := strictMono_seq.monotone hn
    have hcast : ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) ≤ (seq n : ℝ) := by
      rw [hG] at hmono
      exact_mod_cast hmono
    have hb2 : 2 / (seq n : ℝ) ≤ 2 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
      rw [div_le_div_iff₀ (hspos n) hGpos]
      linarith
    linarith
  have hT := tail_le (fun n => 1 / (b n : ℝ)) hsum (N + 1) (2 * (N + 1) ^ 2)
    (2 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1))) hT1 (fun n hn => hF2 n (by omega))
  have hpow : (2 * seq N) ^ (2 * (N + 1)) ≤ 2 ^ (2 * (N + 1) ^ 2) := by
    calc (2 * seq N) ^ (2 * (N + 1)) ≤ (2 ^ (N + 1)) ^ (2 * (N + 1)) :=
          Nat.pow_le_pow_left (by rw [pow_succ]; omega) _
      _ = 2 ^ (2 * (N + 1) ^ 2) := by
          rw [← pow_mul]
          congr 1
          ring
  have hhalf : (1 / 2 : ℝ) ^ (2 * (N + 1) ^ 2)
      ≤ 1 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
    rw [one_div_pow]
    apply one_div_le_one_div_of_le hGpos
    exact_mod_cast hpow
  have hsmall : 8 * (1 / 2 : ℝ) ^ (N + 1 + 2 * (N + 1) ^ 2)
      ≤ 4 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
    have h1 : (1 / 2 : ℝ) ^ (N + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * (N + 1) ^ 2) := by positivity
    have h3 := mul_le_mul h1 hhalf h0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have e : 4 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1))
        = 8 * (1 / 2 * (1 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)))) := by ring
    rw [pow_add, e]
    linarith
  have hTle : ∑' j, 1 / (b (j + (N + 1)) : ℝ)
      ≤ (4 * ((N : ℝ) + 1) ^ 2 + 4) / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
    calc ∑' j, 1 / (b (j + (N + 1)) : ℝ)
          ≤ ((2 * (N + 1) ^ 2 : ℕ) : ℝ) * (2 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)))
            + 8 * (1 / 2 : ℝ) ^ (N + 1 + 2 * (N + 1) ^ 2) := hT
      _ ≤ ((2 * (N + 1) ^ 2 : ℕ) : ℝ) * (2 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)))
            + 4 / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by linarith
      _ = (4 * ((N : ℝ) + 1) ^ 2 + 4) / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1)) := by
          push_cast
          ring
  have hTpos : 0 < ∑' j, 1 / (b (j + (N + 1)) : ℝ) :=
    ((summable_nat_add_iff (N + 1)).mpr hsum).tsum_pos (fun j => (hFpos _).le) 0 (hFpos _)
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  -- `D * (partial sum)` is an integer
  have hDS : ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ)
        * ∑ i ∈ Finset.range (N + 1), 1 / (b i : ℝ)
      = ((∑ i ∈ Finset.range (N + 1), ∏ j ∈ (Finset.range (N + 1)).erase i, b j : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hmul : b i * ∏ j ∈ (Finset.range (N + 1)).erase i, b j
        = ∏ j ∈ Finset.range (N + 1), b j := Finset.mul_prod_erase _ b hi
    have hbi : (b i : ℝ) ≠ 0 := (hbpos i).ne'
    rw [← hmul]
    push_cast
    field_simp
  have hqd : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast Rat.mul_den_eq_num q
  have hTeq : ∑' j, 1 / (b (j + (N + 1)) : ℝ)
      = (q : ℝ) - ∑ i ∈ Finset.range (N + 1), 1 / (b i : ℝ) := by
    rw [hq]
    linarith
  have hint : ((q.den : ℝ) * ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ))
        * ∑' j, 1 / (b (j + (N + 1)) : ℝ)
      = (((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℤ) * q.num
          - (q.den : ℤ) * ((∑ i ∈ Finset.range (N + 1),
              ∏ j ∈ (Finset.range (N + 1)).erase i, b j : ℕ) : ℤ) : ℤ) := by
    push_cast
    rw [hTeq, ← hqd]
    have h := hDS
    push_cast at h
    rw [← h]
    ring
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hDpos : (0 : ℝ) < ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hb i)
  have hDle' : ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ)
      ≤ ((∏ i ∈ Finset.range n₀, b i : ℕ) : ℝ) * ((2 * seq N : ℕ) : ℝ) ^ (N + 1) := by
    exact_mod_cast hDle
  have hkey' : (q.den : ℝ) * ((∏ i ∈ Finset.range n₀, b i : ℕ) : ℝ)
        * (4 * ((N : ℝ) + 1) ^ 2 + 4) < ((2 * seq N : ℕ) : ℝ) ^ (N + 1) := by
    have h1 : q.den * (∏ i ∈ Finset.range n₀, b i) * (4 * (N + 1) ^ 2 + 4)
        < (2 * seq N) ^ (N + 1) := lt_of_lt_of_le hkey (Nat.pow_le_pow_left hA4 _)
    exact_mod_cast h1
  have hGe : ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1))
      = ((2 * seq N : ℕ) : ℝ) ^ (N + 1) * ((2 * seq N : ℕ) : ℝ) ^ (N + 1) := by
    rw [← pow_add]
    congr 1
    ring
  have hlt : ((q.den : ℝ) * ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ))
        * ∑' j, 1 / (b (j + (N + 1)) : ℝ) < 1 := by
    have hne : ((2 * seq N : ℕ) : ℝ) ^ (N + 1) ≠ 0 := hAp.ne'
    calc ((q.den : ℝ) * ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ))
          * ∑' j, 1 / (b (j + (N + 1)) : ℝ)
          ≤ ((q.den : ℝ) * (((∏ i ∈ Finset.range n₀, b i : ℕ) : ℝ)
              * ((2 * seq N : ℕ) : ℝ) ^ (N + 1)))
            * ((4 * ((N : ℝ) + 1) ^ 2 + 4) / ((2 * seq N : ℕ) : ℝ) ^ (2 * (N + 1))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hDle' hden.le) hTle hTpos.le (by positivity)
      _ = ((q.den : ℝ) * ((∏ i ∈ Finset.range n₀, b i : ℕ) : ℝ)
            * (4 * ((N : ℝ) + 1) ^ 2 + 4)) / ((2 * seq N : ℕ) : ℝ) ^ (N + 1) := by
          rw [hGe]
          field_simp
      _ < 1 := by
          rw [div_lt_one hAp]
          exact hkey'
  have hpos : (0 : ℝ) < ((q.den : ℝ) * ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℝ))
      * ∑' j, 1 / (b (j + (N + 1)) : ℝ) := mul_pos (mul_pos hden hDpos) hTpos
  rw [hint] at hpos hlt
  have hz0 : (0 : ℤ) < ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℤ) * q.num
      - (q.den : ℤ) * ((∑ i ∈ Finset.range (N + 1),
          ∏ j ∈ (Finset.range (N + 1)).erase i, b j : ℕ) : ℤ) := by
    exact_mod_cast hpos
  have hz1 : ((∏ i ∈ Finset.range (N + 1), b i : ℕ) : ℤ) * q.num
      - (q.den : ℤ) * ((∑ i ∈ Finset.range (N + 1),
          ∏ j ∈ (Finset.range (N + 1)).erase i, b j : ℕ) : ℤ) < 1 := by
    exact_mod_cast hlt
  omega

end OMAaux

theorem OMA.solution : type_of% @Erdos263.erdos_263.parts.ii := by
  intro h
  exact OMAaux.not_tendsto (h OMAaux.seq
    ⟨fun n => lt_of_lt_of_le (by norm_num) (OMAaux.two_le_seq n), OMAaux.strictMono_seq,
      fun b hb => OMAaux.irrational_of_asymp b hb.1 hb.2⟩)
