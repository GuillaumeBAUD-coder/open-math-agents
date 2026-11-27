import FormalConjectures.ErdosProblems.«399»

-- SPDX-License-Identifier: Apache-2.0
-- Copyright 2026 alan-mroczek. Written with Claude (claude-fable-5-2).

-- Problem: Erdős Problem 399 — erdos oblath
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/399.lean:61 (declaration Erdos399.erdos_399.variants.erdos_oblath)
-- Credit: @alan-mroczek (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Idea: reduce to an odd prime exponent p | k (or to exponent 8).  Then n! = d * Q with
-- d = X -+ Y and Q = (X^p -+ Y^p)/(X -+ Y), whose prime factors are p (at most once) or = 1 mod p.
-- An elementary Chebyshev-type inequality (compare sum of log over m = 1 and m = -1 mod p,
-- expanded through von Mangoldt) bounds the part of n! made of prime powers = 1 mod p, which
-- contradicts Q >= (d/2)^(p-1) for n >= 64; for 4 <= n < 64 the 2- and 3-parts of n! divide 3d.

open Finset Nat ArithmeticFunction

namespace EO

lemma hyp_aux (a b M : ℕ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ M / a) :
    (0 < b ∧ b ≤ M) ∧ 0 < a ∧ a ≤ M / b := by
  have h1 := (Nat.le_div_iff_mul_le ha).mp hba
  refine ⟨⟨hb, le_trans (Nat.le_mul_of_pos_right b ha) h1⟩, ha, ?_⟩
  rw [Nat.le_div_iff_mul_le hb, mul_comm]; exact h1

lemma sum_hyp_comm (M : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ d ∈ Ioc 0 M, ∑ t ∈ Ioc 0 (M / d), F d t = ∑ t ∈ Ioc 0 M, ∑ d ∈ Ioc 0 (M / t), F d t := by
  apply Finset.sum_comm'
  intro d t
  simp only [mem_Ioc]
  constructor
  · rintro ⟨⟨h1, _⟩, h3, h4⟩
    obtain ⟨a, b, c⟩ := hyp_aux d t M h1 h3 h4
    exact ⟨⟨b, c⟩, a⟩
  · rintro ⟨⟨h1, h2⟩, h3, _⟩
    obtain ⟨a, b, c⟩ := hyp_aux t d M h3 h1 h2
    exact ⟨a, b, c⟩

lemma sum_div_hyp (M : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ k ∈ Ioc 0 M, ∑ d ∈ k.divisors, F d (k / d) = ∑ d ∈ Ioc 0 M, ∑ t ∈ Ioc 0 (M / d), F d t := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le M), ih]
    have key : ∀ d ∈ Ioc 0 (M + 1), ∑ t ∈ Ioc 0 ((M + 1) / d), F d t
        = ∑ t ∈ Ioc 0 (M / d), F d t + (if d ∣ M + 1 then F d ((M + 1) / d) else 0) := by
      intro d hd
      rw [Nat.succ_div]
      split_ifs with h
      · rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
      · simp
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_Ioc_succ_top (Nat.zero_le M)]
    have h0 : M / (M + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_succ_self M)
    rw [h0]
    simp only [Ioc_self, sum_empty, add_zero]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h1 (Nat.succ_pos M), Nat.le_of_dvd (Nat.succ_pos M) h1⟩, h1⟩
    · rintro ⟨_, h⟩
      exact ⟨h, Nat.succ_ne_zero M⟩

noncomputable def eps (m k : ℕ) : ℝ :=
  (if (k : ZMod m) = 1 then 1 else 0) - (if (k : ZMod m) = -1 then 1 else 0)

noncomputable def P (m d M : ℕ) : ℝ := ∑ t ∈ Ioc 0 M, eps m (d * t)

noncomputable def D (m M : ℕ) : ℝ := ∑ k ∈ Ioc 0 M, eps m k * Real.log k

noncomputable def E (m d N : ℕ) : ℝ := ∑ s ∈ Ioc 0 N, P m d (N / s)

lemma cnt_eq (m : ℕ) (hm : 0 < m) (M : ℕ) (v : ZMod m) (hv : v ≠ 0) :
    ∑ t ∈ Ioc 0 M, (if (t : ZMod m) = v then (1 : ℝ) else 0)
      = (((M + 1) / m : ℕ) : ℝ) + (if v.val < (M + 1) % m then 1 else 0) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have h1 := Nat.count_modEq_card (M + 1) hm v.val
  rw [Nat.count_eq_card_filter_range] at h1
  have h2 : ∑ t ∈ Ioc 0 M, (if (t : ZMod m) = v then (1 : ℝ) else 0)
      = ((filter (fun x => x ≡ v.val [MOD m]) (range (M + 1))).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M)]
    have h0 : ¬ (0 ≡ v.val [MOD m]) := by
      intro h
      apply hv
      rw [← ZMod.natCast_zmod_val v, ← (ZMod.natCast_eq_natCast_iff _ _ _).mpr h]
      simp
    rw [if_neg h0, zero_add]
    apply Finset.sum_congr
    · ext x; simp only [mem_Ioc, mem_Ico]; omega
    · intro t _
      have : ((t : ZMod m) = v) ↔ t ≡ v.val [MOD m] := by
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
      simp only [this]
  rw [h2, h1, Nat.mod_eq_of_lt (ZMod.val_lt v)]
  push_cast
  split_ifs <;> simp

lemma eps_one_mul (m d t : ℕ) (hm : 3 ≤ m) (hd : d % m = 1) : eps m (d * t) = eps m t := by
  have h : (d : ZMod m) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' d 1 m).mpr (by rw [hd, Nat.mod_eq_of_lt (by omega)])
    simpa using this
  unfold eps; rw [Nat.cast_mul, h, one_mul]

lemma P_congr_one (m d M : ℕ) (hm : 3 ≤ m) (hd : d % m = 1) : P m d M = P m 1 M := by
  unfold P
  exact Finset.sum_congr rfl fun t _ => by rw [eps_one_mul m d t hm hd, one_mul]

lemma val_neg_one' (m : ℕ) (hm : 3 ≤ m) : (-1 : ZMod m).val = m - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [ZMod.val_neg_one]; rfl

lemma P_one (m M : ℕ) (hm : 3 ≤ m) : P m 1 M = if 1 < (M + 1) % m then 1 else 0 := by
  have : Fact (1 < m) := ⟨by omega⟩
  unfold P eps
  simp only [one_mul]
  rw [Finset.sum_sub_distrib, cnt_eq m (by omega) M 1 one_ne_zero,
    cnt_eq m (by omega) M (-1) (neg_ne_zero.mpr one_ne_zero)]
  rw [ZMod.val_one m, val_neg_one' m hm]
  have h3 : ¬ (m - 1 < (M + 1) % m) := by
    have := Nat.mod_lt (M + 1) (show 0 < m by omega); omega
  rw [if_neg h3]; simp

lemma P_one_nonneg (m M : ℕ) (hm : 3 ≤ m) : 0 ≤ P m 1 M := by
  rw [P_one m M hm]; split_ifs <;> norm_num

lemma P_one_le (m M : ℕ) (hm : 3 ≤ m) : P m 1 M ≤ 1 := by
  rw [P_one m M hm]; split_ifs <;> norm_num

lemma P_one_eq (m M : ℕ) (hm : 3 ≤ m) (h1 : 1 ≤ M) (h2 : M + 2 ≤ m) : P m 1 M = 1 := by
  rw [P_one m M hm, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]

lemma eps_noncoprime (m d t : ℕ) (h : ¬ Nat.Coprime d m) : eps m (d * t) = 0 := by
  unfold eps
  have h1 : ¬ (((d * t : ℕ) : ZMod m) = 1) := by
    intro h1
    rw [Nat.cast_mul] at h1
    exact h ((ZMod.isUnit_iff_coprime d m).mp (IsUnit.of_mul_eq_one _ h1))
  have h2 : ¬ (((d * t : ℕ) : ZMod m) = -1) := by
    intro h1
    rw [Nat.cast_mul] at h1
    have h3 : (d : ZMod m) * (-(t : ZMod m)) = 1 := by rw [mul_neg, h1, neg_neg]
    exact h ((ZMod.isUnit_iff_coprime d m).mp (IsUnit.of_mul_eq_one _ h3))
  rw [if_neg h1, if_neg h2, sub_zero]

lemma P_noncoprime (m d M : ℕ) (hm : 3 ≤ m) (h : ¬ Nat.Coprime d m) : P m d M = 0 := by
  unfold P
  exact Finset.sum_eq_zero fun t _ => eps_noncoprime m d t h

lemma P_ge (m d M : ℕ) (hm : 3 ≤ m) : -1 ≤ P m d M := by
  have : Fact (1 < m) := ⟨by omega⟩
  by_cases h : Nat.Coprime d m
  · have hdu : (d : ZMod m) * ((d : ZMod m))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one d h
    generalize ((d : ZMod m))⁻¹ = u at hdu
    have e1 : ∀ t : ℕ, ((d * t : ℕ) : ZMod m) = 1 ↔ (t : ZMod m) = u := by
      intro t; rw [Nat.cast_mul]; constructor
      · intro h1
        calc (t : ZMod m) = (d * u) * t := by rw [hdu, one_mul]
          _ = u * (d * t) := by ring
          _ = u := by rw [h1, mul_one]
      · intro h1; rw [h1, hdu]
    have e2 : ∀ t : ℕ, ((d * t : ℕ) : ZMod m) = -1 ↔ (t : ZMod m) = -u := by
      intro t; rw [Nat.cast_mul]; constructor
      · intro h1
        calc (t : ZMod m) = (d * u) * t := by rw [hdu, one_mul]
          _ = u * (d * t) := by ring
          _ = -u := by rw [h1]; ring
      · intro h1; rw [h1, mul_neg, hdu]
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hdu; exact zero_ne_one hdu
    unfold P eps
    simp only [e1, e2]
    rw [Finset.sum_sub_distrib, cnt_eq m (by omega) M u hu0,
      cnt_eq m (by omega) M (-u) (neg_ne_zero.mpr hu0)]
    split_ifs <;> linarith
  · rw [P_noncoprime m d M hm h]; norm_num

lemma P_succ (m d M : ℕ) : P m d (M + 1) = P m d M + eps m (d * (M + 1)) := by
  unfold P; rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]

lemma D_succ (m M : ℕ) : D m (M + 1) = D m M + eps m (M + 1) * Real.log ((M + 1 : ℕ) : ℝ) := by
  unfold D; rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]

lemma D_le (m : ℕ) (hm : 3 ≤ m) (M : ℕ) (hM : 2 ≤ M) :
    D m M ≤ P m 1 M * Real.log M - Real.log 2 := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hD : D m 2 = eps m 1 * Real.log ((1 : ℕ) : ℝ) + eps m 2 * Real.log ((2 : ℕ) : ℝ) := by
      have h1 := D_succ m 1
      have h0 := D_succ m 0
      have hz : D m 0 = 0 := by simp [D]
      rw [hz] at h0
      simp only [zero_add] at h0
      rw [show (1 : ℕ) + 1 = 2 from rfl] at h1
      rw [h1, h0]
    have hP : P m 1 2 = eps m 1 + eps m 2 := by
      have h1 := P_succ m 1 1
      have h0 := P_succ m 1 0
      have hz : P m 1 0 = 0 := by simp [P]
      rw [hz] at h0
      simp only [zero_add, mul_one] at h0
      rw [show (1 : ℕ) + 1 = 2 from rfl] at h1
      simp only [one_mul] at h1
      rw [h1, h0]
    have e1 : eps m 1 = 1 := by
      have := P_one_eq m 1 hm le_rfl (by omega)
      have h0 := P_succ m 1 0
      have hz : P m 1 0 = 0 := by simp [P]
      rw [hz] at h0
      simp only [zero_add, mul_one] at h0
      rw [← h0]; exact this
    rw [hD, hP, e1]
    simp only [Nat.cast_one, Real.log_one, mul_zero, zero_add, Nat.cast_ofNat]
    linarith
  | succ M hM ih =>
    rw [D_succ, P_succ, one_mul, add_mul]
    have h0 := P_one_nonneg m M hm
    have hl : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by push_cast; linarith)
    have := mul_le_mul_of_nonneg_left hl h0
    linarith

lemma D_le' (m : ℕ) (hm : 3 ≤ m) (M : ℕ) (hM : 1 ≤ M) :
    D m M ≤ Real.log M - (if 2 ≤ M then Real.log 2 else 0) := by
  by_cases h : 2 ≤ M
  · rw [if_pos h]
    have h1 := D_le m hm M h
    have h2 := P_one_le m M hm
    have h3 : 0 ≤ Real.log M := Real.log_natCast_nonneg M
    nlinarith
  · have : M = 1 := by omega
    subst this
    rw [if_neg h]
    have h0 := D_succ m 0
    have hz : D m 0 = 0 := by simp [D]
    rw [hz] at h0
    simp only [zero_add, Nat.cast_one, Real.log_one, mul_zero] at h0
    rw [h0]; simp

lemma log_factorial_sum (n : ℕ) : Real.log ((n ! : ℕ) : ℝ) = ∑ s ∈ Ioc 0 n, Real.log s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), ih, add_comm]

lemma log_factorial_ge (n : ℕ) : n * Real.log n - n ≤ Real.log ((n ! : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have hf : (0 : ℝ) < (n ! : ℕ) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hf] at h
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
  linarith

lemma T_le (m : ℕ) (hm : 3 ≤ m) (n : ℕ) :
    ∑ s ∈ Ioc 0 n, D m (n / s) ≤ n - Real.log 2 * ((n / 2 : ℕ) : ℝ) := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : ∀ s ∈ Ioc 0 n, D m (n / s) ≤
      (Real.log n - Real.log s) - (if 2 ≤ n / s then Real.log 2 else 0) := by
    intro s hs
    rw [mem_Ioc] at hs
    have hpos : 1 ≤ n / s := (Nat.le_div_iff_mul_le hs.1).mpr (by omega)
    have h := D_le' m hm (n / s) hpos
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs.1
    have hc : (((n / s : ℕ)) : ℝ) ≤ (n : ℝ) / s := Nat.cast_div_le
    have h2 : Real.log ((n / s : ℕ) : ℝ) ≤ Real.log n - Real.log s := by
      rw [← Real.log_div (by exact_mod_cast (by omega : n ≠ 0)) hs'.ne']
      exact Real.log_le_log (by exact_mod_cast hpos) hc
    linarith
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← log_factorial_sum]
  simp only [sum_const, Nat.card_Ioc, tsub_zero, nsmul_eq_mul]
  have h3 : Real.log 2 * ((n / 2 : ℕ) : ℝ) ≤ ∑ s ∈ Ioc 0 n, (if 2 ≤ n / s then Real.log 2 else 0) := by
    have hsub : Ioc 0 (n / 2) ⊆ Ioc 0 n := Finset.Ioc_subset_Ioc le_rfl (Nat.div_le_self n 2)
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · have : ∀ s ∈ Ioc 0 (n / 2), (if 2 ≤ n / s then Real.log 2 else 0) = Real.log 2 := by
        intro s hs
        rw [mem_Ioc] at hs
        rw [if_pos]
        rw [Nat.le_div_iff_mul_le hs.1]
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hs.2
        omega
      rw [Finset.sum_congr rfl this]
      simp [mul_comm]
    · intro s _ _; split_ifs <;> simp [hl2]
  have h4 := log_factorial_ge n
  linarith

lemma D_eq (m M : ℕ) : D m M = ∑ d ∈ Ioc 0 M, vonMangoldt d * P m d (M / d) := by
  unfold D P
  have h1 : ∀ k ∈ Ioc 0 M, eps m k * Real.log k
      = ∑ d ∈ k.divisors, vonMangoldt d * eps m (d * (k / d)) := by
    intro k _
    rw [← vonMangoldt_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), mul_comm]
  rw [Finset.sum_congr rfl h1, sum_div_hyp M (fun d t => vonMangoldt d * eps m (d * t))]
  exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]

lemma T_eq (m n : ℕ) :
    ∑ s ∈ Ioc 0 n, D m (n / s) = ∑ d ∈ Ioc 0 n, vonMangoldt d * E m d (n / d) := by
  have h1 : ∀ s ∈ Ioc 0 n, D m (n / s)
      = ∑ d ∈ Ioc 0 (n / s), vonMangoldt d * P m d (n / d / s) := by
    intro s _
    rw [D_eq]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm s d]
  rw [Finset.sum_congr rfl h1,
    ← sum_hyp_comm n (fun d s => vonMangoldt d * P m d (n / d / s))]
  exact Finset.sum_congr rfl fun d _ => by unfold E; rw [Finset.mul_sum]

lemma E_ge (m d N : ℕ) (hm : 3 ≤ m) : -(N : ℝ) ≤ E m d N := by
  unfold E
  have : ∑ s ∈ Ioc 0 N, (-1 : ℝ) ≤ ∑ s ∈ Ioc 0 N, P m d (N / s) :=
    Finset.sum_le_sum fun s _ => P_ge m d (N / s) hm
  simpa using this

lemma E_noncoprime (m d N : ℕ) (hm : 3 ≤ m) (h : ¬ Nat.Coprime d m) : E m d N = 0 := by
  unfold E
  exact Finset.sum_eq_zero fun s _ => P_noncoprime m d _ hm h

lemma E_one (m d N : ℕ) (hm : 3 ≤ m) (hd : d % m = 1) :
    (N : ℝ) - ((N / (m - 1) : ℕ) : ℝ) ≤ E m d N := by
  unfold E
  have hsub : Ioc (N / (m - 1)) N ⊆ Ioc 0 N := Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl
  have h1 : ∑ s ∈ Ioc (N / (m - 1)) N, (1 : ℝ) ≤ ∑ s ∈ Ioc (N / (m - 1)) N, P m d (N / s) := by
    refine Finset.sum_le_sum fun s hs => ?_
    rw [mem_Ioc] at hs
    rw [P_congr_one m d _ hm hd]
    have hs0 : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hs.1
    have h1 : 1 ≤ N / s := (Nat.le_div_iff_mul_le hs0).mpr (by omega)
    have h2 : N / s < m - 1 := by
      rw [Nat.div_lt_iff_lt_mul hs0]
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < m - 1)).mp hs.1
      rw [mul_comm]; exact this
    rw [P_one_eq m _ hm h1 (by omega)]
  have h2 : ∑ s ∈ Ioc (N / (m - 1)) N, P m d (N / s) ≤ ∑ s ∈ Ioc 0 N, P m d (N / s) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => by
      rw [P_congr_one m d _ hm hd]; exact P_one_nonneg m _ hm
  have h3 : ∑ s ∈ Ioc (N / (m - 1)) N, (1 : ℝ) = (N : ℝ) - ((N / (m - 1) : ℕ) : ℝ) := by
    simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (Nat.div_le_self _ _)]
  linarith

lemma log_factorial_vM (n : ℕ) :
    Real.log ((n ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 n, vonMangoldt d * ((n / d : ℕ) : ℝ) := by
  rw [log_factorial_sum]
  have h1 : ∀ k ∈ Ioc 0 n, Real.log k = ∑ d ∈ k.divisors, vonMangoldt d := by
    intro k _; rw [vonMangoldt_sum]
  rw [Finset.sum_congr rfl h1, sum_div_hyp n (fun d _ => vonMangoldt d)]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [mul_comm]

lemma master (m : ℕ) (hm : 3 ≤ m) (n : ℕ) (l : ℕ → ℝ)
    (hl : ∀ d ∈ Ioc 0 n, IsPrimePow d →
      (d % m = 1 → l d ≤ 2 - 1 / ((m : ℝ) - 1)) ∧ (¬ Nat.Coprime d m → l d ≤ 1) ∧
      (d % m ≠ 1 → Nat.Coprime d m → l d ≤ 0)) :
    ∑ d ∈ Ioc 0 n, vonMangoldt d * l d * ((n / d : ℕ) : ℝ)
      ≤ Real.log ((n ! : ℕ) : ℝ) + n - Real.log 2 * ((n / 2 : ℕ) : ℝ) := by
  have hT := T_le m hm n
  rw [T_eq] at hT
  have hL := log_factorial_vM n
  have key : ∀ d ∈ Ioc 0 n, vonMangoldt d * l d * ((n / d : ℕ) : ℝ)
      ≤ vonMangoldt d * E m d (n / d) + vonMangoldt d * ((n / d : ℕ) : ℝ) := by
    intro d hd
    by_cases hv : vonMangoldt d = 0
    · rw [hv]; simp
    have hpp : IsPrimePow d := vonMangoldt_ne_zero_iff.mp hv
    have hpos : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    obtain ⟨c1, c2, c3⟩ := hl d hd hpp
    have hN : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ hpos
    by_cases h1 : d % m = 1
    · have hE := E_one m d (n / d) hm h1
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (3 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have hc : (((n / d / (m - 1) : ℕ)) : ℝ) ≤ ((n / d : ℕ) : ℝ) / ((m - 1 : ℕ) : ℝ) := Nat.cast_div_le
      rw [Nat.cast_sub (by omega), Nat.cast_one] at hc
      have := mul_le_mul_of_nonneg_right (c1 h1) hN
      have e : (2 - 1 / ((m : ℝ) - 1)) * ((n / d : ℕ) : ℝ)
          = 2 * ((n / d : ℕ) : ℝ) - ((n / d : ℕ) : ℝ) / ((m : ℝ) - 1) := by ring
      linarith
    · by_cases h2 : Nat.Coprime d m
      · have hE := E_ge m d (n / d) hm
        have := mul_le_mul_of_nonneg_right (c3 h1 h2) hN
        linarith
      · have hE := E_noncoprime m d (n / d) hm h2
        have := mul_le_mul_of_nonneg_right (c2 h2) hN
        linarith
  have := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← hL] at this
  linarith

noncomputable def gd (m d : ℕ) : ℝ := if d.minFac % m = 1 then 1 else 0

noncomputable def Sg (m n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, vonMangoldt d * gd m d * ((n / d : ℕ) : ℝ)

lemma gd_nonneg (m d : ℕ) : 0 ≤ gd m d := by unfold gd; split_ifs <;> norm_num

lemma gd_le (m d : ℕ) : gd m d ≤ 1 := by unfold gd; split_ifs <;> norm_num

lemma Sg_eq (m n : ℕ) :
    Sg m n = ∑ u ∈ Ioc 0 n, ∑ d ∈ u.divisors, vonMangoldt d * gd m d := by
  rw [sum_div_hyp n (fun d _ => vonMangoldt d * gd m d)]
  unfold Sg
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [mul_comm]

lemma log_le_div (m u Q : ℕ) (hu : u ≠ 0) (hQ : Q ∣ u)
    (hg : ∀ q, q.Prime → q ∣ Q → q % m = 1) :
    Real.log Q ≤ ∑ d ∈ u.divisors, vonMangoldt d * gd m d := by
  rw [← vonMangoldt_sum]
  have h1 : ∑ d ∈ Q.divisors, vonMangoldt d = ∑ d ∈ Q.divisors, vonMangoldt d * gd m d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hv : vonMangoldt d = 0
    · rw [hv]; simp
    have hpp := vonMangoldt_ne_zero_iff.mp hv
    have hd1 : d ≠ 1 := hpp.ne_one
    have := hg d.minFac (Nat.minFac_prime hd1)
      ((Nat.minFac_dvd d).trans (Nat.dvd_of_mem_divisors hd))
    unfold gd; rw [if_pos this, mul_one]
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hu hQ)
    (fun d _ _ => mul_nonneg vonMangoldt_nonneg (gd_nonneg m d))

lemma log_le_Sg (m n Q : ℕ) (hQ : Q ∣ n !) (hg : ∀ q, q.Prime → q ∣ Q → q % m = 1) :
    Real.log Q ≤ Sg m n := by
  rw [Sg_eq]
  induction n generalizing Q with
  | zero =>
    have : Q = 1 := by simpa using hQ
    subst this; simp
  | succ n ih =>
    rw [Nat.factorial_succ] at hQ
    obtain ⟨Q1, Q2, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hQ
    have hQ1 : Q1 ≠ 0 := fun h => by subst h; simp at h1
    have hQ2 : Q2 ≠ 0 := fun h => by subst h; exact (Nat.factorial_ne_zero n) (by simpa using h2)
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hQ1) (by exact_mod_cast hQ2)]
    have a := log_le_div m (n + 1) Q1 (Nat.succ_ne_zero n) h1
      (fun q hq hqd => hg q hq (hqd.mul_right _))
    have b := ih Q2 h2 (fun q hq hqd => hg q hq (hqd.mul_left _))
    linarith

lemma pp_good_mod (m d : ℕ) (hm : 3 ≤ m) (hpp : IsPrimePow d) (h : d.minFac % m = 1) :
    d % m = 1 := by
  obtain ⟨q, k, hq, hk, rfl⟩ := hpp
  have hq' : q.Prime := hq.nat_prime
  rw [hq'.pow_minFac hk.ne'] at h
  rw [Nat.pow_mod, h, one_pow, Nat.mod_eq_of_lt (by omega)]

lemma coprime_of_mod_one (m d : ℕ) (h : d % m = 1) : Nat.Coprime d m := by
  apply Nat.coprime_of_mul_modEq_one 1
  rw [mul_one]
  unfold Nat.ModEq
  have h2 := Nat.mod_mod d m
  rw [h] at h2
  rw [h, h2]

lemma master2 (m : ℕ) (hm : 3 ≤ m) (n : ℕ) (c : ℝ) (hc : c ≤ 2 - 1 / ((m : ℝ) - 1))
    (hc0 : 0 ≤ c) (S1 S0 : Finset ℕ)
    (h1 : ∀ d ∈ S1, d ∈ Ioc 0 n ∧ d % m = 1 ∧ d.minFac % m ≠ 1)
    (h0 : ∀ d ∈ S0, d ∈ Ioc 0 n ∧ ¬ Nat.Coprime d m) :
    c * Sg m n + c * ∑ d ∈ S1, vonMangoldt d * ((n / d : ℕ) : ℝ)
        + ∑ d ∈ S0, vonMangoldt d * ((n / d : ℕ) : ℝ)
      ≤ Real.log ((n ! : ℕ) : ℝ) + n - Real.log 2 * ((n / 2 : ℕ) : ℝ) := by
  have hM := master m hm n
    (fun d => c * gd m d + c * (if d ∈ S1 then 1 else 0) + (if d ∈ S0 then 1 else 0)) ?_
  · have e : ∑ d ∈ Ioc 0 n, vonMangoldt d *
          (c * gd m d + c * (if d ∈ S1 then 1 else 0) + (if d ∈ S0 then 1 else 0))
          * ((n / d : ℕ) : ℝ)
        = c * Sg m n + c * ∑ d ∈ S1, vonMangoldt d * ((n / d : ℕ) : ℝ)
          + ∑ d ∈ S0, vonMangoldt d * ((n / d : ℕ) : ℝ) := by
      have i1 : ∑ d ∈ S1, vonMangoldt d * ((n / d : ℕ) : ℝ)
          = ∑ d ∈ Ioc 0 n, (if d ∈ S1 then vonMangoldt d * ((n / d : ℕ) : ℝ) else 0) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (fun d hd => (h1 d hd).1)]
      have i0 : ∑ d ∈ S0, vonMangoldt d * ((n / d : ℕ) : ℝ)
          = ∑ d ∈ Ioc 0 n, (if d ∈ S0 then vonMangoldt d * ((n / d : ℕ) : ℝ) else 0) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (fun d hd => (h0 d hd).1)]
      rw [i1, i0]
      unfold Sg
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> ring
    rw [e] at hM
    exact hM
  · intro d hd hpp
    have hg0 := gd_nonneg m d
    have hg1 := gd_le m d
    refine ⟨fun hd1 => ?_, fun hnc => ?_, fun hd1 hcop => ?_⟩
    · have hS0 : d ∉ S0 := fun h => (h0 d h).2 (coprime_of_mod_one m d hd1)
      rw [if_neg hS0]
      by_cases hS1 : d ∈ S1
      · have : gd m d = 0 := by unfold gd; rw [if_neg (h1 d hS1).2.2]
        rw [if_pos hS1, this]; linarith
      · rw [if_neg hS1]
        nlinarith
    · have hd1 : d % m ≠ 1 := fun h => hnc (coprime_of_mod_one m d h)
      have : gd m d = 0 := by
        unfold gd; rw [if_neg (fun h => hd1 (pp_good_mod m d hm hpp h))]
      have hS1 : d ∉ S1 := fun h => hd1 (h1 d h).2.1
      rw [this, if_neg hS1]
      split_ifs <;> norm_num
    · have : gd m d = 0 := by
        unfold gd; rw [if_neg (fun h => hd1 (pp_good_mod m d hm hpp h))]
      have hS1 : d ∉ S1 := fun h => hd1 (h1 d h).2.1
      have hS0 : d ∉ S0 := fun h => (h0 d h).2 hcop
      rw [this, if_neg hS1, if_neg hS0]; norm_num

lemma L64 (n : ℕ) (hn : 64 ≤ n) : 3.158 * (n : ℝ) ≤ Real.log ((n ! : ℕ) : ℝ) := by
  have h := log_factorial_ge n
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : Real.log 64 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have h3 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h4 := Real.log_two_gt_d9
  nlinarith

lemma logn_le (n : ℕ) (hn : 64 ≤ n) : Real.log n ≤ n / 16 + 1.78 := by
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.log ((n : ℝ) / 16) ≤ n / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h3 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h4 := Real.log_two_lt_d9
  linarith

lemma small (n : ℕ) (h4 : 4 ≤ n) (h64 : n < 64) :
    108 * n ! < (Nat.gcd (n !) (6 ^ n)) ^ 3 ∧ 6 ≤ Nat.gcd (n !) (6 ^ n) := by
  interval_cases n <;> decide +kernel

lemma coprime_c (n Q : ℕ) (h2 : ¬ 2 ∣ Q) (h3 : ¬ 3 ∣ Q) : Nat.Coprime (Nat.gcd (n !) (6 ^ n)) Q := by
  have a2 : Nat.Coprime 2 Q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
  have a3 : Nat.Coprime 3 Q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have a6 : Nat.Coprime 6 Q := by
    rw [show 6 = 2 * 3 from rfl]; exact Nat.Coprime.mul_left a2 a3
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.pow_left n a6)

lemma vM4 : vonMangoldt 4 = Real.log 2 := by
  have := vonMangoldt_apply_pow (n := 2) (k := 2) (by norm_num)
  rw [vonMangoldt_apply_prime Nat.prime_two] at this
  norm_num at this
  exact this

lemma vM9 : vonMangoldt 9 = Real.log 3 := by
  have := vonMangoldt_apply_pow (n := 3) (k := 2) (by norm_num)
  rw [vonMangoldt_apply_prime Nat.prime_three] at this
  norm_num at this
  exact this

lemma log3_ge : (19 / 12 : ℝ) * Real.log 2 ≤ Real.log 3 := by
  have h : Real.log ((2 : ℝ) ^ 19) ≤ Real.log ((3 : ℝ) ^ 12) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

lemma log3_le : Real.log 3 ≤ (8 / 5 : ℝ) * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 8) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

lemma core_prime (p n d Q : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 4 ≤ n) (hN : n ! = d * Q)
    (hsize : d ^ p ≤ 2 ^ (p - 1) * n !)
    (hA1 : ∀ q, q.Prime → q ∣ Q → q % p = 1 ∨ q = p) (hA2 : ¬ p ^ 2 ∣ Q) : False := by
  have hfpos : 0 < n ! := Nat.factorial_pos n
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hN; omega)
  have hQ0 : 0 < Q := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hN; omega)
  -- the good part
  obtain ⟨Q', hQQ, hgood⟩ : ∃ Q', (Q = Q' ∨ (Q = p * Q' ∧ p ≤ n)) ∧
      ∀ q, q.Prime → q ∣ Q' → q % p = 1 := by
    by_cases hpQ : p ∣ Q
    · obtain ⟨Q', rfl⟩ := hpQ
      refine ⟨Q', Or.inr ⟨rfl, ?_⟩, ?_⟩
      · apply (Nat.Prime.dvd_factorial hp).mp
        rw [hN]; exact Dvd.intro (d * Q') (by ring)
      · intro q hq hqd
        rcases hA1 q hq (hqd.mul_left p) with h | h
        · exact h
        · exfalso; subst h
          apply hA2
          rw [pow_two]; exact Nat.mul_dvd_mul_left q hqd
    · refine ⟨Q, Or.inl rfl, ?_⟩
      intro q hq hqd
      rcases hA1 q hq hqd with h | h
      · exact h
      · exfalso; subst h; exact hpQ hqd
  have hQ'0 : 0 < Q' := by
    rcases hQQ with h | ⟨h, _⟩
    · omega
    · exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at h; omega)
  have hQ'dvd : Q' ∣ n ! := by
    rcases hQQ with h | ⟨h, _⟩
    · rw [hN, ← h]; exact Dvd.intro_left d rfl
    · rw [hN, h]; exact Dvd.intro_left (d * p) (by ring)
  have h2Q : ¬ 2 ∣ Q' := fun h => by
    have := hgood 2 Nat.prime_two h
    rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have h3Q : ¬ 3 ∣ Q' := fun h => by
    have := hgood 3 Nat.prime_three h
    rcases Nat.lt_or_ge 3 p with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at this; omega
    · have : p = 3 := by omega
      subst this; omega
  rcases Nat.lt_or_ge n 64 with hsm | hbig
  · -- small n
    obtain ⟨hc3, hc6⟩ := small n hn hsm
    have hcop := coprime_c n Q' h2Q h3Q
    have hcn : Nat.gcd (n !) (6 ^ n) ∣ n ! := Nat.gcd_dvd_left _ _
    have hc6n : Nat.gcd (n !) (6 ^ n) ∣ 6 ^ n := Nat.gcd_dvd_right _ _
    generalize Nat.gcd (n !) (6 ^ n) = c at hc3 hc6 hcop hcn hc6n
    have hc3d : c ∣ d * 3 := by
      rcases hQQ with h | ⟨h, _⟩
      · have : c ∣ d * Q' := by rw [← h, ← hN]; exact hcn
        exact (hcop.dvd_of_dvd_mul_right this).mul_right 3
      · have h1 : c ∣ (d * p) * Q' := by rw [mul_assoc, ← h, ← hN]; exact hcn
        have h2 := hcop.dvd_of_dvd_mul_right h1
        by_cases hp3' : p = 3
        · subst hp3'; exact h2
        · have h6 : Nat.Coprime 6 p := by
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
            intro h6
            have := Nat.le_of_dvd (by norm_num) h6
            interval_cases p <;> first | omega | (norm_num at hp)
          have hcp : Nat.Coprime c p :=
            Nat.Coprime.coprime_dvd_left hc6n (Nat.Coprime.pow_left n h6)
          exact (hcp.dvd_of_dvd_mul_right h2).mul_right 3
    have hle : c ≤ d * 3 := Nat.le_of_dvd (by omega) hc3d
    obtain ⟨j, rfl⟩ : ∃ j, p = j + 3 := ⟨p - 3, by omega⟩
    have hj : j + 3 - 1 = j + 2 := by omega
    rw [hj] at hsize
    have h6j : 6 ^ j ≤ c ^ j := Nat.pow_le_pow_left hc6 j
    have s1 : c ^ (j + 3) ≤ (d * 3) ^ (j + 3) := Nat.pow_le_pow_left hle _
    rw [mul_pow] at s1
    have s2 : d ^ (j + 3) * 3 ^ (j + 3) ≤ (2 ^ (j + 2) * n !) * 3 ^ (j + 3) :=
      Nat.mul_le_mul_right _ hsize
    have s3 : (2 ^ (j + 2) * n !) * 3 ^ (j + 3) = 6 ^ j * (108 * n !) := by
      rw [show (6 : ℕ) = 3 * 2 from rfl, mul_pow]; ring
    have s4 : 6 ^ j * (108 * n !) < 6 ^ j * c ^ 3 :=
      Nat.mul_lt_mul_of_pos_left hc3 (by positivity)
    have s5 : 6 ^ j * c ^ 3 ≤ c ^ j * c ^ 3 := Nat.mul_le_mul_right _ h6j
    have s6 : c ^ j * c ^ 3 = c ^ (j + 3) := (pow_add c j 3).symm
    omega
  · -- large n
    have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hbig
    have hfR : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by exact_mod_cast hfpos
    have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
    have hQ'R : (0 : ℝ) < (Q' : ℝ) := by exact_mod_cast hQ'0
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    have hK : ((p : ℝ) - 1) * Real.log ((n ! : ℕ) : ℝ)
        ≤ ((p : ℝ) - 1) * Real.log 2 + p * Real.log Q := by
      have e : (n !) ^ p = d ^ p * Q ^ p := by rw [hN, mul_pow]
      have hnat : (n !) ^ p ≤ 2 ^ (p - 1) * n ! * Q ^ p := by
        rw [e]; exact Nat.mul_le_mul_right _ hsize
      have hR : (((n ! : ℕ) : ℝ)) ^ p ≤ 2 ^ (p - 1) * ((n ! : ℕ) : ℝ) * (Q : ℝ) ^ p := by
        exact_mod_cast hnat
      have h := Real.log_le_log (by positivity) hR
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) hfR.ne', Real.log_pow, Real.log_pow,
        Nat.cast_sub (by omega)] at h
      push_cast at h
      linarith
    have hSg := log_le_Sg p n Q' hQ'dvd hgood
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    have hQl : Real.log Q ≤ Real.log p + Sg p n ∧ Real.log Q ≤ Real.log n + Sg p n := by
      rcases hQQ with h | ⟨h, hpn⟩
      · rw [h]; constructor <;> linarith
      · rw [h, Nat.cast_mul, Real.log_mul (by positivity) hQ'R.ne']
        have : Real.log p ≤ Real.log n :=
          Real.log_le_log (by positivity) (by exact_mod_cast hpn)
        constructor <;> linarith
    by_cases hp3' : p = 3
    · subst hp3'
      have hM := master2 3 (by norm_num) n (3 / 2) (by norm_num) (by norm_num) {4} {3, 9}
        (by
          intro d hd
          rw [Finset.mem_singleton] at hd
          subst hd
          refine ⟨by rw [mem_Ioc]; omega, by norm_num, by norm_num⟩)
        (by
          intro d hd
          rw [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact ⟨by rw [mem_Ioc]; omega, by decide⟩
          · exact ⟨by rw [mem_Ioc]; omega, by decide⟩)
      rw [Finset.sum_singleton, Finset.sum_pair (by norm_num), vM4, vM9,
        vonMangoldt_apply_prime Nat.prime_three] at hM
      have b2 : (n : ℝ) - 1 ≤ 2 * ((n / 2 : ℕ) : ℝ) := by
        have : n - 1 ≤ 2 * (n / 2) := by omega
        have h' : ((n - 1 : ℕ) : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; linarith
      have b4 : (n : ℝ) - 3 ≤ 4 * ((n / 4 : ℕ) : ℝ) := by
        have : n - 3 ≤ 4 * (n / 4) := by omega
        have h' : ((n - 3 : ℕ) : ℝ) ≤ ((4 * (n / 4) : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; linarith
      have b3 : (n : ℝ) - 2 ≤ 3 * ((n / 3 : ℕ) : ℝ) := by
        have : n - 2 ≤ 3 * (n / 3) := by omega
        have h' : ((n - 2 : ℕ) : ℝ) ≤ ((3 * (n / 3) : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; linarith
      have b9 : (n : ℝ) - 8 ≤ 9 * ((n / 9 : ℕ) : ℝ) := by
        have : n - 8 ≤ 9 * (n / 9) := by omega
        have h' : ((n - 8 : ℕ) : ℝ) ≤ ((9 * (n / 9) : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; linarith
      have hl3 := log3_ge
      have hl3' := log3_le
      have hK' := hK
      push_cast at hK' hQl
      have q2 := mul_le_mul_of_nonneg_right hl2.le (show (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) from Nat.cast_nonneg _)
      have q4 := mul_le_mul_of_nonneg_right hl2.le (show (0:ℝ) ≤ ((n / 4 : ℕ) : ℝ) from Nat.cast_nonneg _)
      have l3lb : (1.0974 : ℝ) ≤ Real.log 3 := by linarith
      have q3 := mul_le_mul_of_nonneg_right l3lb (show (0:ℝ) ≤ ((n / 3 : ℕ) : ℝ) from Nat.cast_nonneg _)
      have q9 := mul_le_mul_of_nonneg_right l3lb (show (0:ℝ) ≤ ((n / 9 : ℕ) : ℝ) from Nat.cast_nonneg _)
      linarith [hQl.1]
    · have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · exfalso
          interval_cases p
          · exact hp3' rfl
          · norm_num at hp
        · exact h
      have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hM := master2 p hp3 n (7 / 4)
        (by
          have : 1 / ((p : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
          linarith) (by norm_num) ∅ ∅ (by simp) (by simp)
      simp only [Finset.sum_empty, mul_zero, add_zero] at hM
      have hL := L64 n hbig
      have hln := logn_le n hbig
      have hlogQ : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ0)
      have hnn : (0 : ℝ) ≤ Real.log 2 * ((n / 2 : ℕ) : ℝ) := by positivity
      have h5 : Real.log ((n ! : ℕ) : ℝ) ≤ Real.log 2 + (5 / 4) * Real.log Q := by
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have : ((p : ℝ) - 1) * Real.log ((n ! : ℕ) : ℝ)
            ≤ ((p : ℝ) - 1) * (Real.log 2 + (5 / 4) * Real.log Q) := by
          have : (p : ℝ) * Real.log Q ≤ (5 / 4) * ((p : ℝ) - 1) * Real.log Q :=
            mul_le_mul_of_nonneg_right (by linarith) hlogQ
          nlinarith
        exact le_of_mul_le_mul_left this hp1
      linarith [hQl.2]

lemma A1 (p : ℕ) (hp : p.Prime) (a b : ℤ) (hab : IsCoprime a b) (q : ℕ) (hq : q.Prime)
    (hdiv : (q : ℤ) ∣ ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i)) :
    q % p = 1 ∨ (q = p ∧ (p : ℤ) ∣ a - b) := by
  haveI := Fact.mk hq
  have hsum : ∑ i ∈ range p, (a : ZMod q) ^ i * (b : ZMod q) ^ (p - 1 - i) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdiv
    push_cast at this
    exact this
  have hpow : (a : ZMod q) ^ p = (b : ZMod q) ^ p := by
    have := geom_sum₂_mul (a : ZMod q) (b : ZMod q) p
    rw [hsum, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hnot : ¬ ((a : ZMod q) = 0 ∧ (b : ZMod q) = 0) := by
    rintro ⟨ha, hb⟩
    have ha' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ha
    have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hb
    have hu := hab.isUnit_of_dvd' ha' hb'
    rw [Int.ofNat_isUnit, Nat.isUnit_iff] at hu
    exact hq.one_lt.ne' hu
  have hB : (b : ZMod q) ≠ 0 := by
    intro hb
    apply hnot
    refine ⟨?_, hb⟩
    rw [hb, zero_pow hp.ne_zero] at hpow
    exact pow_eq_zero_iff hp.ne_zero |>.mp hpow
  have hr : ((a : ZMod q) / b) ^ p = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero _ hB)]
  have hr0 : (a : ZMod q) / b ≠ 0 := by
    intro h; rw [h, zero_pow hp.ne_zero] at hr; exact zero_ne_one hr
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hr) with h1 | h1
  · right
    have hAB : (a : ZMod q) = b := by
      rw [orderOf_eq_one_iff] at h1
      exact (div_eq_one_iff_eq hB).mp h1
    rw [hAB] at hsum
    have hterm : ∀ i ∈ range p, (b : ZMod q) ^ i * (b : ZMod q) ^ (p - 1 - i) = (b : ZMod q) ^ (p - 1) := by
      intro i hi
      rw [mem_range] at hi
      rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_range, nsmul_eq_mul] at hsum
    rcases mul_eq_zero.mp hsum with h | h
    · have hqp : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp h
      have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      refine ⟨hqp', ?_⟩
      rw [← hqp']
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
      push_cast; rw [hAB, sub_self]
    · exact absurd (pow_eq_zero_iff (by have := hp.two_le; omega) |>.mp h) hB
  · left
    have hdvd := ZMod.orderOf_dvd_card_sub_one hr0
    rw [h1] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hq1 : q = p * c + 1 := by have := hq.two_le; omega
    rw [hq1, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]

lemma A2 (p : ℕ) (hp : p.Prime) (hodd : Odd p) (a b : ℤ) (hab : IsCoprime a b) :
    ¬ ((p : ℤ) ^ 2 ∣ ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i)) := by
  intro h
  have hp1 : (p : ℤ) ∣ ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i) :=
    dvd_trans (dvd_pow_self _ two_ne_zero) h
  have hpab : (p : ℤ) ∣ a - b := by
    rcases A1 p hp a b hab p hp hp1 with h1 | ⟨_, h1⟩
    · rw [Nat.mod_self] at h1; omega
    · exact h1
  have hpa : ¬ (p : ℤ) ∣ a := by
    intro ha
    have hb : (p : ℤ) ∣ b := by
      have := dvd_sub ha hpab
      rwa [sub_sub_cancel] at this
    have hu := hab.isUnit_of_dvd' ha hb
    rw [Int.ofNat_isUnit, Nat.isUnit_iff] at hu
    exact hp.one_lt.ne' hu
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 := le_emultiplicity_of_pow_dvd h
  rw [emultiplicity_geom_sum₂_eq_one hpI hodd hpab hpa] at h2
  norm_num at h2

lemma sq_prime (X Y q : ℕ) (hXY : Nat.Coprime X Y) (hq : q.Prime) (hd : q ∣ X ^ 2 + Y ^ 2) :
    q = 2 ∨ q % 4 = 1 := by
  haveI := Fact.mk hq
  have h0 : ((X : ZMod q)) ^ 2 + (Y : ZMod q) ^ 2 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ q).mpr hd
    push_cast at this
    exact this
  have hY : (Y : ZMod q) ≠ 0 := by
    intro hY
    rw [hY, zero_pow two_ne_zero, add_zero] at h0
    have hX : (X : ZMod q) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
    have h1 := (ZMod.natCast_eq_zero_iff _ q).mp hX
    have h2 := (ZMod.natCast_eq_zero_iff _ q).mp hY
    have := Nat.dvd_gcd h1 h2
    rw [hXY] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hY (eq_neg_of_add_eq_zero_left h0)
  rcases hq.eq_two_or_odd with h | h
  · left; exact h
  · right; omega

lemma not8 (X Y : ℕ) (hXY : Nat.Coprime X Y) : ¬ 8 ∣ (X ^ 2 + Y ^ 2) * (X ^ 4 + Y ^ 4) := by
  have hpar : ¬ (X % 2 = 0 ∧ Y % 2 = 0) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
    rw [hXY] at this
    omega
  intro h
  have h8 := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod, Nat.add_mod, Nat.pow_mod, Nat.pow_mod Y, Nat.add_mod (X ^ 4),
    Nat.pow_mod X 4, Nat.pow_mod Y 4] at h8
  have hx : X % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hy : Y % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hx2 : X % 2 = (X % 8) % 2 := by omega
  have hy2 : Y % 2 = (Y % 8) % 2 := by omega
  rw [hx2, hy2] at hpar
  generalize X % 8 = u at *
  generalize Y % 8 = v at *
  interval_cases u <;> interval_cases v <;> simp at h8 hpar


lemma core_four (n d Ee : ℕ) (hn : 4 ≤ n) (hN : n ! = d * Ee) (hsize : d ^ 3 ≤ Ee)
    (h1 : ∀ q, q.Prime → q ∣ Ee → q = 2 ∨ q % 4 = 1) (h2 : ¬ 8 ∣ Ee) : False := by
  have hfpos : 0 < n ! := Nat.factorial_pos n
  have hd0 : 0 < d := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hN; omega)
  have hE0 : 0 < Ee := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hN; omega)
  obtain ⟨e, E2, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hE0.ne'
  have he : e ≤ 2 := by
    by_contra hc
    apply h2
    have : 2 ^ 3 ∣ 2 ^ e := pow_dvd_pow 2 (by omega)
    exact Dvd.dvd.mul_right this E2
  have h2Q : ¬ 2 ∣ E2 := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hgood : ∀ q, q.Prime → q ∣ E2 → q % 4 = 1 := by
    intro q hq hqd
    rcases h1 q hq (hqd.mul_left _) with h | h
    · subst h; exact absurd hqd h2Q
    · exact h
  have h3Q : ¬ 3 ∣ E2 := fun h => by
    have := hgood 3 Nat.prime_three h
    omega
  have h4 : 2 ^ e ∣ 4 := by interval_cases e <;> norm_num
  have hE2dvd : E2 ∣ n ! := by rw [hN]; exact Dvd.intro_left (d * 2 ^ e) (by ring)
  have hE20 : 0 < E2 := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hE0; omega)
  rcases Nat.lt_or_ge n 64 with hsm | hbig
  · obtain ⟨hc3, hc6⟩ := small n hn hsm
    have hcop := coprime_c n E2 h2Q h3Q
    have hcn : Nat.gcd (n !) (6 ^ n) ∣ n ! := Nat.gcd_dvd_left _ _
    generalize Nat.gcd (n !) (6 ^ n) = c at hc3 hc6 hcop hcn
    have h5 : c ∣ (d * 2 ^ e) * E2 := by rw [mul_assoc, ← hN]; exact hcn
    have h6 : c ∣ d * 4 := (hcop.dvd_of_dvd_mul_right h5).trans (Nat.mul_dvd_mul_left d h4)
    have hle : c ≤ d * 4 := Nat.le_of_dvd (by omega) h6
    have s1 : c ^ 3 ≤ (d * 4) ^ 3 := Nat.pow_le_pow_left hle 3
    rw [mul_pow] at s1
    have s2 : 2 ^ e * E2 ≤ n ! := by rw [hN]; exact Nat.le_mul_of_pos_left _ hd0
    omega
  · have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hbig
    have hfR : (0 : ℝ) < ((n ! : ℕ) : ℝ) := by exact_mod_cast hfpos
    have hE2R : (0 : ℝ) < (E2 : ℝ) := by exact_mod_cast hE20
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    have hK : 3 * Real.log ((n ! : ℕ) : ℝ) ≤ 8 * Real.log 2 + 4 * Real.log E2 := by
      have hnat : (n !) ^ 3 ≤ (4 * E2) ^ 4 := by
        have hEe : 2 ^ e * E2 ≤ 4 * E2 := Nat.mul_le_mul_right _ (Nat.le_of_dvd (by norm_num) h4)
        calc (n !) ^ 3 = d ^ 3 * (2 ^ e * E2) ^ 3 := by rw [hN, mul_pow]
          _ ≤ (2 ^ e * E2) * (2 ^ e * E2) ^ 3 := Nat.mul_le_mul_right _ hsize
          _ = (2 ^ e * E2) ^ 4 := by ring
          _ ≤ (4 * E2) ^ 4 := Nat.pow_le_pow_left hEe 4
      have hR : (((n ! : ℕ) : ℝ)) ^ 3 ≤ (4 * (E2 : ℝ)) ^ 4 := by exact_mod_cast hnat
      have h := Real.log_le_log (by positivity) hR
      rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hE2R.ne'] at h
      have h44 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h44] at h
      push_cast at h
      linarith
    have hSg := log_le_Sg 4 n E2 hE2dvd hgood
    have hM := master2 4 (by norm_num) n (5 / 3) (by norm_num) (by norm_num) ∅ {2}
      (by simp)
      (by
        intro d hd
        rw [Finset.mem_singleton] at hd
        subst hd
        exact ⟨by rw [mem_Ioc]; omega, by decide⟩)
    rw [Finset.sum_singleton, Finset.sum_empty, vonMangoldt_apply_prime Nat.prime_two] at hM
    have b2 : (n : ℝ) - 1 ≤ 2 * ((n / 2 : ℕ) : ℝ) := by
      have : n - 1 ≤ 2 * (n / 2) := by omega
      have h' : ((n - 1 : ℕ) : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h'; push_cast at h'; linarith
    have q2 := mul_le_mul_of_nonneg_right hl2.le
      (show (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) from Nat.cast_nonneg _)
    have hL := L64 n hbig
    push_cast at hM
    linarith

lemma core_int (p n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 4 ≤ n) (a b : ℤ)
    (hab : IsCoprime a b) (d : ℕ) (hd : (d : ℤ) = a - b)
    (hN : a ^ p - b ^ p = ((n ! : ℕ) : ℤ)) (hsize : d ^ p ≤ 2 ^ (p - 1) * n !) : False := by
  have hg : (∑ i ∈ range p, a ^ i * b ^ (p - 1 - i)) * (a - b) = a ^ p - b ^ p :=
    geom_sum₂_mul a b p
  rw [hN, ← hd] at hg
  have hfpos : (0 : ℤ) < ((n ! : ℕ) : ℤ) := by exact_mod_cast Nat.factorial_pos n
  have hQpos : 0 < ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i) := by
    by_contra hc
    replace hc := not_lt.mp hc
    have : (∑ i ∈ range p, a ^ i * b ^ (p - 1 - i)) * (d : ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Int.natCast_nonneg d)
    linarith
  obtain ⟨Qn, hQn⟩ := Int.eq_ofNat_of_zero_le hQpos.le
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  apply core_prime p n d Qn hp hp3 hn _ hsize _ _
  · have : ((n ! : ℕ) : ℤ) = ((d * Qn : ℕ) : ℤ) := by
      push_cast; rw [← hQn, ← hg]; ring
    exact_mod_cast this
  · intro q hq hqd
    have : (q : ℤ) ∣ ∑ i ∈ range p, a ^ i * b ^ (p - 1 - i) := by
      rw [hQn]; exact_mod_cast hqd
    rcases A1 p hp a b hab q hq this with h | ⟨h, _⟩
    · left; exact h
    · right; exact h
  · intro h
    apply A2 p hp hodd a b hab
    rw [hQn]; exact_mod_cast h

lemma plus_prime (p n X Y : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 4 ≤ n)
    (hXY : Nat.Coprime X Y) (h : n ! = X ^ p + Y ^ p) : False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  apply core_int p n hp hp3 hn (X : ℤ) (-(Y : ℤ)) (Nat.isCoprime_iff_coprime.mpr hXY).neg_right
    (X + Y) (by push_cast; ring)
  · rw [hodd.neg_pow, h]; push_cast; ring
  · rw [h]; exact add_pow_le (Nat.zero_le _) (Nat.zero_le _) p

lemma minus_prime (p n X Y : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hn : 4 ≤ n)
    (hXY : Nat.Coprime X Y) (h : n ! + Y ^ p = X ^ p) : False := by
  have hfpos : 0 < n ! := Nat.factorial_pos n
  have hlt : Y < X := by
    by_contra hc
    replace hc := Nat.le_of_not_lt hc
    have := Nat.pow_le_pow_left hc p
    omega
  apply core_int p n hp hp3 hn (X : ℤ) (Y : ℤ) (Nat.isCoprime_iff_coprime.mpr hXY)
    (X - Y) (by rw [Nat.cast_sub hlt.le])
  · have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    linarith
  · have h1 : (X - Y) ^ p + Y ^ p ≤ (X - Y + Y) ^ p :=
      pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) hp.ne_zero
    rw [Nat.sub_add_cancel hlt.le] at h1
    have h2 : n ! ≤ 2 ^ (p - 1) * n ! := Nat.le_mul_of_pos_left _ (by positivity)
    omega

lemma minus_eight (n X Y : ℕ) (hn : 4 ≤ n) (hXY : Nat.Coprime X Y)
    (h : n ! + Y ^ 8 = X ^ 8) : False := by
  have hfpos : 0 < n ! := Nat.factorial_pos n
  have hlt : Y < X := by
    by_contra hc
    replace hc := Nat.le_of_not_lt hc
    have := Nat.pow_le_pow_left hc 8
    omega
  have hsq : Y ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hlt.le 2
  apply core_four n (X ^ 2 - Y ^ 2) ((X ^ 2 + Y ^ 2) * (X ^ 4 + Y ^ 4)) hn
  · zify [hsq]
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at this
    linear_combination this
  · have h1 : (X ^ 2 - Y ^ 2) ^ 3 ≤ (X ^ 2) ^ 3 := Nat.pow_le_pow_left (Nat.sub_le _ _) 3
    have h2 : (X ^ 2) ^ 3 ≤ (X ^ 2 + Y ^ 2) * (X ^ 4 + Y ^ 4) := by
      have : (X ^ 2 + Y ^ 2) * (X ^ 4 + Y ^ 4)
          = (X ^ 2) ^ 3 + (X ^ 2 * Y ^ 4 + Y ^ 2 * X ^ 4 + Y ^ 6) := by ring
      omega
    exact h1.trans h2
  · intro q hq hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h1 | h1
    · exact sq_prime X Y q hXY hq h1
    · have hc : Nat.Coprime (X ^ 2) (Y ^ 2) := Nat.Coprime.pow 2 2 hXY
      apply sq_prime (X ^ 2) (Y ^ 2) q hc hq
      rw [← pow_mul, ← pow_mul]; exact h1
  · exact not8 X Y hXY

lemma pow_gap (x y k : ℕ) (hxy : y < x) (hy : 1 ≤ y) (hk : 3 ≤ k) : y ^ k + 7 ≤ x ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (y + 1) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hxy 3
    nlinarith [Nat.mul_le_mul hy hy]
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    have h1 : (y ^ k + 7) * (y + 1) ≤ x ^ k * x := Nat.mul_le_mul ih hxy
    have h2 : (y ^ k + 7) * (y + 1) = y ^ k * y + (y ^ k + 7 * y + 7) := by ring
    omega

lemma exp_cases (k : ℕ) (hk2 : 2 < k) (hk4 : k ≠ 4) :
    8 ∣ k ∨ ∃ p, p.Prime ∧ 3 ≤ p ∧ p ∣ k := by
  obtain ⟨e, m, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  by_cases hm : m = 1
  · subst hm
    left
    have he : 3 ≤ e := by
      by_contra hc
      have : e ≤ 2 := by omega
      interval_cases e <;> omega
    rw [mul_one]
    exact pow_dvd_pow 2 he
  · right
    have hpr := Nat.minFac_prime hm
    refine ⟨m.minFac, hpr, ?_, (Nat.minFac_dvd m).mul_left _⟩
    have h2 : m.minFac ≠ 2 := by
      intro h2
      have := Nat.minFac_dvd m
      rw [h2] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    have := hpr.two_le
    omega

lemma main (n x y k : ℕ) (hxy : x.Coprime y) (h1 : 1 < x * y) (hk2 : 2 < k) (hk4 : k ≠ 4) :
    n ! ≠ x ^ k + y ^ k ∧ n ! + y ^ k ≠ x ^ k := by
  have hx : 1 ≤ x := Nat.pos_of_ne_zero (fun h => by rw [h] at h1; omega)
  have hy : 1 ≤ y := Nat.pos_of_ne_zero (fun h => by rw [h] at h1; omega)
  have hbig : 2 ≤ x ∨ 2 ≤ y := by
    by_contra hc
    rw [not_or] at hc
    have hx1 : x = 1 := by omega
    have hy1 : y = 1 := by omega
    rw [hx1, hy1] at h1; omega
  rcases Nat.lt_or_ge n 4 with hn | hn
  · have hf : n ! ≤ 6 := by interval_cases n <;> decide
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hxk : 1 ≤ x ^ k := Nat.one_le_pow _ _ hx
    have hyk : 1 ≤ y ^ k := Nat.one_le_pow _ _ hy
    constructor
    · intro h
      rcases hbig with hb | hb
      · have := Nat.pow_le_pow_left hb k; omega
      · have := Nat.pow_le_pow_left hb k; omega
    · intro h
      rcases Nat.lt_or_ge y x with hlt | hge
      · have := pow_gap x y k hlt hy (by omega); omega
      · have := Nat.pow_le_pow_left hge k
        have := Nat.factorial_pos n
        omega
  · rcases exp_cases k hk2 hk4 with h8 | ⟨p, hp, hp3, hpk⟩
    · obtain ⟨j, rfl⟩ := h8
      have hj : 1 ≤ j := by omega
      constructor
      · intro h
        have e1 : x ^ (8 * j) = (x ^ (2 * j)) ^ 4 := by rw [← pow_mul]; congr 1; ring
        have e2 : y ^ (8 * j) = (y ^ (2 * j)) ^ 4 := by rw [← pow_mul]; congr 1; ring
        rw [e1, e2] at h
        have hc : Nat.Coprime (x ^ (2 * j)) (y ^ (2 * j)) := Nat.Coprime.pow _ _ hxy
        have hX : 1 ≤ x ^ (2 * j) := Nat.one_le_pow _ _ hx
        have hY : 1 ≤ y ^ (2 * j) := Nat.one_le_pow _ _ hy
        have hprod : 1 < x ^ (2 * j) * y ^ (2 * j) := by
          rcases hbig with hb | hb
          · have : 2 ^ 1 ≤ x ^ (2 * j) :=
              (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hb _)
            nlinarith
          · have : 2 ^ 1 ≤ y ^ (2 * j) :=
              (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hb _)
            nlinarith
        exact Erdos399.erdos_399.variants.cambie hc hprod h
      · intro h
        have e1 : x ^ (8 * j) = (x ^ j) ^ 8 := by rw [← pow_mul]; congr 1; ring
        have e2 : y ^ (8 * j) = (y ^ j) ^ 8 := by rw [← pow_mul]; congr 1; ring
        rw [e1, e2] at h
        exact minus_eight n (x ^ j) (y ^ j) hn (Nat.Coprime.pow _ _ hxy) h
    · obtain ⟨j, rfl⟩ := hpk
      have e1 : x ^ (p * j) = (x ^ j) ^ p := by rw [← pow_mul]; congr 1; ring
      have e2 : y ^ (p * j) = (y ^ j) ^ p := by rw [← pow_mul]; congr 1; ring
      rw [e1, e2]
      exact ⟨fun h => plus_prime p n (x ^ j) (y ^ j) hp hp3 hn (Nat.Coprime.pow _ _ hxy) h,
        fun h => minus_prime p n (x ^ j) (y ^ j) hp hp3 hn (Nat.Coprime.pow _ _ hxy) h⟩

end EO

theorem OMA.solution : type_of% @Erdos399.erdos_399.variants.erdos_oblath := by
  intro n x y k hxy h1 hk2 hk4
  exact EO.main n x y k hxy h1 hk2 hk4
