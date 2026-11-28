import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H2
-- Credit: @ibrahimshahid1 (agent: Claude Code, model claude-opus-5-5)
--
-- The step H2: n unitary perfect, z the only odd prime with z^2 | n, z one of 43 primes, a = v2(n)
-- even with the residue conditions of the step.  This file PROVES the case 4 | a and leaves the
-- case a = 2 mod 4 open, split by the size of z.
--
-- Method (case 4 | a).  The residue conditions of the step exclude v2(a) = r for r = 2 .. 19
-- (r = 3 allowed only for z = 43), so v2(a) >= 20, or z = 43 and v2(a) = 3.  Every prime p dividing
-- 2^a + 1 then has 2^(v2(a)+1) | p - 1 (two_pow_succ_dvd_sub_one).  As in case_zero_mod_fourL, a prime
-- p0 = 2 mod 3 divides 2^a + 1; it is simple, and it is the only simple parent of 3.  Graham's
-- weights with beta 3 = 4/3 (1 + 1/p0) and beta p0 = 1 + 1/p0 (p0_core, built on master_gen like
-- three_top_core, so no lower bound on z is needed) leave the z-leaves a budget of
-- 2 / (1025/1024 (4/3)^2 (16/15) (64/63) (2048/2047) (1 + 1/p0)), which is above 311/300 for
-- p0 > 2^21: the leaf tables tmass_z of the parent close all 43 primes.  For z = 43 and v2(a) = 3,
-- p0 >= 65 and the leaf table of 43 within 101/100 closes it.
--
-- H1 (OPEN): a = 2 mod 4, z one of the 23 primes 13 <= z <= 127 of the step.
-- H2 (OPEN): a = 2 mod 4, z one of the 20 primes 131 <= z <= 619 of the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (zleaf_bound zleaf_form filter_mem_singleton B_nonneg master_gen
  three_dvd_two_pow_add_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2 hiding H1 H2 H3 main

-- H1: a = v2(n) is bounded when a = 2 mod 4 and the only repeated odd prime z is one of the 23
-- primes 13 <= z <= 127 of the step, under the conditions of the step that survive for a = 2 mod 4.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    padicValNat 2 n % 4 = 2 → (z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    padicValNat 2 n ≤ A

-- H2: the same for the 20 primes 131 <= z <= 619 of the step (each has a heavy z-leaf 2z - 1 or
-- 4z - 1 for the budget 2101/2097 of the parent).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z ∈ ({131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ),
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    padicValNat 2 n % 4 = 2 → (z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n % 20 ≠ 10 → padicValNat 2 n % 28 ≠ 14 →
    padicValNat 2 n ≤ A

-- The 2-adic order of 2 modulo a prime factor of 2^a + 1.
theorem two_pow_succ_dvd_sub_one {p a s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2 ^ a + 1)
    (hs : 2 ^ s ∣ a) : 2 ^ (s + 1) ∣ p - 1 := by
  obtain ⟨t, rfl⟩ := hs
  have := Fact.mk hp
  have hp2' : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hne := one_ne_neg_one_zmod hp2'
  have ha := two_pow_eq_neg_one hd
  have h1 : ((2 : ZMod p) ^ t) ^ (2 ^ s) = -1 := by
    rw [← pow_mul, mul_comm]
    exact ha
  have h2 : ((2 : ZMod p) ^ t) ^ (2 ^ (s + 1)) = 1 := by
    rw [pow_succ, pow_mul, h1]
    norm_num
  have hord : orderOf ((2 : ZMod p) ^ t) = 2 ^ (s + 1) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact fun h => hne h.symm
    · exact h2
  have hy0 : (2 : ZMod p) ^ t ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at h1
    exact one_ne_zero (neg_eq_zero.mp h1.symm)
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hy0

theorem pieceA_mod_step {a r : ℕ} (h0 : a % 2 ^ r = 0) (h1 : a % 2 ^ (r + 1) ≠ 2 ^ r) :
    a % 2 ^ (r + 1) = 0 := by
  rw [Nat.mod_pow_succ, h0] at h1 ⊢
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ r) with h | h
  · rw [h]
    simp
  · rw [h] at h1
    simp at h1

theorem v2_big {a : ℕ} (h4 : a % 4 = 0) (h8 : a % 8 ≠ 4) (h4096 : a % 4096 ≠ 2048)
    (hr : ∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      a % 2 ^ (r + 1) ≠ 2 ^ r) :
    a % 16 = 8 ∨ 2 ^ 20 ∣ a := by
  by_cases h16 : a % 16 = 8
  · exact Or.inl h16
  right
  have e4 : a % 2 ^ 4 = 0 := by
    show a % 16 = 0
    omega
  have e5 : a % 2 ^ 5 = 0 := pieceA_mod_step e4 (hr 4 (by simp))
  have e6 : a % 2 ^ 6 = 0 := pieceA_mod_step e5 (hr 5 (by simp))
  have e7 : a % 2 ^ 7 = 0 := pieceA_mod_step e6 (hr 6 (by simp))
  have e8 : a % 2 ^ 8 = 0 := pieceA_mod_step e7 (hr 7 (by simp))
  have e9 : a % 2 ^ 9 = 0 := pieceA_mod_step e8 (hr 8 (by simp))
  have e10 : a % 2 ^ 10 = 0 := pieceA_mod_step e9 (hr 9 (by simp))
  have e11 : a % 2 ^ 11 = 0 := pieceA_mod_step e10 (hr 10 (by simp))
  have e12 : a % 2 ^ 12 = 0 := pieceA_mod_step (r := 11) e11 (by norm_num; exact h4096)
  have e13 : a % 2 ^ 13 = 0 := pieceA_mod_step e12 (hr 12 (by simp))
  have e14 : a % 2 ^ 14 = 0 := pieceA_mod_step e13 (hr 13 (by simp))
  have e15 : a % 2 ^ 15 = 0 := pieceA_mod_step e14 (hr 14 (by simp))
  have e16 : a % 2 ^ 16 = 0 := pieceA_mod_step e15 (hr 15 (by simp))
  have e17 : a % 2 ^ 17 = 0 := pieceA_mod_step e16 (hr 16 (by simp))
  have e18 : a % 2 ^ 18 = 0 := pieceA_mod_step e17 (hr 17 (by simp))
  have e19 : a % 2 ^ 19 = 0 := pieceA_mod_step e18 (hr 18 (by simp))
  have e20 : a % 2 ^ 20 = 0 := pieceA_mod_step e19 (hr 19 (by simp))
  exact Nat.dvd_of_mod_eq_zero e20

theorem p0_big {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2 ^ a + 1) (h20 : 2 ^ 20 ∣ a) :
    2 ^ 21 + 1 ≤ p := by
  have h := two_pow_succ_dvd_sub_one hp hp2 hd h20
  have h2 := hp.two_le
  have hle : 2 ^ (20 + 1) ≤ p - 1 := Nat.le_of_dvd (by omega) h
  have e : (2 : ℕ) ^ (20 + 1) = 2 ^ 21 := by norm_num
  rw [e] at hle
  omega

theorem p0_big8 {p a : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ a + 1) (h8 : a % 16 = 8) (h3 : p % 3 = 2) :
    65 ≤ p := by
  have h2 := hp.two_le
  have ha0 : a ≠ 0 := by omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h21 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 ha0)).mp hd
    omega
  have h8d : 2 ^ 3 ∣ a := Nat.dvd_of_mod_eq_zero (by show a % 8 = 0; omega)
  have h16 : 2 ^ (3 + 1) ∣ p - 1 := two_pow_succ_dvd_sub_one hp hp2 hd h8d
  have h16' : 16 ∣ p - 1 := by norm_num at h16; exact h16
  have h17 : p ≠ 17 := by
    rintro rfl
    obtain ⟨k, rfl⟩ := h8d
    have hm : (2 ^ (2 ^ 3 * k) + 1) % 17 = 2 := by
      rw [Nat.add_mod, pow_mul, Nat.pow_mod]
      norm_num
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  omega

-- The weight theorem when 3 has exactly one simple parent p0, and p0 has none.
theorem p0_core {m K K' p0 X0 : ℕ} {B : ℚ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hK0 : 0 < K)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 10 ≤ m)
    (h3N : 3 ∉ N) (hp0P : p0 ∈ P) (hX0 : 4 ≤ X0) (hp0X : X0 ≤ p0) (h3p0 : 3 ∣ p0 + 1)
    (h3par : ∀ p ∈ P, 3 ∣ p + 1 → p = p0) (hp0par : ∀ p ∈ P, ¬ p0 ∣ p + 1)
    (hΛ : ∀ L : Finset ℕ, L ⊆ P →
      (∀ q ∈ L, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) ∧ ¬ ∃ k, q + 1 = 2 ^ k) →
      (K' : ℚ) / K * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ B)
    (hfin : 1025 / 1024 * ((4 / 3 * (1 + 1 / (X0 : ℚ))) * (4 / 3) * (16 / 15) * (64 / 63) *
      (2048 / 2047) * B) < 2) : False := by
  classical
  have hp0ne3 : p0 ≠ 3 := by omega
  have hp0prime : p0.Prime := (hP p0 hp0P).1
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 4 / 3 * (1 + 1 / (p0 : ℚ)) else
      if p = p0 then 1 + 1 / (p0 : ℚ) else ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hp0q : (4 : ℚ) ≤ p0 := by exact_mod_cast hX0.trans hp0X
  have hinv0 : 0 < 1 / (p0 : ℚ) := by positivity
  have hinv : 1 / (p0 : ℚ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hp0q
  have b3 : β 3 = 4 / 3 * (1 + 1 / (p0 : ℚ)) := by rw [hβ, if_pos rfl]
  have bp0 : β p0 = 1 + 1 / (p0 : ℚ) := by rw [hβ, if_neg hp0ne3, if_pos rfl]
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ p0 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) := fun c e3 e0 => by
    rw [hβ, if_neg e3, if_neg e0]
  have b7 : β 7 = 4 / 3 := by rw [bd 7 (by norm_num) (by omega)]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [bd 31 (by norm_num) (by omega)]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [bd 127 (by norm_num) (by omega)]; norm_num
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · rw [e3, b3]
      have e1 : (1 : ℚ) + 1 / ((3 : ℕ) : ℚ) = 4 / 3 := by norm_num
      have e2 : (((3 : ℕ) : ℚ) + 1) / (((3 : ℕ) : ℚ) - 1) = 2 := by norm_num
      rw [e1, e2]
      constructor <;> linarith
    by_cases e0 : p = p0
    · rw [e0, bp0]; exact ⟨le_refl _, one_add_le_B hp0prime.two_le⟩
    rw [bd p e3 e0]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK hK0 E β hB
    (fun p hp c _ hcd _ hne => by
      by_cases e3 : c = 3
      · rw [e3] at hcd ⊢
        rw [h3par p hp hcd, b3, bp0]
        norm_num
      by_cases e0 : c = p0
      · rw [e0] at hcd
        exact absurd hcd (hp0par p hp)
      exact absurd (bd c e3 e0) hne)
  have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hp0L : p0 ∉ L := fun h => h3N (hLleaf p0 h 3 Nat.prime_three (by norm_num) h3p0)
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => ∃ k, q + 1 = 2 ^ k) β
  have hrest := hΛ (L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k))
    ((Finset.filter_subset _ _).trans hLP)
    (fun q hq => ⟨hLleaf q (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩)
  have hrest' : (K' : ℚ) / K * ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q ≤ B := by
    refine le_of_eq_of_le ?_ hrest
    congr 1
    refine Finset.prod_congr rfl fun q hq => bd q ?_ ?_
    · intro e
      rw [e] at hq
      exact (Finset.mem_filter.mp hq).2 ⟨2, by norm_num⟩
    · intro e
      rw [e] at hq
      exact hp0L (Finset.mem_filter.mp hq).1
  have hmers : ∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
        (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
    rw [b3, b7, b31, b127]
    refine ⟨by linarith, by norm_num, by norm_num, by norm_num⟩
  have hX0q : (4 : ℚ) ≤ X0 := by exact_mod_cast hX0
  have hb3X : β 3 ≤ 4 / 3 * (1 + 1 / (X0 : ℚ)) := by
    rw [b3]
    have : 1 / (p0 : ℚ) ≤ 1 / (X0 : ℚ) :=
      one_div_le_one_div_of_le (by linarith) (by exact_mod_cast hp0X)
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℚ, Y = (4 / 3 * (1 + 1 / (X0 : ℚ))) * (4 / 3) * (16 / 15) * (64 / 63) *
      (2048 / 2047) := ⟨_, rfl⟩
  have hM : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) ≤ Y := by
    rw [b7, b31, b127, hY]
    linarith
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hrest0 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q :=
    Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1025 / 1024 := by
    have h2 : (2 : ℚ) ^ 10 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 10 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hL1 : (K' : ℚ) / K * ∏ q ∈ L, β q ≤ Y * B := by
    rw [← hsplit]
    calc (K' : ℚ) / K * ((∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q) *
            ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q)
        = (∏ q ∈ L.filter (fun q => ∃ k, q + 1 = 2 ^ k), β q) * ((K' : ℚ) / K *
            ∏ q ∈ L.filter (fun q => ¬ ∃ k, q + 1 = 2 ^ k), β q) := by ring
      _ ≤ Y * B := mul_le_mul (hmers.trans hM) hrest' (mul_nonneg hKr0 hrest0) hY0
  have h2 : (2 : ℚ) ≤ 1025 / 1024 * (Y * B) := by
    refine hmain.trans ?_
    rw [mul_assoc]
    exact mul_le_mul hT hL1 (mul_nonneg hKr0
      (Finset.prod_nonneg fun q hq => (hβpos q hq).le)) (by norm_num)
  rw [← hY] at hfin
  linarith

-- The leaf table of 43 within 101/100 (same table as tmass_43).
theorem tmass_43w (L : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 43 ^ j) :
    (1 + 1 / (((43 : ℕ) : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 101 / 100 :=
  zmass_two (X := 10000) (K := 8) (by norm_num) (by norm_num) (by norm_num) ({5503} : Finset ℕ)
    (by
      intro k hk hk' hq hqX
      interval_cases k <;> first | (norm_num at hqX; done) | (simp; done) | (norm_num at hq))
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]) L hL

-- One repeated prime z >= 13, 4 | a, every prime p = 2 mod 3 dividing 2^a + 1 is at least
-- X0 and differs from z: a <= 9 when the leaf mass and X0 satisfy hfin.
theorem le_nine_four {n z X0 : ℕ} {B : ℚ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime)
    (hzlo : 13 ≤ z) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hmass : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) →
      (1 + 1 / ((z : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ B)
    (hX0 : 4 ≤ X0)
    (hfin : 1025 / 1024 * ((4 / 3 * (1 + 1 / (X0 : ℚ))) * (4 / 3) * (16 / 15) * (64 / 63) *
      (2048 / 2047) * B) < 2)
    (h4 : padicValNat 2 n % 4 = 0)
    (hp0 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ padicValNat 2 n + 1 → p % 3 = 2 → X0 ≤ p ∧ p ≠ z) :
    padicValNat 2 n ≤ 9 := by
  by_contra hcon
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hcon h4 hp0
  have hm : 10 ≤ n.factorization 2 := by omega
  have h2 : 2 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have hz2 : z ≠ 2 := by omega
  obtain ⟨hzn, hsim⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.simple_of_unique_repeated hn0 hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, hn0⟩
  have hze : 2 ≤ n.factorization z :=
    (hz.pow_dvd_iff_le_factorization hn0).mp ((hS z).mpr rfl).2.2
  have hs' : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ ({z} : Finset ℕ) → n.factorization r = 1 :=
    fun r hr hr2 hrN => hsim r hr hr2 (fun e => hrN (Finset.mem_singleton.mpr e))
  have E := kernel_balance (N := {z}) h h2 hs'
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({z} : Finset ℕ)),
      p.Prime ∧ p ≠ 2 := fun p hp => by
    have h1 := (Finset.mem_filter.mp hp).1
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  rw [filter_mem_singleton hzpf hz2, Finset.prod_singleton, Finset.prod_singleton] at E
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ n.factorization z → c ∈ ({z} : Finset ℕ) := fun c hc hd =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow hd))
  have hzq : (13 : ℚ) ≤ z := by exact_mod_cast hzlo
  have hpow : (z : ℚ) ^ 2 ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ (by linarith) hze
  have hpow0 : (0 : ℚ) < (z : ℚ) ^ 2 := by positivity
  have hratio : ((1 + z ^ n.factorization z : ℕ) : ℚ) / ((z ^ n.factorization z : ℕ) : ℚ) ≤
      1 + 1 / (z : ℚ) ^ 2 := by
    push_cast
    rw [div_le_iff₀ (by linarith)]
    have h1 : 1 / (z : ℚ) ^ 2 * (z : ℚ) ^ n.factorization z ≥ 1 := by
      rw [ge_iff_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hpow0]
      linarith
    nlinarith
  have h3N : 3 ∉ ({z} : Finset ℕ) := fun h' => by
    have := Finset.mem_singleton.mp h'
    omega
  obtain ⟨S1, S5, S2, S3, -, -, -, -⟩ := facts hP hK E
  have hmod : (2 ^ n.factorization 2 + 1) % 3 = 2 := by
    obtain ⟨k, hk⟩ : ∃ k, n.factorization 2 = k * 4 := ⟨n.factorization 2 / 4, by omega⟩
    rw [hk, mul_comm, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  obtain ⟨p0, hp0p, hp0d, hp03⟩ := exists_prime_mod3 _ hmod
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hp0d
    omega
  obtain ⟨hX0p, hp0z⟩ := hp0 p0 hp0p hp02 hp0d hp03
  have hp0N : p0 ∉ ({z} : Finset ℕ) := fun h' => hp0z (Finset.mem_singleton.mp h')
  have hp0P := S5 p0 hp0p hp02 hp0N hp0d
  have h3d : 3 ∣ p0 + 1 := by omega
  refine p0_core (N := {z}) hP hK (pow_pos hz.pos _) E hm h3N hp0P hX0 hX0p h3d
    (fun p hp h3p => S2 3 Nat.prime_three (by norm_num) h3N p hp p0 hp0P h3p h3d)
    (fun p hp => S3 p0 hp0p hp02 hp0N hp0d p hp) (fun L hLP hL => ?_) hfin
  have hLp : ∀ q ∈ L, q.Prime := fun q hq => (hP q (hLP hq)).1
  have hform : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j := fun q hq =>
    zleaf_form hz hz2 (hLp q hq) (hP q (hLP hq)).2 (hL q hq).1 (hL q hq).2
  have hprod0 : (0 : ℚ) ≤ ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
    Finset.prod_nonneg fun q hq => B_nonneg (hLp q hq).one_lt.le
  exact (mul_le_mul_of_nonneg_right hratio hprod0).trans
    (hmass L (fun q hq => ⟨hLp q hq, hform q hq⟩))

-- The case 4 | a for the 43 primes of the step.
-- The generic case v2(a) >= 20: X0 = 2^21 + 1, budget 311/300.
theorem four_all_gen {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hzlo : 13 ≤ z)
    (hzhi : z ≤ 619) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (hmass : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * z ^ j) →
      (1 + 1 / ((z : ℚ)) ^ 2) * ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 311 / 300)
    (h4 : padicValNat 2 n % 4 = 0) (h20 : 2 ^ 20 ∣ padicValNat 2 n) :
    padicValNat 2 n ≤ 9 := by
  refine le_nine_four (X0 := 2097153) h hz hzlo hS hmass (by norm_num) (by norm_num) h4 ?_
  intro p hp hp2 hd _
  have hb := p0_big hp hp2 hd h20
  norm_num at hb
  exact ⟨hb, by omega⟩

-- The case z = 43, a = 8 mod 16: X0 = 65, budget 101/100.
theorem four_all_43 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 43)
    (h4 : padicValNat 2 n % 4 = 0) (h8 : padicValNat 2 n % 16 = 8) :
    padicValNat 2 n ≤ 9 := by
  refine le_nine_four (X0 := 65) (B := 101 / 100) h (by norm_num) (by norm_num) hS tmass_43w
    (by norm_num) (by norm_num) h4 ?_
  intro p hp _ hd h3
  have hb := p0_big8 hp hd h8 h3
  exact ⟨hb, by omega⟩

theorem four_all {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hz : z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337, 367, 379, 439, 499, 619} : Finset ℕ))
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z)
    (h4 : padicValNat 2 n % 4 = 0) (hv : 2 ^ 20 ∣ padicValNat 2 n ∨ (z = 43 ∧ padicValNat 2 n % 16 = 8)) :
    padicValNat 2 n ≤ 9 := by
  rcases hv with h20 | ⟨rfl, h8⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_13 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_23 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_29 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_37 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_41 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_43 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_47 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_53 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_59 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_61 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_67 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_71 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_73 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_79 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_83 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_89 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_97 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_101 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_103 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_107 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_109 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_113 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_127 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_131 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_137 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_139 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_157 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_173 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_197 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_199 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_211 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_227 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_229 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_263 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_271 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_307 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_331 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_337 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_367 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_379 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_439 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_499 h4 h20
    · exact four_all_gen h (by norm_num) (by norm_num) (by norm_num) hS tmass_619 h4 h20
  · exact four_all_43 h hS h4 h8

-- The reduction: 4 | a is closed by four_all, a = 2 mod 4 goes to H1 (z <= 127) or H2 (z >= 131).
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max 9 (max A1 A2), fun n h z hz hS d1 d2 d3 d4 d5 d6 d7 d8 => ?_⟩
  have hA1 : A1 ≤ max 9 (max A1 A2) := (le_max_left _ _).trans (le_max_right _ _)
  have hA2 : A2 ≤ max 9 (max A1 A2) := (le_max_right _ _).trans (le_max_right _ _)
  by_cases h4 : padicValNat 2 n % 4 = 0
  · rcases v2_big h4 d5 d7 d8 with h16 | h20
    · have h43 : z = 43 := by
        by_contra hne
        exact d6 hne h16
      exact (four_all h hz hS h4 (Or.inr ⟨h43, h16⟩)).trans (le_max_left _ _)
    · exact (four_all h hz hS h4 (Or.inl h20)).trans (le_max_left _ _)
  · have h42 : padicValNat 2 n % 4 = 2 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h1 n h _ (by simp) hS h42 d2 d3 d4).trans hA1
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2
    · exact (h2 n h _ (by simp) hS h42 d2 d3 (d4 (by norm_num))).trans hA2

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H2_R1
