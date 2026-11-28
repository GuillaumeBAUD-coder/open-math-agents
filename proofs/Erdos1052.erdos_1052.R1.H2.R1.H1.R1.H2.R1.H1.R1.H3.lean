import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1
import Mathlib

-- Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H3: hypothesis H3 of reduction
-- Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1
-- Credit: @SlipstreamAI

/-!
# Unitary perfect numbers with odd core 5^2 and 4 dividing the 2-adic exponent

The step is vacuous: no unitary perfect number n has 5 as its only repeated odd prime,
n.factorization 5 = 2, 43 <= a = v2(n), 4 | a, and v2(a) outside R5 = {2..19, ...}.

Part 1: From 4 | a and v2(a) not in {2..19}, we get 2^20 | a (so a >= 2^20 >= 64).
Every odd prime q | 2^a + 1 has 2^21 | q - 1 (hence q >= 2097153). Since 2^a + 1 = 2 (mod 3),
some prime q = 2 (mod 3) divides 2^a + 1, forcing 3 in P and forcing every p in P with 3 | p + 1
to satisfy 2097153 <= p and 2097152 | p - 1. Applying `master_gen` with the core-25 weights
adjusted at 3 (bw 3 = 1048577 / 786432) forces both 19 in P and 79 in P.

Part 2: With 3, 7, 13, 19, 79 in P, the two primes 19 and 79 exhaust the 5^2 ledger
(5^2 | (19 + 1) * (79 + 1)), so no other simple prime p has 5 | p + 1. A verified finite
branch-and-bound tree closes the remaining space via abundancy jumps, window sieving,
and `path_bound` + `tail_bound`, checked by `decide +kernel`.
-/

namespace OMA.P_Erdos1052_z5_e2_even

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts master_gen mersenne_bound
  path_bound tail_bound exists_child two_mul_le B_step B_anti B_nonneg one_add_le_B
  two_pow_of_no_odd_prime two_pow_mul_pow_of_odd_primes_eq exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (setup hK5)

-- =============================================================================
-- Part 1: 2^20 | a, large source of 3, and forcing 19 in P and 79 in P
-- =============================================================================

theorem step_pow2 {a r : ℕ} (h1 : 2 ^ r ∣ a) (h2 : a % 2 ^ (r + 1) ≠ 2 ^ r) :
    2 ^ (r + 1) ∣ a := by
  obtain ⟨k, rfl⟩ := h1
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨j, by rw [pow_succ]; ring⟩
  · exfalso
    apply h2
    have hpow : 2 ^ (r + 1) = 2 ^ r * 2 := by rw [pow_succ]
    rw [hpow, show 2 ^ r * (2 * j + 1) = (2 ^ r * 2) * j + 2 ^ r by ring,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.two_pow_pos r; omega)]

theorem two_pow_20_dvd {a : ℕ} (ha4 : a % 4 = 0)
    (hR : ∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
      21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ), a % 2 ^ (r + 1) ≠ 2 ^ r) :
    2 ^ 20 ∣ a := by
  have h2 : 2 ^ 2 ∣ a := Nat.dvd_of_mod_eq_zero ha4
  have h3 := step_pow2 h2 (hR 2 (by decide))
  have h4 := step_pow2 h3 (hR 3 (by decide))
  have h5 := step_pow2 h4 (hR 4 (by decide))
  have h6 := step_pow2 h5 (hR 5 (by decide))
  have h7 := step_pow2 h6 (hR 6 (by decide))
  have h8 := step_pow2 h7 (hR 7 (by decide))
  have h9 := step_pow2 h8 (hR 8 (by decide))
  have h10 := step_pow2 h9 (hR 9 (by decide))
  have h11 := step_pow2 h10 (hR 10 (by decide))
  have h12 := step_pow2 h11 (hR 11 (by decide))
  have h13 := step_pow2 h12 (hR 12 (by decide))
  have h14 := step_pow2 h13 (hR 13 (by decide))
  have h15 := step_pow2 h14 (hR 14 (by decide))
  have h16 := step_pow2 h15 (hR 15 (by decide))
  have h17 := step_pow2 h16 (hR 16 (by decide))
  have h18 := step_pow2 h17 (hR 17 (by decide))
  have h19 := step_pow2 h18 (hR 18 (by decide))
  exact step_pow2 h19 (hR 19 (by decide))

theorem prime_large_21 {m q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 2 ^ 20 ∣ m) (hd : q ∣ 2 ^ m + 1) : 2097153 ≤ q ∧ 2097152 ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hm
  have hz : ((2 ^ (2 ^ 20 * k) + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
  rw [Nat.mul_comm (2 ^ 20) k, pow_mul] at hz
  let x : ZMod q := (2 : ZMod q) ^ k
  have hx : x ^ (2 ^ 20 : ℕ) = -1 := by
    change ((2 : ZMod q) ^ k) ^ (2 ^ 20 : ℕ) = -1
    linear_combination hz
  have hn : x ^ (2 ^ 20 : ℕ) ≠ 1 := by
    intro he
    have hzero : ((2 : ℕ) : ZMod q) = 0 := by rw [Nat.cast_ofNat]; linear_combination hx - he
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff _ _).1 hzero))
  have he : x ^ (2 ^ (20 + 1) : ℕ) = 1 := by
    rw [pow_succ (2 : ℕ), pow_mul, hx]
    norm_num
  have ho : orderOf x = 2 ^ 21 := orderOf_eq_prime_pow hn he
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at he
    exact zero_ne_one he
  have hpow : x ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hdvd : 2 ^ 21 ∣ q - 1 := ho ▸ orderOf_dvd_of_pow_eq_one hpow
  have hpos : 0 < q - 1 := by have := hq.two_le; omega
  have hle : 2 ^ 21 ≤ q - 1 := Nat.le_of_dvd hpos hdvd
  norm_num at hle hdvd
  exact ⟨by omega, hdvd⟩

theorem core25_even_data {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : 2 ^ 20 ∣ m) (hmpos : 1 ≤ m) :
    3 ∈ P ∧ (∀ p ∈ P, 3 ∣ p + 1 → 2097153 ≤ p ∧ 2097152 ∣ p - 1) ∧
    13 ∈ P ∧ 7 ∈ P ∧ (∀ p ∈ P, ¬ 13 ∣ p + 1) := by
  obtain ⟨S1, S2, S3, -, -, -, S7, S8⟩ := facts hP (hK5 2) E
  have hmod : (2 ^ m + 1) % 3 = 2 := by
    have h2 : 2 ∣ m := dvd_trans (by decide : 2 ∣ 2 ^ 20) hm
    obtain ⟨k, rfl⟩ := h2
    rw [pow_mul]
    have h4 : ∀ j : ℕ, (2 ^ 2) ^ j % 3 = 1 := by
      intro j
      induction j with
      | zero => norm_num
      | succ j hj => rw [pow_succ, Nat.mul_mod, hj]; norm_num
    have := h4 k
    omega
  obtain ⟨q, hq, hd, hq3⟩ := exists_prime_mod3 _ hmod
  have hn2 : q ≠ 2 := by
    rintro rfl
    have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have := (Nat.dvd_add_right h2m).mp hd
    omega
  have hlarge := prime_large_21 hq hn2 hm hd
  have hqP := S2 q hq hn2 (by simp; omega) hd
  have hd3 : 3 ∣ q + 1 := by omega
  have g3 := S1 3 Nat.prime_three (by decide) (by decide) q hqP hd3
  have g13 := S7 13 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have g7 := S1 7 (by norm_num) (by norm_num) (by decide) 13 g13 (by norm_num)
  refine ⟨g3, ?_, g13, g7, S8 13 (by norm_num) (by norm_num) (by decide) (by norm_num)⟩
  intro p hp hpd
  rw [S3 3 Nat.prime_three (by decide) (by decide) p hp q hqP hpd hd3]
  exact hlarge

def bw (x : ℕ) : ℚ :=
  if x = 3 then 1048577 / 786432
  else if x = 7 then 16 / 13
  else if x = 13 then 14 / 13
  else if x = 19 then 800 / 729
  else if x = 37 then 760 / 729
  else if x = 73 then 740 / 729
  else if x = 31 then 256 / 243
  else if x = 61 then 248 / 243
  else if x = 127 then 1280 / 1269
  else ((x : ℚ) + 1) / ((x : ℚ) - 1)

theorem bw_of_ne {x : ℕ} (h1 : x ≠ 3) (h2 : x ≠ 7) (h3 : x ≠ 13) (h4 : x ≠ 19) (h5 : x ≠ 37)
    (h6 : x ≠ 73) (h7 : x ≠ 31) (h8 : x ≠ 61) (h9 : x ≠ 127) :
    bw x = ((x : ℚ) + 1) / ((x : ℚ) - 1) := by
  unfold bw
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
    if_neg h9]

theorem bw_big {x : ℕ} (h : 127 < x) : bw x = ((x : ℚ) + 1) / ((x : ℚ) - 1) :=
  bw_of_ne (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem bw_special {x : ℕ} (h : bw x ≠ ((x : ℚ) + 1) / ((x : ℚ) - 1)) :
    x = 3 ∨ x = 7 ∨ x = 13 ∨ x = 19 ∨ x = 37 ∨ x = 73 ∨ x = 31 ∨ x = 61 ∨ x = 127 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcon
  exact h (bw_of_ne h1 h2 h3 h4 h5 h6 h7 h8 h9)

theorem bw_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 + 1 / (p : ℚ) ≤ bw p ∧ bw p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
  by_cases h : bw p = ((p : ℚ) + 1) / ((p : ℚ) - 1)
  · rw [h]
    exact ⟨one_add_le_B hp, le_refl _⟩
  · rcases bw_special h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [bw]

theorem step_big {c T p : ℕ} (hT : 127 < T) (hTp : T ≤ p)
    (hnum : (1 + 1 / (c : ℚ)) * (((T : ℚ) + 1) / ((T : ℚ) - 1)) ≤ bw c) :
    (1 + 1 / (c : ℚ)) * bw p ≤ bw c := by
  rw [bw_big (by omega)]
  exact (mul_le_mul_of_nonneg_left (B_anti (by omega) hTp) (by positivity)).trans hnum

theorem next19 {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 19 ≤ c') :
    p = 37 ∨ 151 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 19 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem next37 {p : ℕ} (hp : p.Prime) (hd : 37 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 37 ≤ c') :
    p = 73 ∨ 739 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 37 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem next73 {p : ℕ} (hp : p.Prime) (hd : 73 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 73 ≤ c') :
    1459 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 73 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem next31 {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 31 ≤ c') :
    p = 61 ∨ 619 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 31 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem next61 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 61 ≤ c') :
    487 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 8 := by omega
  obtain rfl : p = 61 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem next127 {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1)
    (hl : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → 127 ≤ c') :
    2539 ≤ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hd
  have hk8 : k < 20 := by omega
  obtain rfl : p = 127 * k - 1 := by omega
  interval_cases k <;>
    first
    | omega
    | (norm_num at hp; done)
    | (have := hl 3 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | (have := hl 7 (by norm_num) (by norm_num) (by simp) (by decide); omega)
    | fail

theorem bw_h4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (h3big : ∀ p ∈ P, 3 ∣ p + 1 → 2097153 ≤ p) :
    ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      bw c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * bw p ≤ bw c := by
  intro p hp c _ hd hl hne
  obtain ⟨-, -, F3, -, -, -, F7, F8⟩ := facts hP (hK5 2) E
  have hpp := (hP p hp).1
  rcases bw_special hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_big (T := 2097153) (by norm_num) (h3big p hp hd) (by norm_num [bw])
  · have h13 : 13 ∈ P := F7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
    obtain rfl : p = 13 :=
      F3 7 (by norm_num) (by norm_num) (by simp) p hp 13 h13 hd (by norm_num)
    norm_num [bw]
  · exact absurd hd (F8 13 (by norm_num) (by norm_num) (by simp) (by norm_num) p hp)
  · rcases next19 hpp hd hl with rfl | h
    · norm_num [bw]
    · exact step_big (T := 151) (by norm_num) h (by norm_num [bw])
  · rcases next37 hpp hd hl with rfl | h
    · norm_num [bw]
    · exact step_big (T := 739) (by norm_num) h (by norm_num [bw])
  · exact step_big (T := 1459) (by norm_num) (next73 hpp hd hl) (by norm_num [bw])
  · rcases next31 hpp hd hl with rfl | h
    · norm_num [bw]
    · exact step_big (T := 619) (by norm_num) h (by norm_num [bw])
  · exact step_big (T := 487) (by norm_num) (next61 hpp hd hl) (by norm_num [bw])
  · exact step_big (T := 2539) (by norm_num) (next127 hpp hd hl) (by norm_num [bw])

theorem ledger5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {T : Finset ℕ} (hT : T ⊆ P) : ¬ 5 ^ 3 ∣ ∏ p ∈ T, (p + 1) := by
  intro h
  have h1 : 5 ^ 3 ∣ ∏ p ∈ P, (p + 1) :=
    h.trans (Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hT)
  have h2 : 5 ^ 3 ∣ 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by
    rw [← E]
    exact Dvd.dvd.mul_left h1 _
  have h3 : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
    have e : 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p = 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
    rw [← e]
    exact h2
  have h4 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h4 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  · obtain ⟨p, hp, h5p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_five.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five (hP p hp).1).mp h5p
    exact h5 (this ▸ hp)

theorem five_leaf_j1 {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k * 5) :
    q = 19 ∨ q = 79 ∨ 1279 ≤ q := by
  by_cases h8 : k < 8
  · obtain rfl : q = 2 ^ k * 5 - 1 := by omega
    interval_cases k <;> first | (norm_num at hq; done) | norm_num
  · have h2 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h2
    exact Or.inr (Or.inr (by omega))

theorem five_leaf_bw_le {q : ℕ} (hq : q.Prime) (h5 : 5 ∣ q + 1)
    (hleaf : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5)
    (h125 : ¬ 5 ^ 3 ∣ q + 1) : bw q ≤ 800 / 729 := by
  obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := q + 1) (z := 5) (by omega) hleaf
  have hj3 : j < 3 := by
    by_contra hj
    exact h125 (hkj ▸ Dvd.dvd.mul_left (pow_dvd_pow 5 (by omega : 3 ≤ j)) _)
  interval_cases j
  · rw [pow_zero, mul_one] at hkj
    rw [hkj] at h5
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h5)
    omega
  · rw [pow_one] at hkj
    rcases five_leaf_j1 hq hkj with rfl | rfl | h1279
    · norm_num [bw]
    · exact (bw_bounds hq.two_le).2.trans (by norm_num)
    · exact (bw_bounds hq.two_le).2.trans ((B_anti (by norm_num) h1279).trans (by norm_num))
  · by_cases hk : k < 3
    · obtain rfl : q = 2 ^ k * 5 ^ 2 - 1 := by omega
      interval_cases k <;> norm_num at hq
    · have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h8
      have h199 : 199 ≤ q := by omega
      exact (bw_bounds hq.two_le).2.trans ((B_anti (by norm_num) h199).trans (by norm_num))

theorem mem_19_and_79 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm43 : 43 ≤ m) (h3big : ∀ p ∈ P, 3 ∣ p + 1 → 2097153 ≤ p) : 19 ∈ P ∧ 79 ∈ P := by
  classical
  by_contra hnot
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP (hK5 2) (by norm_num) E bw
    (fun p hp => bw_bounds (hP p hp).1.two_le) (bw_h4 hP E h3big)
  have hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5 := fun q hq c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf q hq c hc h2 hd)
  have hpos : ∀ q ∈ L, 0 < bw q := fun q hq =>
    lt_of_lt_of_le (by positivity) (bw_bounds (hP q (hLP hq)).1.two_le).1
  let L5 := L.filter (fun q => 5 ∣ q + 1)
  have hL5sub : L5 ⊆ P := (Finset.filter_subset _ _).trans hLP
  have hL5card : L5.card ≤ 2 := by
    by_contra h3
    have hdiv : 5 ^ L5.card ∣ ∏ q ∈ L5, (q + 1) := by
      rw [← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
    exact ledger5 hP h5 E hL5sub ((pow_dvd_pow 5 (by omega : 3 ≤ L5.card)).trans hdiv)
  have h5part : ∏ q ∈ L5, bw q ≤ (800 / 729) * (1280 / 1278) := by
    have hcases : L5.card = 0 ∨ L5.card = 1 ∨ L5.card = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]
      norm_num
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
      have hqmem : q ∈ L5 := hq ▸ Finset.mem_singleton_self q
      obtain ⟨hqL, hq5⟩ := Finset.mem_filter.mp hqmem
      have h125 : ¬ 5 ^ 3 ∣ q + 1 := fun hd => by
        apply ledger5 hP h5 E (T := {q}) (Finset.singleton_subset_iff.mpr (hLP hqL))
        simpa using hd
      rw [hq, Finset.prod_singleton]
      exact (five_leaf_bw_le (hP q (hLP hqL)).1 hq5 (hleaf q hqL) h125).trans (by norm_num)
    · obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp h2
      have hsub : ∀ {x y : ℕ}, x < y → L5 = {x, y} →
          ∏ q ∈ L5, bw q ≤ (800 / 729) * (1280 / 1278) := by
        intro x y hxy hxyeq
        have hxmem : x ∈ L5 := hxyeq ▸ Finset.mem_insert_self x {y}
        have hymem : y ∈ L5 := hxyeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
        obtain ⟨hxL, hx5⟩ := Finset.mem_filter.mp hxmem
        obtain ⟨hyL, hy5⟩ := Finset.mem_filter.mp hymem
        have hxp := (hP x (hLP hxL)).1
        have hyp := (hP y (hLP hyL)).1
        have h25x : ¬ 5 ^ 2 ∣ x + 1 := fun hd => by
          apply ledger5 hP h5 E hL5sub
          rw [hxyeq, Finset.prod_pair hxy.ne, show (5 : ℕ) ^ 3 = 5 ^ 2 * 5 by norm_num]
          exact mul_dvd_mul hd hy5
        have h25y : ¬ 5 ^ 2 ∣ y + 1 := fun hd => by
          apply ledger5 hP h5 E hL5sub
          rw [hxyeq, Finset.prod_pair hxy.ne, show (5 : ℕ) ^ 3 = 5 * 5 ^ 2 by norm_num]
          exact mul_dvd_mul hx5 hd
        obtain ⟨kx, jx, hkx⟩ := two_pow_mul_pow_of_odd_primes_eq (M := x + 1) (z := 5) (by omega)
          (hleaf x hxL)
        obtain ⟨ky, jy, hky⟩ := two_pow_mul_pow_of_odd_primes_eq (M := y + 1) (z := 5) (by omega)
          (hleaf y hyL)
        have hjx1 : jx = 1 := by
          rcases Nat.lt_or_ge jx 2 with hj | hj
          · interval_cases jx
            · rw [hkx, pow_zero, mul_one] at hx5
              have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
                (Nat.prime_five.dvd_of_dvd_pow hx5)
              omega
            · rfl
          · exact absurd (hkx ▸ Dvd.dvd.mul_left (pow_dvd_pow 5 hj) _) h25x
        have hjy1 : jy = 1 := by
          rcases Nat.lt_or_ge jy 2 with hj | hj
          · interval_cases jy
            · rw [hky, pow_zero, mul_one] at hy5
              have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
                (Nat.prime_five.dvd_of_dvd_pow hy5)
              omega
            · rfl
          · exact absurd (hky ▸ Dvd.dvd.mul_left (pow_dvd_pow 5 hj) _) h25y
        rw [hjx1, pow_one] at hkx
        rw [hjy1, pow_one] at hky
        have hx_cases := five_leaf_j1 hxp hkx
        have hy_cases := five_leaf_j1 hyp hky
        have hy1279 : 1279 ≤ y := by
          rcases hy_cases with rfl | rfl | hybig
          · rcases hx_cases with rfl | rfl | hxbig <;> omega
          · rcases hx_cases with rfl | rfl | hxbig
            · exact absurd ⟨hLP hxL, hLP hyL⟩ hnot
            · omega
            · omega
          · exact hybig
        have hbx : bw x ≤ 800 / 729 := five_leaf_bw_le hxp hx5 (hleaf x hxL)
          (fun hd => h25x ((pow_dvd_pow 5 (by norm_num : 2 ≤ 3)).trans hd))
        have hby : bw y ≤ 1280 / 1278 :=
          (bw_bounds hyp.two_le).2.trans ((B_anti (by norm_num) hy1279).trans (by norm_num))
        rw [hxyeq, Finset.prod_pair hxy.ne]
        exact mul_le_mul hbx hby (hpos y hyL).le (by norm_num)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact hsub hlt hpair
      · exact hsub hgt (by rw [hpair, Finset.pair_comm])
  have hMpart : ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), bw q ≤
      (bw 3 * bw 7 * bw 31 * bw 127) * (2048 / 2047) := by
    apply mersenne_bound
    · intro q hq
      exact (hP q (hLP (Finset.mem_filter.mp hq).1)).1
    · intro q hq
      obtain ⟨hqL, hq5⟩ := Finset.mem_filter.mp hq
      exact two_pow_of_no_odd_prime (fun c hc h2 hd => hq5 (hleaf q hqL c hc h2 hd ▸ hd))
    · intro q hq
      have hqL := (Finset.mem_filter.mp hq).1
      exact ⟨hpos q hqL, (bw_bounds (hP q (hLP hqL)).1.two_le).2⟩
    · norm_num [bw]
  have hM0 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), bw q :=
    Finset.prod_nonneg fun q hq => (hpos q (Finset.mem_filter.mp hq).1).le
  have hX : (∏ q ∈ L5, bw q) * (∏ q ∈ L.filter (fun q => ¬ 5 ∣ q + 1), bw q) ≤
      ((800 / 729) * (1280 / 1278)) * ((bw 3 * bw 7 * bw 31 * bw 127) * (2048 / 2047)) :=
    mul_le_mul h5part hMpart hM0 (by norm_num)
  rw [Finset.prod_filter_mul_prod_filter_not L (fun q => 5 ∣ q + 1) bw] at hX
  have hX0 : (0 : ℚ) ≤ ∏ q ∈ L, bw q := Finset.prod_nonneg fun q hq => (hpos q hq).le
  have hpow : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 43 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm43)
  have hKK : (((1 + 5 ^ 2 : ℕ) : ℚ) / ((5 ^ 2 : ℕ) : ℚ)) = 26 / 25 := by norm_num
  rw [hKK] at hmain
  have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ q ∈ L, bw q ≤
      (1 + 1 / 2 ^ 43) * (26 / 25) *
        (((800 / 729) * (1280 / 1278)) * ((bw 3 * bw 7 * bw 31 * bw 127) * (2048 / 2047))) := by
    apply mul_le_mul _ hX hX0 (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  have h2 : (1 + 1 / (2 : ℚ) ^ 43) * (26 / 25) *
      (((800 / 729) * (1280 / 1278)) * ((bw 3 * bw 7 * bw 31 * bw 127) * (2048 / 2047))) < 2 := by
    norm_num [bw]
  linarith

-- =============================================================================
-- Part 2: Verified finite branch-and-bound tree (with 19, 79 exhausting 5^2)
-- =============================================================================

def subProds : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProds t ++ (subProds t).map (fun d => c * d)

def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 3 && c != 13 && X.all (fun x => (x + 1) % c != 0))

def has3 (X : List ℕ) : Bool :=
  X.any (fun x => x != 3 && (x + 1) % 3 == 0)

def scanOpens (X : List ℕ) (N : ℕ) : List ℕ :=
  if has3 X || decide (2 * N ≤ 2097153) then opens X else 3 :: opens X

def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

def candOk (X F : List ℕ) (N' v : ℕ) : Bool :=
  decide (N' ≤ v) || decide (v ∈ X) ||
    (v % 3 == 2 && (has3 X || decide (v < 2097153) || (v - 1) % 2097152 != 0)) ||
    F.any (fun f => decide (1 < f) && decide (f < v) && v % f == 0)

def winOk (X F : List ℕ) (N N' : ℕ) : Bool :=
  decide (N' < 2 * N) &&
    (subProds (scanOpens X N)).all (fun d =>
      decide (N < d) || candOk X F N' (2 ^ (Nat.log2 (N / d) + 1) * d - 1))

def upOk (X : List ℕ) : Bool := decide (2 * 25 * X.prod ≤ 26 * succProd X)

def jumpOk (X : List ℕ) (N' : ℕ) : Bool :=
  decide (2 ≤ N') && decide (2 * 25 * X.prod * (N' - 1) ≤ 26 * succProd X * N')

def lowOk (X : List ℕ) (N : ℕ) : Bool :=
  let k := (opens X).length
  let Q := max N 2097153
  let qnum := if has3 X then 1 else Q + 1
  let qden := if has3 X then 1 else Q - 1
  decide (5 ≤ N) &&
    decide ((2 ^ 64 + 1) * 26 * succProd X * qnum * (N + 1) ^ (k + 1) <
      2 * 2 ^ 64 * 25 * X.prod * qden * (N - 1) ^ k * (N - 3))

structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 26 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  hc13 : ∀ p ∈ P, ¬ 13 ∣ p + 1
  h3big : ∀ p ∈ P, 3 ∣ p + 1 → 2097153 ≤ p ∧ 2097152 ∣ p - 1
  hno5 : ∀ p ∈ P, p ≠ 19 → p ≠ 79 → ¬ 5 ∣ p + 1
  hm : 64 ≤ m

def St (P : Finset ℕ) (X : List ℕ) (N : ℕ) : Prop :=
  (∀ x ∈ X, x ∈ P) ∧ X.Nodup ∧ 19 ∈ X ∧ 79 ∈ X ∧ ∀ p ∈ P, p < N → p ∈ X

theorem mem_subProds : ∀ (l : List ℕ), (∀ c ∈ l, c.Prime) → ∀ d : ℕ, d ∣ l.prod → d ∈ subProds l
  | [], _, d, hd => by
    rw [List.prod_nil, Nat.dvd_one] at hd
    rw [hd]
    exact List.mem_singleton.mpr rfl
  | c :: t, hl, d, hd => by
    have hc : c.Prime := hl c List.mem_cons_self
    have ht : ∀ x ∈ t, x.Prime := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.prod_cons] at hd
    by_cases hcd : c ∣ d
    · obtain ⟨e, rfl⟩ := hcd
      have he : e ∣ t.prod := Nat.dvd_of_mul_dvd_mul_left hc.pos hd
      exact List.mem_append_right _ (List.mem_map.mpr ⟨e, mem_subProds t ht e he, rfl⟩)
    · have hcop : Nat.Coprime d c := (hc.coprime_iff_not_dvd.mpr hcd).symm
      have hdt : d ∣ t.prod := hcop.dvd_of_dvd_mul_left hd
      exact List.mem_append_left _ (mem_subProds t ht d hdt)

theorem dvd_of_primes {d D : ℕ} (hsq : ∀ c : ℕ, c.Prime → ¬ c * c ∣ d)
    (hdiv : ∀ c : ℕ, c.Prime → c ∣ d → c ∣ D) : d ∣ D := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hd0 : d ≠ 0 := fun h => hsq 2 Nat.prime_two (h ▸ dvd_zero _)
    by_cases h1 : d = 1
    · rw [h1]; exact one_dvd D
    · have hp : d.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨e, he⟩ := Nat.minFac_dvd d
      set p := d.minFac
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [mul_zero] at he
        exact hd0 he
      have hlt : e < d := by
        have := hp.two_le
        have : 0 < e := Nat.pos_of_ne_zero he0
        nlinarith
      have hed : e ∣ d := ⟨p, by rw [he, mul_comm]⟩
      have hpe : ¬ p ∣ e := fun h => by
        obtain ⟨f, rfl⟩ := h
        exact hsq p hp ⟨f, by rw [he]; ring⟩
      have heD : e ∣ D := ih e hlt
        (fun c hc hcc => hsq c hc (hcc.trans hed))
        (fun c hc hce => hdiv c hc (hce.trans hed))
      have hpD : p ∣ D := hdiv p hp ⟨e, he⟩
      rw [he]
      exact (hp.coprime_iff_not_dvd.mpr hpe).mul_dvd_of_dvd_of_dvd hpD heD

theorem mem_opens {X : List ℕ} {c : ℕ} (hc : c ∈ X) (h3 : c ≠ 3) (h13 : c ≠ 13)
    (hclosed : ∀ x ∈ X, ¬ c ∣ x + 1) : c ∈ opens X := by
  unfold opens
  rw [List.mem_filter]
  refine ⟨hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true]
  exact ⟨⟨h3, h13⟩, fun x hx hmod => hclosed x hx (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem succProd_eq {X : List ℕ} (hXn : X.Nodup) :
    ∏ p ∈ X.toFinset, (p + 1) = succProd X := by
  rw [List.prod_toFinset _ hXn]
  rfl

theorem prod_eq {X : List ℕ} (hXn : X.Nodup) :
    ∏ p ∈ X.toFinset, p = X.prod := by
  rw [List.prod_toFinset _ hXn]
  simp

theorem pow_window {N w i t : ℕ} (hw : 0 < w) (hwN : w ≤ N) (ht : t = 2 ^ i * w)
    (h1 : N < t) (h2 : t < 2 * N) : 2 ^ (Nat.log2 (N / w) + 1) * w = t := by
  have hq0 : N / w ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos hwN hw)
  have hk1 : 2 ^ Nat.log2 (N / w) * w ≤ N :=
    (Nat.mul_le_mul_right _ (Nat.log2_self_le hq0)).trans (Nat.div_mul_le_self _ _)
  have hk2 : N < 2 ^ (Nat.log2 (N / w) + 1) * w := (Nat.div_lt_iff_lt_mul hw).mp Nat.lt_log2_self
  have hgt : Nat.log2 (N / w) < i := by
    by_contra hle
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hle))
    omega
  have hlt : i < Nat.log2 (N / w) + 2 := by
    by_contra hge
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge))
    have e : 2 ^ (Nat.log2 (N / w) + 2) * w = 2 * (2 ^ (Nat.log2 (N / w) + 1) * w) := by ring
    omega
  have hi : i = Nat.log2 (N / w) + 1 := by omega
  rw [ht, hi]

theorem not_dvd3_of_has3 {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ}
    (hXP : ∀ x ∈ X, x ∈ P) (h3 : has3 X = true) {p : ℕ} (hp : p ∈ P) (hpX : p ∉ X) :
    ¬ 3 ∣ p + 1 := by
  unfold has3 at h3
  rw [List.any_eq_true] at h3
  obtain ⟨x, hxX, hx⟩ := h3
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hx
  intro hd3
  have hx3 : 3 ∣ x + 1 := Nat.dvd_of_mod_eq_zero hx.2
  have eq := C.s3 3 Nat.prime_three (by decide) (by decide) p hp x (hXP x hxX) hd3 hx3
  exact hpX (eq ▸ hxX)

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X F : List ℕ} {N N' : ℕ}
    (h : St P X N) (hchk : winOk X F N N' = true) : St P X N' := by
  obtain ⟨hXP, hXn, h19, h79, hcl⟩ := h
  refine ⟨hXP, hXn, h19, h79, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact hcl p hp hpN
  by_contra hpX
  simp only [winOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨hN2, hall⟩ := hchk
  have hpp := (C.hP p hp).1
  have hp2 := (C.hP p hp).2
  have hpodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  have hp5 : ¬ 5 ∣ p + 1 := C.hno5 p hp (fun e => hpX (e ▸ h19)) (fun e => hpX (e ▸ h79))
  obtain ⟨i, d, hd2, hiu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := p + 1) (by omega) 2 (by norm_num)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hiu
    omega
  have hdvd : d ∣ p + 1 := ⟨2 ^ i, by rw [hiu]; ring⟩
  have hprime : ∀ c : ℕ, c.Prime → c ∣ d → c ≠ 2 ∧ c ≠ 5 := fun c _ hcd =>
    ⟨fun h2 => hd2 (h2 ▸ hcd), fun h5 => hp5 ((h5 ▸ hcd).trans hdvd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ scanOpens X N := fun c hc hcd => by
    obtain ⟨hc2, hc5⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hc5 p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    by_cases hc3 : c = 3
    · subst hc3
      have hno3 : has3 X = false := by
        cases h : has3 X with
        | false => rfl
        | true => exact absurd hcp (not_dvd3_of_has3 C hXP h hp hpX)
      have hbig : 2097153 ≤ p := (C.h3big p hp hcp).1
      unfold scanOpens
      rw [hno3]
      have hlt : ¬ (2 * N ≤ 2097153) := by omega
      simp [hlt]
    · have hco : c ∈ opens X := mem_opens hcX hc3 (fun e => C.hc13 p hp (e ▸ hcp)) fun x hx hcx =>
        hpX ((C.s3 c hc hc2 hc5 p hp x (hXP x hx) hcp hcx) ▸ hx)
      unfold scanOpens
      split_ifs
      · exact hco
      · exact List.mem_cons_of_mem _ hco
  have hscanP : ∀ c ∈ scanOpens X N, c.Prime := fun c hc => by
    unfold scanOpens at hc
    split_ifs at hc
    · exact (C.hP c (hXP c (List.mem_filter.mp hc).1)).1
    · rcases List.mem_cons.mp hc with rfl | hc'
      · exact Nat.prime_three
      · exact (C.hP c (hXP c (List.mem_filter.mp hc').1)).1
  have hdD : d ∣ (scanOpens X N).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hc5⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hc5 p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hmem : d ∈ subProds (scanOpens X N) := mem_subProds _ hscanP d hdD
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hd2 ⟨(p + 1) / 2, by omega⟩
  have hdN : d ≤ N := by
    by_contra hNd
    have h2 : 2 ^ 1 * d ≤ 2 ^ i * d :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi1)
    omega
  have h1 := hall d hmem
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (of_decide_eq_true h1) (not_lt.mpr hdN)
  · have hwin := pow_window (Nat.pos_of_ne_zero hd0) hdN hiu (by omega) (by omega)
    have hv : 2 ^ (Nat.log2 (N / d) + 1) * d - 1 = p := by rw [hwin]; omega
    rw [hv] at h1
    simp only [candOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, bne_iff_ne, List.any_eq_true] at h1
    rcases h1 with ((h1 | h1) | ⟨hmod3, h3c⟩) | ⟨f, _, ⟨hf1, hfp⟩, hfd⟩
    · omega
    · exact hpX h1
    · have hd3 : 3 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
      have ⟨hbig, hdiv21⟩ := C.h3big p hp hd3
      rcases h3c with (hh3 | hlt) | hmod21
      · exact not_dvd3_of_has3 C hXP hh3 hp hpX hd3
      · omega
      · exact hmod21 (Nat.mod_eq_zero_of_dvd hdiv21)
    · have hdvd_f : f ∣ p := Nat.dvd_of_mod_eq_zero hfd
      rcases hpp.eq_one_or_self_of_dvd f hdvd_f with rfl | rfl <;> omega

theorem up_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N : ℕ}
    (h : St P X N) (hchk : upOk X = true) : False := by
  obtain ⟨hXP, hXn, -, -, -⟩ := h
  simp only [upOk, decide_eq_true_eq] at hchk
  have hF : X.toFinset ⊆ P := fun x hx => hXP x (List.mem_toFinset.mp hx)
  have h1 := Finset.prod_sdiff hF (f := fun p => p + 1)
  have h2 := Finset.prod_sdiff hF (f := fun p => p)
  rw [succProd_eq hXn] at h1
  rw [prod_eq hXn] at h2
  have hQ : ∏ p ∈ P \ X.toFinset, p ≤ ∏ p ∈ P \ X.toFinset, (p + 1) :=
    Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.le_succ i)
  have hpos : 0 < ∏ p ∈ P \ X.toFinset, (p + 1) := Finset.prod_pos fun p _ => Nat.succ_pos p
  have hSpos : 0 < succProd X := by
    unfold succProd
    exact List.prod_pos (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
      exact Nat.succ_pos x)
  have E := C.E
  rw [← h1, ← h2] at E
  have key : 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod) <
      (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) :=
    calc 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod)
        = 2 ^ m * ((∏ p ∈ P \ X.toFinset, p) * (2 * 25 * X.prod)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hchk)
      _ < (2 ^ m + 1) * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem jump_step {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N N' : ℕ}
    (h : St P X N) (hchk : jumpOk X N' = true) : St P X N' := by
  obtain ⟨hXP, hXn, h19, h79, -⟩ := h
  simp only [jumpOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hN2, hineq⟩ := hchk
  refine ⟨hXP, hXn, h19, h79, fun p hp hpN' => ?_⟩
  by_contra hpX
  have hF : insert p X.toFinset ⊆ P := Finset.insert_subset hp (fun x hx => hXP x (List.mem_toFinset.mp hx))
  have hpF : p ∉ X.toFinset := fun h => hpX (List.mem_toFinset.mp h)
  have h1 := Finset.prod_sdiff hF (f := fun q => q + 1)
  have h2 := Finset.prod_sdiff hF (f := fun q => q)
  rw [Finset.prod_insert hpF, succProd_eq hXn] at h1
  rw [Finset.prod_insert hpF, prod_eq hXn] at h2
  have hQ : ∏ q ∈ P \ insert p X.toFinset, q ≤ ∏ q ∈ P \ insert p X.toFinset, (q + 1) :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.le_succ _)
  have hpos : 0 < ∏ q ∈ P \ insert p X.toFinset, (q + 1) :=
    Finset.prod_pos fun _ _ => Nat.succ_pos _
  have hSpos : 0 < succProd X := by
    unfold succProd
    exact List.prod_pos fun a ha => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact Nat.succ_pos x
  have hpp : 1 ≤ p := (C.hP p hp).1.pos
  have hstep : 2 * 25 * (p * X.prod) ≤ 26 * ((p + 1) * succProd X) := by
    have hmul : N' * p ≤ (p + 1) * (N' - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, N' = k + 1 := ⟨N' - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : p ≤ k := by omega
      nlinarith
    have h1' : (2 * 25 * X.prod * (N' - 1)) * p ≤ (26 * succProd X * N') * p :=
      Nat.mul_le_mul_right p hineq
    have h2' : (26 * succProd X * N') * p ≤ (26 * succProd X) * ((p + 1) * (N' - 1)) := by
      calc (26 * succProd X * N') * p = (26 * succProd X) * (N' * p) := by ring
        _ ≤ (26 * succProd X) * ((p + 1) * (N' - 1)) := Nat.mul_le_mul_left _ hmul
    have h3' : (2 * 25 * (p * X.prod)) * (N' - 1) ≤ (26 * ((p + 1) * succProd X)) * (N' - 1) := by
      linarith
    exact Nat.le_of_mul_le_mul_right h3' (by omega : 0 < N' - 1)
  have E := C.E
  rw [← h1, ← h2] at E
  have key : 2 ^ (m + 1) * 25 * ((∏ q ∈ P \ insert p X.toFinset, q) * (p * X.prod)) <
      (2 ^ m + 1) * 26 * ((∏ q ∈ P \ insert p X.toFinset, (q + 1)) * ((p + 1) * succProd X)) :=
    calc 2 ^ (m + 1) * 25 * ((∏ q ∈ P \ insert p X.toFinset, q) * (p * X.prod))
        = 2 ^ m * ((∏ q ∈ P \ insert p X.toFinset, q) * (2 * 25 * (p * X.prod))) := by ring
      _ ≤ 2 ^ m * ((∏ q ∈ P \ insert p X.toFinset, (q + 1)) * (26 * ((p + 1) * succProd X))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hstep)
      _ < (2 ^ m + 1) * ((∏ q ∈ P \ insert p X.toFinset, (q + 1)) * (26 * ((p + 1) * succProd X))) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _)
            (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.succ_pos p) hSpos)))
      _ = (2 ^ m + 1) * 26 * ((∏ q ∈ P \ insert p X.toFinset, (q + 1)) * ((p + 1) * succProd X)) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 26 * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, (p : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) C.E
    push_cast at h
    exact h
  have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
    field_simp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [e]
  field_simp
  rw [pow_succ] at hcast
  linarith

theorem weight_list : ∀ X : List ℕ, (∀ x ∈ X, 0 < x) →
    (X.map (fun x : ℕ => 1 + 1 / (x : ℚ))).prod = (succProd X : ℚ) / (X.prod : ℚ)
  | [], _ => by simp [succProd]
  | x :: t, h => by
    have hx : (0 : ℚ) < x := by exact_mod_cast h x List.mem_cons_self
    have ht : (0 : ℚ) < (t.prod : ℚ) := by
      exact_mod_cast List.prod_pos (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ih := weight_list t (fun a ha => h a (List.mem_cons_of_mem _ ha))
    unfold succProd at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.prod_cons]
    push_cast
    field_simp

theorem final_ineq {S Pi N E qnum qden : ℕ} (hN : 5 ≤ N) (hPi : 0 < Pi) (hqden : 0 < qden)
    (h : (2 ^ 64 + 1) * 26 * S * qnum * (N + 1) ^ (E + 1) <
      2 * 2 ^ 64 * 25 * Pi * qden * (N - 1) ^ E * (N - 3)) :
    (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) * ((qnum : ℚ) / qden) *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ E * (((N : ℚ) + 1) / ((N : ℚ) - 3)) < 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e3 : k + 3 - 3 = k := by omega
  rw [e1, e3] at h
  have hq := (Nat.cast_lt (α := ℚ)).mpr h
  push_cast at hq
  have hk : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  have hPiq : (0 : ℚ) < Pi := by exact_mod_cast hPi
  have hqdq : (0 : ℚ) < qden := by exact_mod_cast hqden
  have hk2 : (0 : ℚ) < (k : ℚ) + 2 := by linarith
  have e : (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) * ((qnum : ℚ) / qden) *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 1)) ^ E *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 3)) =
      (((2 : ℚ) ^ 64 + 1) * 26 * S * qnum * ((k : ℚ) + 3 + 1) ^ (E + 1)) /
        (2 ^ 64 * 25 * Pi * qden * ((k : ℚ) + 2) ^ E * k) := by
    push_cast
    have e4 : (k : ℚ) + 3 - 1 = k + 2 := by ring
    have e5 : (k : ℚ) + 3 - 3 = k := by ring
    rw [e4, e5, div_pow]
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  linarith

theorem low_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X : List ℕ} {N : ℕ}
    (h : St P X N) (hchk : lowOk X N = true) : False := by
  obtain ⟨hXP, hXn, h19, h79, hcl⟩ := h
  simp only [lowOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hN5, hnum⟩ := hchk
  classical
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hnz : ∀ {c : ℕ}, c ∉ ({5} : Finset ℕ) → c ≠ 5 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 5 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hnz hcN, C.s1 _ hc hc2 (hnz hcN) p hp (hg p).1,
        two_mul_le hc hc2 (C.hP p hp).1 (C.hP p hp).2 (hg p).1⟩
  have hg1 : ∀ q ∈ P.filter (fun p => p ∉ X), g q ∈ P.filter (fun p => p ∉ X) → g q ≠ 1 :=
    fun q _ hgq h1 => by
      have := (C.hP _ (hQP _ hgq)).1
      rw [h1] at this
      exact Nat.not_prime_one this
  have hpath := path_bound g (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (P.filter (fun p => p ∉ X)).card (P.filter (fun p => p ∉ X)) rfl
    (fun q hq => (C.hP q (hQP q hq)).1.pos)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      have := hc.two_le
      omega)
    (fun q hq q' hq' hgq he => by
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact C.s3 _ hc hc2 hcz q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
    (fun q hq => one_add_le_B (C.hP q (hQP q hq)).1.two_le)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact B_step hc.two_le h2)
  generalize hRdef : (P.filter (fun p => p ∉ X)).filter (fun q => g q ∉ P.filter (fun p => p ∉ X)) = R at hpath
  have hRQ : ∀ q ∈ R, q ∈ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).1
  have hRg : ∀ q ∈ R, g q ∉ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).2
  have hRP : ∀ q ∈ R, q ∈ P := fun q hq => hQP q (hRQ q hq)
  have hRX : ∀ q ∈ R, q ∉ X := fun q hq => hQX q (hRQ q hq)
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (C.hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  let Q := max N 2097153
  let qnum : ℕ := if has3 X then 1 else Q + 1
  let qden : ℕ := if has3 X then 1 else Q - 1
  have hqden_pos : 0 < qden := by
    dsimp [qden, Q]
    split_ifs <;> omega
  have hq1 : (1 : ℚ) ≤ (qnum : ℚ) / (qden : ℚ) := by
    dsimp [qnum, qden, Q]
    split_ifs
    · norm_num
    · have hQ2 : (2 : ℚ) ≤ (max N 2097153 : ℕ) := by exact_mod_cast (by omega : 2 ≤ max N 2097153)
      have he : ((max N 2097153 - 1 : ℕ) : ℚ) = (max N 2097153 : ℕ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ max N 2097153)]; norm_num
      rw [Nat.cast_add, Nat.cast_one, he, le_div_iff₀ (by linarith)]
      linarith
  -- Part A: g q = 3
  have hprod3 : ∏ q ∈ R.filter (fun q => g q = 3), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (qnum : ℚ) / (qden : ℚ) := by
    rcases Finset.eq_empty_or_nonempty (R.filter (fun q => g q = 3)) with hempty | ⟨q0, hq0⟩
    · rw [hempty, Finset.prod_empty]
      exact hq1
    · obtain ⟨hq0R, hg0⟩ := Finset.mem_filter.mp hq0
      have hd3 : 3 ∣ q0 + 1 := hg0 ▸ (hg q0).1
      have hsing : R.filter (fun q => g q = 3) = {q0} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hq0, fun q hq => by
          obtain ⟨hqR, hgq⟩ := Finset.mem_filter.mp hq
          exact C.s3 3 Nat.prime_three (by decide) (by decide) q (hRP q hqR) q0 (hRP q0 hq0R)
            (hgq ▸ (hg q).1) hd3⟩
      rw [hsing, Finset.prod_singleton]
      have hno3 : has3 X = false := by
        cases h3 : has3 X with
        | false => rfl
        | true => exact absurd hd3 (not_dvd3_of_has3 C hXP h3 (hRP q0 hq0R) (hRX q0 hq0R))
      have hq0Q : Q ≤ q0 := max_le (hQN q0 (hRQ q0 hq0R)) (C.h3big q0 (hRP q0 hq0R) hd3).1
      have hB := B_anti (by omega : 2 ≤ Q) hq0Q
      dsimp [qnum, qden]
      rw [hno3]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have he : ((Q - 1 : ℕ) : ℚ) = (Q : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ Q)]; norm_num
      rw [Nat.cast_add, Nat.cast_one, he]
      exact hB
  -- Part B: g q ≠ 3 ∧ g q ≠ 1 (maps injectively into opens X)
  let Rrest := R.filter (fun q => ¬ g q = 3)
  have hA : ∀ q ∈ Rrest, g q ≠ 1 → g q ∈ opens X := fun q hq h1 => by
    obtain ⟨hqR, hne3⟩ := Finset.mem_filter.mp hq
    have hqP := hRP q hqR
    obtain ⟨hc, hc2, hcz, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hqR (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    refine mem_opens hcX hne3 (fun e => C.hc13 q hqP (e ▸ (hg q).1)) fun x hx hcx => ?_
    exact hRX q hqR ((C.s3 _ hc hc2 hcz q hqP x (hXP x hx) (hg q).1 hcx) ▸ hx)
  have hcardA : (Rrest.filter (fun q => g q ≠ 1)).card ≤ (opens X).length := by
    refine (Finset.card_le_card_of_injOn g (t := (opens X).toFinset) ?_ ?_).trans (List.toFinset_card_le _)
    · intro q hq
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (hA q hqR h1))
    · intro q hq q' hq' he
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hRP q (Finset.mem_filter.mp hqR).1) h1
      exact C.s3 _ hc hc2 hcz q (hRP q (Finset.mem_filter.mp hqR).1)
        q' (hRP q' (Finset.mem_filter.mp hqR').1) (hg q).1 (he ▸ (hg q').1)
  have hprodA : ∏ q ∈ Rrest.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (opens X).length := by
    refine le_trans ?_ (pow_le_pow_right₀ hBN1 hcardA)
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  -- Part C: g q = 1 (pure Mersenne primes since 5 is exhausted!)
  have hpow : ∀ q ∈ Rrest.filter (fun q => ¬ g q ≠ 1), ∃ k, q + 1 = 2 ^ k := fun q hq => by
    obtain ⟨hq1, hg1'⟩ := Finset.mem_filter.mp hq
    have hqR := (Finset.mem_filter.mp hq1).1
    have hqno5 : ¬ 5 ∣ q + 1 := C.hno5 q (hRP q hqR) (fun e => hRX q hqR (e ▸ h19))
      (fun e => hRX q hqR (e ▸ h79))
    refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
    have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
    rw [Finset.mem_singleton] at this
    exact hqno5 (this ▸ hcd)
  have hprodC : ∏ q ∈ Rrest.filter (fun q => ¬ g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    refine tail_bound _ _ N rfl (by omega)
      (fun q hq => hQN q (hRQ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1))
      (fun q hq q' hq' hlt => ?_)
    obtain ⟨k, hk⟩ := hpow q hq
    obtain ⟨k', hk'⟩ := hpow q' hq'
    have hkk : k < k' := by
      by_contra hge
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge)
      omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt hkk)
    rw [pow_succ] at this
    omega
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q = 3)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not Rrest (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hB0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := le_trans zero_le_one hBN1
  have hT0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    have : (5 : ℚ) ≤ N := by exact_mod_cast hN5
    exact div_nonneg (by linarith) (by linarith)
  have hRrest : ∏ q ∈ Rrest, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (opens X).length * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    rw [← hsplit2]
    exact mul_le_mul hprodA hprodC
      (Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (pow_nonneg hB0 _)
  have hRbound : ∏ q ∈ R, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      ((qnum : ℚ) / (qden : ℚ)) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (opens X).length *
        (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    rw [← hsplit1, mul_assoc]
    exact mul_le_mul hprod3 hRrest
      (Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp hq).1)
      (le_trans zero_le_one hq1)
  have hXpos : ∀ x ∈ X, 0 < x := fun x hx => (C.hP x (hXP x hx)).1.pos
  have hfil : P.filter (fun p => p ∈ X) = X.toFinset := by
    ext x
    rw [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hXP x h, h⟩⟩
  have hsplitP := Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ X) (fun p => 1 + 1 / (p : ℚ))
  rw [hfil, List.prod_toFinset _ hXn, weight_list X hXpos] at hsplitP
  have hpow64 : (1 : ℚ) + 1 / (2 : ℚ) ^ m ≤ 1 + 1 / (2 : ℚ) ^ 64 := by
    have : (2 : ℚ) ^ 64 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) C.hm
    linarith [one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ 64) this]
  have hX0 : (0 : ℚ) ≤ (succProd X : ℚ) / (X.prod : ℚ) := by positivity
  have hP0 : (0 : ℚ) ≤ ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have htot : (2 : ℚ) ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ)) *
      ((qnum : ℚ) / (qden : ℚ)) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (opens X).length *
      (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    calc (2 : ℚ)
        = (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := (balance_q C).symm
      _ = (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
            (((succProd X : ℚ) / (X.prod : ℚ)) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) := by
          rw [hsplitP]
      _ ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) *
            (((succProd X : ℚ) / (X.prod : ℚ)) *
              (((qnum : ℚ) / (qden : ℚ)) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (opens X).length *
                (((N : ℚ) + 1) / ((N : ℚ) - 3)))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hpow64 (by norm_num)
          · exact mul_le_mul_of_nonneg_left (hpath.trans hRbound) hX0
          · exact mul_nonneg hX0 hP0
          · positivity
      _ = _ := by ring
  have hlt := final_ineq hN5 (List.prod_pos hXpos) hqden_pos hnum
  linarith

inductive T where
  | U : T
  | L : T
  | J : ℕ → T → T
  | W : ℕ → List ℕ → T → T
  | B : T → T → T

def chk : T → List ℕ → ℕ → Bool
  | .U, X, _ => upOk X
  | .L, X, N => lowOk X N
  | .J N' t, X, _ => jumpOk X N' && chk t X N'
  | .W N' F t, X, N => winOk X F N N' && chk t X N'
  | .B t1 t2, X, N => !decide (N ∈ X) && chk t1 (N :: X) (N + 1) && chk t2 X (N + 1)

theorem sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    ∀ (t : T) (X : List ℕ) (N : ℕ), chk t X N = true → St P X N → False
  | .U, _, _, hchk, h => up_kill C h hchk
  | .L, _, _, hchk, h => low_kill C h hchk
  | .J N' t, X, _, hchk, h => by
    simp only [chk, Bool.and_eq_true] at hchk
    exact sound C t X N' hchk.2 (jump_step C h hchk.1)
  | .W N' F t, X, N, hchk, h => by
    simp only [chk, Bool.and_eq_true] at hchk
    exact sound C t X N' hchk.2 (extend C h hchk.1)
  | .B t1 t2, X, N, hchk, h => by
    simp only [chk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hchk
    obtain ⟨⟨hNX, h1⟩, h2⟩ := hchk
    obtain ⟨hXP, hXn, h19, h79, hcl⟩ := h
    by_cases hNP : N ∈ P
    · refine sound C t1 (N :: X) (N + 1) h1 ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨hNX, hXn⟩,
        List.mem_cons_of_mem _ h19, List.mem_cons_of_mem _ h79, fun p hp hpN => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hNP
        · exact hXP x hx
      · by_cases hpeq : p = N
        · rw [hpeq]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hcl p hp (by omega))
    · refine sound C t2 X (N + 1) h2 ⟨hXP, hXn, h19, h79, fun p hp hpN => ?_⟩
      have hne : p ≠ N := fun e => hNP (e ▸ hp)
      exact hcl p hp (by omega)

def tree : T :=
  (.J 11 (.W 21 [3] (.W 31 [] (.B (.W 37 [] (.B (.W 61 [] (.B (.W 73 [3] (.B (.J 155 (.W 157 [] (.B (.J
  9940 (.W 19879 [3, 107] (.W 22921 [5] (.B (.W 31231 [] (.B (.J 40062 (.W 45841 [] (.B (.J 317746 (.W
  366727 [] (.B (.J 2378990 (.W 4757979 [3, 5, 7] (.W 9515957 [3, 47] (.W 19031913 [3, 11, 1567] (.W
  38063825 [3, 31] .L))))) (.W 524287 [3] (.B (.J 806571 (.W 1048573 [97] (.B (.J 3494795 (.W 5867647
  [3, 7] (.B (.J 8642014 (.W 17284027 [3, 11, 19] (.W 34568053 [3, 5, 31] (.W 69136105 [3, 5, 19] (.W
  138272209 [3, 7, 13] .L))))) (.W 11735295 [3, 7, 47] (.W 23470589 [3, 11] (.W 46941177 [3, 5, 17, 31]
  .L)))))) (.W 1466911 [3] (.B (.J 1791755 (.W 3583509 [3, 7, 11] (.W 7167017 [3, 5, 7] (.W 14334033
  [3, 17, 47] (.W 16777183 [11] (.B (.W 33554367 [3, 5] .L) (.W 33554367 [3] .L))))))) (.W 2933823 [3, 7]
  (.W 5867645 [3, 5, 7] (.W 5867647 [] (.B (.W 11735295 [3, 19, 47] .L) (.W 11735295 [3, 47] .L))))))))))
  (.W 1048575 [3, 97] (.W 1466911 [3] (.B (.W 2933823 [3, 7, 11] (.W 5867645 [3, 7] .L)) (.W 2933823
  [3, 7] (.W 5867645 [3, 7] .L)))))))))) (.W 91683 [3, 7] (.W 131071 [3] (.B (.W 262143 [3, 11, 13, 29]
  (.W 524285 [3] (.W 524287 [] (.B (.W 1048573 [13, 83, 97] .L) (.W 1048575 [3, 13, 83, 97] .L))))) (.W
  262143 [3, 13, 29] (.W 524285 [3] .L)))))))) (.W 45841 [7] (.B (.W 91683 [3, 17] (.W 131071 [11] (.B
  (.W 262143 [3, 11] (.W 366727 [3] (.B (.W 499711 [] .L) (.W 499711 [] .L)))) (.W 262143 [3] .L)))) (.W
  91683 [3] (.W 131071 [3, 11] (.B (.W 262143 [3, 11, 29] .L) (.W 262143 [3, 29] .L)))))))) (.W 31231 []
  (.B (.W 62463 [3, 5, 7] (.W 124925 [3, 31, 277] (.W 131071 [] (.B (.W 149503 [] (.B (.W 299007
  [3, 5, 11, 13] .L) (.W 299007 [3, 11, 13] .L))) (.W 149503 [] .L))))) (.W 62463 [3, 5, 7] (.W 124925
  [3, 5, 31, 277] .L)))))))) (.W 315 [3] (.W 487 [3] (.B (.W 631 [7, 11] (.B (.W 1263 [3, 7, 13] (.W 2525
  [3, 5, 23] (.W 5049 [3, 5, 7] .L))) (.W 1263 [3, 7] (.W 2525 [3, 5, 23] .L)))) (.W 631 [7, 11] (.B (.W
  1263 [3, 13] (.W 1951 [] (.B (.W 3903 [3, 5, 23, 47] .L) (.W 3903 [3, 5, 23] .L)))) (.W 1263 [3] (.W
  1951 [3] .L)))))))))) (.W 127 [11] (.B (.W 157 [3] (.B (.J 171 (.W 313 [3, 5, 11] (.B (.J 374 (.W 487
  [] (.B (.J 1608 (.W 2503 [3, 23] (.B (.J 4493 (.W 8191 [3, 5] (.B (.J 9952 (.W 15583 [3] (.B (.J 27537
  (.W 37591 [3, 5, 7] (.B (.J 102952 (.W 131071 [3, 7] (.B (.J 479878 (.W 524287 [3, 5] (.B (.J 5665264
  (.W 11330527 [3, 5, 47] (.W 16777183 [3, 71, 1531] (.B (.W 33554367 [3, 5, 7, 139] (.W 67108351
  [3, 5, 11, 31] (.B (.W 82018303 [3, 7, 163] (.B (.W 164036607 [3, 5, 7, 19, 31] (.W 307945471 [3, 5, 7]
  .L)) (.W 164016583 [3, 5, 7, 19, 31] (.B (.W 307945471 [3] .L) (.W 307945471 [3, 5, 7] .L))))) (.W
  82018303 [3, 7, 163] (.B (.W 164036607 [3, 5, 7, 19] (.W 307945471 [3, 5, 7, 11] .L)) (.W 164016583
  [3, 5, 7, 19] .L)))))) (.W 33554367 [3, 5, 7, 139] (.W 67108351 [3, 5, 11, 31] (.B (.W 82018303
  [3, 5, 7, 163] (.B (.W 164036607 [3, 5, 7, 31] .L) (.W 164016583 [3, 5, 7, 31] .L))) (.W 82018303
  [3, 5, 7, 163] (.B (.W 164036607 [3, 5, 7] .L) (.W 164016583 [3, 5, 7] .L)))))))))) (.W 1048447 [3] (.B
  (.W 1994623 [3, 5, 13, 211] (.B (.W 2096893 [] (.B (.J 6586320 (.W 13172639 [3, 47] (.W 26345277
  [3, 5, 7, 71] (.W 52690553 [3, 31] (.W 67108351 [5] (.B (.W 82018303 [3, 163] (.B (.W 164036607
  [3, 5, 7, 31] .L) (.W 164036607 [3, 7, 31] .L))) (.W 82018303 [3, 163] (.B (.W 164036607 [3, 5, 7] .L)
  (.W 164036607 [3, 7] .L))))))))) (.W 4193787 [3, 5, 7] (.W 4194271 [3] (.B (.W 4811647 [3] (.B (.J
  5480162 (.W 10960323 [3, 5, 7, 37, 47] (.W 21920645 [3, 5, 7] (.W 33554167 [3, 29] (.B (.W 67108335
  [3, 5, 17, 31] (.W 82018303 [3] (.B (.W 164036607 [3, 5, 7, 3701] .L) (.W 164036607 [3, 5, 7, 3701]
  .L)))) (.W 67108335 [3, 5, 31] (.W 82018303 [3] (.B (.W 164036607 [3, 5, 7, 229, 3701] .L) (.W
  164036607 [3, 5, 7, 229, 3701] .L))))))))) (.W 9623295 [3, 5, 7, 11, 47] (.W 19246589 [3, 7] (.W
  33554167 [3, 5, 7, 29] (.B (.W 67108335 [3, 5, 17, 31] .L) (.W 67108335 [3, 5, 31] .L))))))) (.W
  4811647 [3] (.B (.W 9623295 [3, 5, 11, 37, 47] (.W 19246589 [3, 7, 71] (.W 38493177 [3, 5, 29, 31]
  .L))) (.W 9623295 [3, 5, 11, 47] (.W 19246589 [3, 7, 71] (.W 38493177 [3, 5, 7, 29, 31] .L))))))))))
  (.W 2096893 [] (.B (.W 4193787 [3, 5, 7] (.W 4194271 [] (.B (.W 4811647 [3] (.B (.J 4832595 (.W 9665189
  [3, 5, 7, 11, 37, 47] (.W 19330377 [3, 7] (.W 33554167 [3, 5, 139] (.B (.W 67108335 [3, 5, 17, 31] (.W
  82018303 [3, 7] (.B (.W 164036607 [3, 5, 7, 3701] .L) (.W 164036607 [3, 5, 7, 3701] .L)))) (.W 67108335
  [3, 5, 31] (.W 82018303 [3, 7] .L))))))) (.W 9623295 [3, 5, 7, 11, 47] (.W 19246589 [3, 7] (.W 33554167
  [3, 5, 7, 139] (.B (.W 67108335 [3, 5, 17, 31] .L) (.W 67108335 [3, 5, 31] .L))))))) (.W 4811647 [3]
  (.B (.W 9623295 [3, 5, 11, 37, 47] (.W 19246589 [3, 7, 71] (.W 38493177 [3, 5, 31, 139] .L))) (.W
  9623295 [3, 5, 11, 47] (.W 19246589 [3, 7, 71] (.W 38493177 [3, 5, 7, 31, 139] .L)))))))) (.W 4193787
  [3, 7] (.W 4194271 [3] (.B (.W 4811647 [3] (.B (.W 9623295 [5, 7, 11, 37, 47] (.W 19246589 [3] (.W
  33554167 [5, 29, 139] .L))) (.W 9623295 [3, 5, 7, 11, 47] (.W 19246589 [3] .L)))) (.W 4811647 [3] (.B
  (.W 9623295 [3, 5, 11, 37, 47] (.W 19246589 [3, 71] .L)) (.W 9623295 [3, 5, 11, 47] (.W 19246589
  [3, 71] .L))))))))))) (.W 1994623 [3, 5, 13, 211] (.B (.W 3989247 [3, 5, 7] (.W 4194271 [7] (.B (.W
  4811647 [3] (.B (.W 9623295 [3, 7, 11, 37, 47] (.W 19246589 [3, 7, 1531] .L)) (.W 9623295
  [3, 7, 11, 47] (.W 19246589 [3, 7, 1531] .L)))) (.W 4811647 [3] (.B (.W 9623295 [3, 11, 37, 47] (.W
  19246589 [3, 7, 71, 1531] .L)) (.W 9623295 [3, 11, 47] (.W 19246589 [3, 7, 71, 1531] .L))))))) (.W
  3989247 [3, 7] (.W 4194271 [3, 7] (.B (.W 4811647 [3] (.B (.W 9623295 [3, 5, 7, 11, 37, 47] (.W
  19246589 [3, 1531] .L)) (.W 9623295 [3, 5, 7, 11, 47] .L))) (.W 4811647 [3] (.B (.W 9623295
  [3, 5, 11, 37, 47] .L) (.W 9623295 [3, 5, 11, 47] .L))))))))))))) (.W 262111 [3] (.B (.W 524221
  [3, 5, 7] (.B (.W 524287 [] (.B (.W 1048573 [3, 17] (.B (.W 1994623 [3, 5, 211] (.B (.W 3989247
  [3, 5, 7] (.W 4811647 [3, 41] (.B (.W 9623295 [3, 7, 11, 37, 47] (.W 19246589 [3, 7, 1447] (.W 38493177
  [3, 5, 31] .L))) (.W 9623295 [3, 7, 11, 47] (.W 19246589 [3, 7, 1447] (.W 38493177 [3, 5, 7, 31]
  .L)))))) (.W 3989247 [3, 5, 7] (.W 4811647 [3, 41] (.B (.W 9623295 [3, 5, 7, 11, 37, 47] (.W 19246589
  [3, 1447] .L)) (.W 9623295 [3, 5, 7, 11, 47] (.W 19246589 [3, 1447] .L))))))) (.W 1994623 [3, 5, 211]
  (.B (.W 3989247 [3, 5, 7] (.W 4811647 [3, 5, 41] (.B (.W 9623295 [3, 11, 37, 47] (.W 16777183
  [3, 7, 1447] .L)) (.W 9623295 [3, 11, 47] (.W 16777183 [3, 7, 1447] .L))))) (.W 3989247 [3, 7] (.W
  4811647 [3, 5, 41] (.B (.W 9623295 [3, 5, 11, 37, 47] .L) (.W 9623295 [3, 5, 11, 47] .L)))))))) (.W
  1048575 [3, 17] (.W 1994623 [3, 5, 211] (.B (.W 3989247 [3, 5, 7] (.W 4811647 [3, 41] .L)) (.W 3989247
  [3, 7] .L)))))) (.W 524287 [] (.B (.W 1048573 [3] (.B (.W 1994623 [3, 5, 211] (.B (.W 3989247
  [3, 5, 7, 13] (.W 4811647 [3] (.B (.W 9623295 [3, 7, 11, 37, 47, 137] .L) (.W 9623295
  [3, 7, 11, 47, 137] .L)))) (.W 3989247 [3, 5, 7, 13] (.W 4811647 [3] (.B (.W 9623295
  [5, 7, 11, 37, 47, 137] .L) (.W 9623295 [3, 5, 7, 11, 47, 137] .L)))))) (.W 1994623 [3, 5, 211] (.B (.W
  3989247 [3, 5, 7, 13] (.W 4811647 [3, 5] .L)) (.W 3989247 [3, 7, 13] (.W 4811647 [3, 5] .L)))))) (.W
  1048575 [3] (.W 1994623 [3, 5, 211] (.B (.W 3989247 [3, 5, 7, 13] .L) (.W 3989247 [3, 7, 13] .L))))))))
  (.W 524223 [3, 5, 7] (.W 524287 [3] (.B (.W 1048447 [3] (.B (.W 1048573 [] (.B (.W 1994623 [3, 5, 211]
  (.B (.W 2096893 [] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))) (.W 2096893 [] (.B (.W
  4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))))) (.W 1994623 [3, 5, 211] (.B (.W 2096893 [] (.B (.W
  4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))) (.W 2096893 [] (.B (.W 4193787 [3, 5, 7] .L) (.W
  4193787 [3, 7] .L))))))) (.W 1048573 [] (.B (.W 1994623 [3, 5, 211] (.B (.W 3989247 [3, 5, 7] .L) (.W
  3989247 [3, 5, 7] .L))) (.W 1994623 [3, 5, 211] (.B (.W 3989247 [3, 5, 7] .L) (.W 3989247 [3, 7]
  .L))))))) (.W 1048447 [3] (.B (.W 1994623 [3, 5, 211] .L) (.W 1994623 [3, 5, 211] .L))))))))))) (.W
  75183 [3, 7] (.W 131071 [3, 5, 7] (.B (.W 185221 [3, 7] (.B (.W 262111 [3, 5] (.B (.W 370441 [3, 11]
  (.B (.W 524221 [3, 5] (.B (.W 524287 [3] (.B (.W 1048573 [3, 13, 17, 179] (.B (.W 1994623 [3] .L) (.W
  1994623 [3] .L))) (.W 1048575 [3, 13, 17, 179] .L))) (.W 524287 [3] (.B (.W 1048573 [3, 13, 17, 179]
  (.B (.W 1994623 [3] .L) (.W 1994623 [3] .L))) (.W 1048575 [3, 13, 17, 179] .L))))) (.W 524221 [3, 5]
  (.B (.W 524287 [3] (.B (.W 1048573 [3, 13, 17] (.B (.W 1994623 [3, 7] .L) (.W 1994623 [3, 7] .L))) (.W
  1048575 [3, 13, 17] .L))) (.W 524287 [3] (.B (.W 1048573 [3, 13, 17] .L) (.W 1048575 [3, 13, 17]
  .L))))))) (.W 370441 [3, 11] (.B (.W 524287 [3, 5] (.B (.W 1048447 [3, 17, 179] .L) (.W 1048447
  [3, 17, 179] .L))) (.W 524287 [3, 5] (.B (.W 1048447 [3, 17] .L) (.W 1048447 [3, 17] .L))))))) (.W
  262111 [3, 5] (.B (.W 524221 [3, 5, 7, 11, 47] (.B (.W 524287 [3] (.B (.W 1048573 [3, 7, 13, 17] .L)
  (.W 1048575 [3, 7, 13, 17] .L))) (.W 524287 [3] (.B (.W 1048573 [3, 7, 13, 17] .L) (.W 1048575
  [3, 7, 13, 17] .L))))) (.W 524223 [3, 5, 7, 11, 47] (.W 524287 [3] (.B (.W 1048447 [3, 7, 11, 13, 17]
  .L) (.W 1048447 [3, 7, 11, 13, 17] .L)))))))) (.W 185221 [3, 7] (.B (.W 262111 [3, 5] (.B (.W 370441
  [3] (.B (.W 524221 [3, 5] .L) (.W 524221 [3, 5] .L))) (.W 370441 [3] (.B (.W 524287 [3, 5] .L) (.W
  524287 [3, 5] .L))))) (.W 262111 [3, 5] (.B (.W 524221 [3, 5, 7, 47] .L) (.W 524223 [3, 5, 7, 47]
  .L))))))))))) (.W 16381 [5] (.B (.J 25354 (.W 36037 [3, 7, 181] (.B (.J 85528 (.W 131071 [3, 7] (.B (.J
  246141 (.W 492281 [3, 5, 7, 11] (.W 524287 [3, 19] (.B (.W 1048573 [3, 7, 13, 17] (.B (.W 1153183 [3]
  (.B (.J 2989318 (.W 4194271 [3, 5, 113] (.B (.J 10405388 (.W 20810775 [3, 5, 113] (.W 33548287 [3] (.B
  (.W 33554167 [] (.B (.W 67108335 [3, 5, 7, 17, 31, 397] (.W 82018303 [3] (.B (.W 164036607
  [3, 5, 7, 13, 283] (.W 328073213 [3, 5, 7, 131, 167] (.W 656146423 [3, 5, 233] (.B (.W 1073733343
  [5, 7, 1483] .L) (.W 1073733343 [5, 7, 1483] .L))))) (.W 164036607 [3, 7, 13, 283, 3539] (.W 328073213
  [3, 5, 7, 131, 167] (.W 656146425 [3, 5, 17, 233] .L)))))) (.W 67108335 [3, 5, 7, 31, 397] (.W 82018303
  [3] (.B (.W 164036607 [3, 5, 7, 13, 229, 283] (.W 328073213 [3, 5, 7, 131, 167] (.W 656146423
  [3, 5, 7, 233] .L))) (.W 164036607 [3, 7, 13, 229, 283, 3539] (.W 328073213 [3, 5, 7, 131, 167]
  .L))))))) (.W 33554167 [] (.B (.W 66572383 [3, 5, 7, 31] (.B (.W 82018303 [3, 17] (.B (.W 164036607
  [3, 5, 7, 13, 283] (.W 328073213 [3, 5] (.W 656146423 [3, 5, 19, 233] .L))) (.W 164036607
  [3, 5, 7, 13, 283] (.W 328073213 [3, 5] .L)))) (.W 82018303 [3, 5, 17] (.B (.W 164036607
  [3, 5, 7, 13, 283, 1381] (.W 328073213 [3, 5, 7, 131, 167] (.W 656146423 [3, 5, 7, 233] .L))) (.W
  164036607 [3, 7, 13, 283, 1381, 3539] (.W 328073213 [3, 5, 7, 23, 131, 167] .L)))))) (.W 66572383
  [3, 5, 7, 31] (.B (.W 82018303 [3] (.B (.W 164036607 [5, 7, 13, 229, 283] (.W 328073213 [3] .L)) (.W
  164036607 [3, 5, 7, 13, 229, 283] (.W 328073213 [3] .L)))) (.W 82018303 [3, 5] (.B (.W 164036607
  [3, 5, 7, 13, 229, 283, 1381] (.W 328073213 [3, 5, 7, 131, 167] .L)) (.W 164036607
  [3, 7, 13, 229, 283, 1381, 3539] (.W 328073213 [3, 5, 7, 23, 131, 167] .L)))))))))))) (.W 8388543
  [3, 7, 11] (.W 10172191 [3, 7, 13, 47] (.B (.W 20344383 [3, 71, 151] (.W 33548287 [] (.B (.W 67096575
  [3, 5, 31, 397] (.W 67108351 [] (.B (.W 134216703 [3, 7, 31] .L) (.W 134216703 [3, 7] .L)))) (.W
  67096575 [3, 5, 31] (.W 67108351 [3] (.B (.W 134216703 [3, 7, 31, 1381] .L) (.W 134216703 [3, 7, 1381]
  .L))))))) (.W 20344383 [3, 5, 71, 113] (.W 33292033 [3, 5] (.B (.W 33548287 [] (.B (.W 67096575
  [3, 5, 31, 397] .L) (.W 67096575 [3, 5, 31] .L))) (.W 33548287 [3] (.B (.W 67096575 [3, 5, 7, 31, 397]
  .L) (.W 66572383 [3, 5, 7, 31] .L)))))))))))) (.W 2306367 [3, 5, 7, 233] (.W 4194271 [3, 5, 13, 113]
  (.B (.W 8388543 [3, 5, 7, 11] (.W 10172191 [3, 7, 11, 47] (.B (.W 20344383 [3, 7, 151] .L) (.W 20344383
  [3, 5, 7, 113] .L)))) (.W 8388543 [3, 5, 7, 11] (.W 10172191 [3, 7, 11, 47] (.B (.W 20344383
  [3, 7, 71, 151] .L) (.W 20344383 [3, 5, 7, 71, 113] .L))))))))) (.W 1153183 [3] (.B (.W 2306367
  [3, 5, 7, 233] (.W 4194271 [3, 5, 13, 113] (.B (.W 8388543 [3, 5, 7, 11] (.W 10172191 [3, 13, 47] (.B
  (.W 16777183 [3] (.B (.W 33548287 [3, 151] .L) (.W 33548287 [3, 151] .L))) (.W 16777183 [3, 5, 113] (.B
  (.W 33548287 [3, 5] .L) (.W 33548287 [3, 5] .L)))))) (.W 8388543 [3, 5, 7, 11] (.W 10172191 [3, 13, 47]
  (.B (.W 16777183 [3, 71] .L) (.W 16777183 [3, 5, 71, 113] .L))))))) (.W 2306367 [3, 5, 7, 233] (.W
  4194271 [3, 5, 13, 113] (.B (.W 8388543 [3, 5, 7, 11] (.W 10172191 [3, 11, 47] .L)) (.W 8388543
  [3, 5, 7, 11] .L)))))))) (.W 1048575 [3, 7, 13, 17] (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 233] (.W
  4194271 [3, 5, 13, 113] (.B (.W 8388543 [3, 7, 11] .L) (.W 8388543 [3, 7, 11] .L)))) (.W 2306367
  [3, 5, 7, 233] (.W 4194271 [3, 5, 13, 113] .L))))))))) (.W 262143 [3, 5] (.W 524285 [3, 5, 7, 19] (.W
  524287 [] (.B (.W 1048573 [3, 7, 17] (.B (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 233] .L) (.W 2306367
  [3, 5, 7, 233] .L))) (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 233] .L) (.W 2306367 [3, 5, 7, 233]
  .L))))) (.W 1048575 [3, 7, 17] (.W 1153183 [3] .L))))))))) (.W 37591 [] (.B (.J 77886 (.W 131071
  [3, 5, 7] (.B (.J 191945 (.W 383889 [3, 7, 11, 23] (.W 524287 [3, 19] (.B (.W 1048573 [3, 5, 13] (.B
  (.W 2097147 [3, 5, 211, 233] (.W 4194271 [3, 7, 139] (.B (.W 4811647 [3] (.B (.W 9623295
  [3, 7, 11, 37, 47] .L) (.W 9623295 [3, 7, 11, 47] .L))) (.W 4811647 [3] (.B (.W 9623295
  [3, 7, 11, 37, 47] .L) (.W 9623295 [3, 7, 11, 47] .L)))))) (.W 2097147 [3, 5, 211, 233] (.W 4194271
  [3, 7, 139] (.B (.W 4811647 [3, 5] (.B (.W 9623295 [3, 7, 11, 37, 47] .L) (.W 9623295 [3, 7, 11, 47]
  .L))) (.W 4811647 [3, 5] (.B (.W 9623295 [3, 7, 11, 37, 47] .L) (.W 9623295 [3, 7, 11, 47] .L))))))))
  (.W 1048575 [3, 5, 13] (.W 2097149 [3, 5, 211, 233] (.W 4194271 [3, 7, 139] .L))))))) (.W 262143
  [3, 23] (.W 524285 [3, 7, 19] (.W 524287 [] (.B (.W 1048573 [3, 5] (.B (.W 2097147 [3, 5, 211, 233] .L)
  (.W 2097147 [3, 5, 211, 233] .L))) (.W 1048575 [3, 5] .L)))))))) (.W 75183 [3, 5, 7] (.W 131071
  [3, 5, 7] (.B (.W 185221 [3, 7] (.B (.W 370441 [3, 5, 11, 23] (.B (.W 524287 [3, 11, 19] (.B (.W
  1048573 [3, 5, 13, 17, 179] .L) (.W 1048575 [3, 5, 13, 17, 179] .L))) (.W 524287 [3, 11, 19] (.B (.W
  1048573 [3, 5, 13, 17] .L) (.W 1048575 [3, 5, 13, 17] .L))))) (.W 370443 [3, 5, 7, 11, 23, 47] (.W
  524287 [3, 11, 19] .L)))) (.W 185221 [3, 7] (.B (.W 370441 [3, 5, 23] .L) (.W 370443 [3, 5, 7, 23, 47]
  .L))))))))))) (.W 20023 [3, 19] (.B (.W 36037 [3, 7] (.B (.J 43869 (.W 72073 [3, 7] (.B (.J 112101 (.W
  131071 [3] (.B (.J 774508 (.W 1048447 [17] (.B (.J 2964264 (.W 4194271 [3, 5] (.B (.J 10108011 (.W
  20216021 [3, 5, 11, 113] (.W 33554167 [3, 11, 29] (.B (.W 41007103 [3, 5, 31] (.B (.W 82014207
  [3, 5, 7, 17] (.W 164028413 [3, 5, 7, 173] (.W 292904671 [3, 5, 7, 41] (.B (.W 585809343
  [3, 7, 13, 233, 307] .L) (.W 585809343 [3, 7, 233, 307] .L))))) (.W 82014207 [3, 5, 7, 17, 23] (.W
  164028413 [3, 5, 7, 173] (.W 292904671 [3, 5, 7, 41] .L))))) (.W 41007103 [3, 5, 31] (.B (.W 82014207
  [3, 5, 7] (.W 164028413 [3, 5, 7, 173, 229] (.W 292904671 [3, 7, 41] .L))) (.W 82014207 [3, 5, 7, 23]
  (.W 164028413 [3, 5, 7, 173, 229] .L)))))))) (.W 5085841 [3] (.B (.J 7105929 (.W 9225343 [3, 5, 47] (.B
  (.J 30930535 (.W 40686727 [3, 29, 31] (.B (.J 128991119 (.W 257982237 [3, 5, 7] (.W 515964473
  [3, 5, 11] (.W 1031928945 [3, 7, 233] (.W 1180843903 [3, 8941] (.B (.W 2147483647 [3, 5, 53] .L) (.W
  2147483647 [3, 5, 53] .L))))))) (.W 67108351 [3] (.B (.W 134216703 [3, 5, 7, 31] (.W 162746911 [3, 7]
  (.B (.W 325493823 [3, 5, 281] (.W 536866807 [7] (.B (.W 1073733615 [3, 29, 233] (.W 1180843903 [3] (.B
  (.W 1301975287 [] (.B (.W 2147483647 [3, 5] .L) (.W 2147483647 [3, 5] .L))) (.W 1301975287 [] (.B (.W
  2147483647 [3, 5] .L) (.W 2147483647 [3, 5] .L)))))) (.W 1073733615 [3, 233] (.W 1180843903 [3] (.B (.W
  1301975287 [] (.B (.W 2147483647 [5, 7] .L) (.W 2147483647 [5, 7] .L))) (.W 1301975287 [] .L))))))) (.W
  325493823 [3, 5] (.W 536866807 [3, 7] (.B (.W 1073733615 [3, 17, 29, 233] .L) (.W 1073733615
  [3, 17, 233] .L))))))) (.W 134216703 [3, 5, 7] (.W 162746911 [3, 7] (.B (.W 325493823 [3, 5, 11, 281]
  (.W 650987645 [3, 7, 233] .L)) (.W 325493823 [3, 5, 11] (.W 650987645 [3, 7, 233] .L)))))))))) (.W
  18450687 [3, 13, 71] (.W 36901373 [3, 29, 31] (.W 40686727 [5] (.B (.W 67108351 [3] (.B (.W 134216703
  [3, 5, 7, 31] (.W 268433405 [3, 7, 173] .L)) (.W 134216703 [3, 5, 7] .L))) (.W 67108351 [3] (.B (.W
  134216703 [3, 5, 31] .L) (.W 134216703 [3, 5] .L)))))))))) (.W 9225343 [3, 5, 47] (.B (.W 18450687
  [3, 5, 71, 113] (.W 33292033 [3, 11] (.B (.W 41007103 [3, 29, 31] (.B (.W 82014207 [3, 5, 7] .L) (.W
  82014207 [3, 5, 7] .L))) (.W 41007103 [3, 29, 31] (.B (.W 67108351 [3, 5] (.B (.W 134216703
  [3, 5, 7, 31] .L) (.W 134216703 [3, 5, 7] .L))) (.W 67108351 [3, 5] (.B (.W 134216703 [3, 5, 7, 23, 31]
  .L) (.W 134216703 [3, 5, 7, 23] .L)))))))) (.W 18450687 [3, 5, 11, 71, 113] (.W 33292033 [3, 11] (.B
  (.W 41007103 [5, 29, 31] (.B (.W 82014207 [3, 5] .L) (.W 82014207 [3, 5] .L))) (.W 41007103
  [3, 5, 29, 31] (.B (.W 67108351 [3, 5] .L) (.W 67108351 [3, 5] .L))))))))))))) (.W 2096895 [3, 13, 71]
  (.W 2562943 [3, 5, 7] (.B (.W 4194271 [3, 5, 7] (.B (.W 8388543 [3, 5, 7] (.W 9225343 [47] (.B (.W
  18450687 [3, 5, 113, 1531] (.W 33554167 [3, 887, 2357] .L)) (.W 18450687 [3, 11, 113, 1531] (.W
  33554167 [3, 887, 2357] .L))))) (.W 8388543 [3, 5] (.W 9225343 [3, 47] (.B (.W 18450687
  [3, 5, 71, 113, 1531] (.W 33292033 [887, 2357] .L)) (.W 18450687 [3, 11, 71, 113, 1531] .L)))))) (.W
  4194271 [3, 5, 7] (.B (.W 5085841 [3] (.B (.W 9225343 [3, 7, 47] (.B (.W 18450687 [3, 5, 13, 1531] (.W
  33554167 [3] .L)) (.W 18450687 [3, 13, 1531] .L))) (.W 9225343 [3, 5, 7, 47] (.B (.W 18450687
  [3, 5, 113, 1531] .L) (.W 18450687 [3, 5, 11, 113, 1531] .L))))) (.W 5085841 [3] (.B (.W 9225343
  [3, 47] (.B (.W 18450687 [3, 5, 13, 71, 1531] .L) (.W 18450687 [3, 13, 71, 1531] .L))) (.W 9225343
  [3, 5, 47] (.B (.W 18450687 [3, 5, 71, 113, 1531] .L) (.W 18450687 [3, 5, 11, 71, 113, 1531]
  .L))))))))))))) (.W 160183 [5] (.B (.J 373451 (.W 524287 [3] (.B (.J 1298067 (.W 2596133 [3, 5, 7, 71]
  (.W 5192265 [3, 5, 7] (.W 9225343 [3, 5, 47] (.B (.W 16777183 [3, 113, 1531] (.B (.W 33554367
  [3, 5, 79, 887] .L) (.W 33554367 [3, 5, 79, 887] .L))) (.W 16777183 [3, 113, 1531] (.B (.W 33554367
  [3, 5, 11, 79, 887] .L) (.W 33554367 [3, 11, 79, 887] .L)))))))) (.W 1048447 [3, 7, 17] (.B (.W 1281463
  [3] (.B (.W 2096893 [3] (.B (.J 2142789 (.W 4285577 [3, 5] (.W 8571153 [3, 47] (.W 9225343 [] (.B (.W
  18450687 [3, 5, 7, 113] (.W 36901373 [3, 31] (.W 73802745 [3, 5, 7] .L))) (.W 18450687 [3, 7, 11, 113]
  (.W 36901373 [3, 31] .L))))))) (.W 4193787 [3, 5, 7] (.W 8387573 [3] (.W 9225343 [5, 47] (.B (.W
  18450687 [3, 5, 7, 113] .L) (.W 18450687 [3, 7, 11, 113] .L))))))) (.W 2096893 [3] (.B (.W 4193787
  [3, 5, 7] (.W 8387573 [3, 5] (.W 9225343 [47] (.B (.W 18450687 [3, 5, 7, 113] .L) (.W 18450687
  [3, 7, 11, 113] .L))))) (.W 4193787 [3, 5, 7] (.W 8387573 [3, 5] .L)))))) (.W 1281463 [3] (.B (.W
  2562927 [3, 5, 7, 71] (.W 5125853 [3, 5, 7] (.W 9225343 [3, 5, 47] .L))) (.W 2562927 [3, 5, 7, 71] (.W
  5125853 [3, 5, 7] (.W 9225343 [3, 5, 47] .L)))))))))) (.W 262111 [5] (.B (.W 524221 [3] (.B (.W 524287
  [] (.B (.J 774920 (.W 1048573 [17] (.B (.J 2969308 (.W 5085841 [3, 5, 41] (.B (.J 7134983 (.W 9225343
  [3, 7, 47] (.B (.J 31488670 (.W 40686727 [3, 5, 31] (.B (.J 139287111 (.W 278574221 [3, 17] (.W
  557148441 [3, 5, 233] (.W 1114296881 [3, 43] (.W 1180843903 [] (.B (.W 2147477503 [3, 53] (.B (.W
  2147483647 [] (.B (.W 4294967295 [3, 5, 37, 9241] .L) (.W 4294967295 [3, 5, 37] .L))) (.W 2147483647 []
  (.B (.W 4294967295 [3, 5, 37, 9241] .L) (.W 4294967295 [3, 5, 37] .L))))) (.W 2147477503 [3, 53]
  .L))))))) (.W 81373455 [3, 7, 29] (.W 162746909 [3, 7, 13] (.W 162746911 [] (.B (.W 325493823
  [3, 5, 17, 281] (.W 650987645 [3, 5, 233] .L)) (.W 325493823 [3, 5, 17] (.W 650987645 [3, 5, 233]
  .L))))))))) (.W 18450687 [3, 13, 1447] (.W 36901373 [3, 5, 31] (.W 40686727 [5] (.B (.W 81373455
  [3, 7, 29] (.W 162746909 [3, 7, 13, 173] .L)) (.W 81373455 [3, 29] (.W 162746909 [3, 7, 13, 173]
  .L))))))))) (.W 9225343 [3, 7, 47] (.B (.W 18450687 [3, 5, 113, 1447] (.W 36901373 [3, 5, 11, 31] (.W
  41007103 [3] (.B (.W 82014207 [3, 5, 7, 29] .L) (.W 82014207 [3, 5, 7, 23, 29] .L))))) (.W 18450687
  [3, 5, 11, 113, 1447] (.W 36901373 [3, 5, 11, 31] (.W 41007103 [3, 5] (.B (.W 82014207 [3, 5, 7, 29]
  .L) (.W 82014207 [3, 5, 7, 23, 29] .L)))))))))) (.W 2097147 [3] (.W 2562943 [3, 5, 7] (.B (.W 5125887
  [3, 5, 41] (.W 9225343 [3, 47] (.B (.W 16777183 [3, 113, 1447] (.B (.W 33554367 [3, 5, 2357] .L) (.W
  33554367 [3, 5, 2357] .L))) (.W 16777183 [3, 113, 1447] (.B (.W 33554367 [3, 5, 11, 2357] .L) (.W
  33554367 [3, 11, 2357] .L)))))) (.W 5085841 [3, 5, 41] (.B (.W 9225343 [3, 47] (.B (.W 16777183
  [13, 1447] .L) (.W 16777183 [13, 1447] .L))) (.W 9225343 [3, 47] (.B (.W 16777183 [3, 5, 113, 1447] .L)
  (.W 16777183 [3, 5, 113, 1447] .L))))))))))) (.W 1048575 [3, 5, 7, 17] (.W 2097149 [3] (.W 2562943
  [5, 7] (.B (.W 5125887 [3, 5, 41] .L) (.W 5085841 [3, 5, 41] .L))))))) (.W 524287 [] (.B (.W 1048573
  [3, 5, 7, 17] (.B (.W 2097147 [3, 5, 13] (.W 2562943 [5, 7] (.B (.W 5125887 [3, 5] (.W 9225343
  [3, 7, 47, 137] .L)) (.W 5085841 [3, 5] (.B (.W 9225343 [7, 47, 137] .L) (.W 9225343 [3, 7, 47, 137]
  .L)))))) (.W 2097147 [3, 13] (.W 2562943 [3, 5, 7] (.B (.W 5125887 [3, 5] (.W 9225343 [3, 47, 137] .L))
  (.W 5085841 [3, 5] .L)))))) (.W 1048575 [3, 5, 7, 17] (.W 2097149 [3, 13] (.W 2562943 [5, 7] (.B (.W
  5125887 [3, 5] .L) (.W 5085841 [3, 5] .L))))))))) (.W 524223 [3] (.W 524287 [3] (.B (.W 1048447
  [5, 7, 17] (.B (.W 1048573 [] (.B (.W 2096893 [3] (.B (.W 2562943 [5, 7] (.B (.W 5125887 [3, 5] .L) (.W
  5085841 [3, 5] .L))) (.W 2562943 [5, 7] (.B (.W 5125887 [3, 5] .L) (.W 5085841 [3, 5] .L))))) (.W
  2096893 [3] (.B (.W 2562943 [3, 5, 7] (.B (.W 5125887 [3, 5] .L) (.W 5085841 [3, 5] .L))) (.W 2562943
  [3, 5, 7] (.B (.W 5125887 [3, 5] .L) (.W 5085841 [3, 5] .L))))))) (.W 1048573 [] (.B (.W 2097147
  [3, 5, 71] (.W 2562943 [5, 7] (.B (.W 5125887 [3, 5, 7] .L) (.W 5085841 [3, 5, 7] .L)))) (.W 2097147
  [3, 71] (.W 2562943 [3, 5, 7] .L)))))) (.W 1048447 [5, 7, 17] (.B (.W 2096893 [3] .L) (.W 2096895
  [3, 71] .L))))))))))))) (.W 131071 [3] (.B (.W 160183 [3] (.B (.W 262111 [5] (.B (.W 524221 [3, 5, 11]
  (.B (.W 524287 [3] (.B (.J 773445 (.W 1048573 [13, 17] (.B (.J 2947765 (.W 4194271 [5, 41] (.B (.J
  9918706 (.W 19837411 [3, 7, 113, 1447] (.W 33554167 [3, 79] (.B (.W 67108335 [3, 5, 7, 11, 17, 29, 31]
  (.W 134216669 [3, 5, 19] (.W 146454367 [7, 13] (.B (.W 292908735 [3, 5, 13, 17] .L) (.W 292908735
  [3, 5, 7, 17, 43, 131] .L))))) (.W 67108335 [3, 5, 7, 11, 29, 31] (.W 134216669 [3, 5, 19] (.W
  146454367 [7, 13, 229] (.B (.W 292908735 [3, 13, 17] .L) (.W 292908735 [3, 7, 17, 43, 131] .L)))))))))
  (.W 8388543 [3, 5] (.W 16777085 [3, 7, 11, 47, 113, 1447] (.W 33292033 [3, 7, 71, 79] (.B (.W 66584067
  [3, 5, 31] .L) (.W 66584067 [3, 5, 7, 11, 31] .L)))))))) (.W 1153183 [3] (.B (.J 2348786 (.W 4194271
  [3, 5, 41] (.B (.J 5338130 (.W 10676259 [3, 7, 13, 47] (.W 16777183 [3, 113, 1447] (.B (.W 33554167
  [3, 79] (.B (.W 67108335 [3, 5, 11, 17, 29, 31] (.W 134216669 [3, 5, 19] (.W 268433337
  [3, 5, 7, 17, 19, 43, 283] .L))) (.W 67108335 [3, 5, 11, 29, 31] (.W 134216669 [3, 5, 19] (.W 268433337
  [3, 7, 17, 19, 43, 229, 283] .L))))) (.W 33554167 [3, 79] (.B (.W 67108335 [3, 5, 11, 17, 29, 31] (.W
  134216669 [3, 5, 19, 109] .L)) (.W 67108335 [3, 5, 11, 29, 31] (.W 134216669 [3, 5, 19, 109] .L))))))))
  (.W 8388543 [3, 5] (.W 16777085 [3, 13, 47, 113, 1447] (.W 16777183 [71] (.B (.W 33292033 [3, 79] (.B
  (.W 66584067 [3, 5, 31] .L) (.W 66584067 [3, 5, 11, 31] .L))) (.W 33292033 [3, 79] (.B (.W 66584067
  [3, 5, 31] .L) (.W 66584067 [3, 5, 11, 31] .L)))))))))) (.W 1281463 [] (.B (.J 1950995 (.W 3901989
  [3, 5, 7] (.W 4194271 [5, 41] (.B (.W 8388543 [3, 5, 7] (.W 16777085 [3, 7, 11, 47, 113, 1447] (.W
  16777183 [] (.B (.W 33554167 [3, 7] (.B (.W 67108335 [3, 5, 7, 17, 29, 31] (.W 134216669 [3, 5, 19]
  .L)) (.W 67108335 [3, 5, 7, 29, 31] (.W 134216669 [3, 5, 19] .L)))) (.W 33554167 [3, 7] (.B (.W
  67108335 [3, 5, 7, 17, 29, 31] (.W 134216669 [3, 5, 19, 109] .L)) (.W 67108335 [3, 5, 7, 29, 31]
  .L))))))) (.W 8388543 [3, 5] (.W 16777085 [3, 7, 11, 47, 113, 1447] (.W 16777183 [71] (.B (.W 33292033
  [3, 7] (.B (.W 66584067 [3, 5, 31] .L) (.W 66584067 [3, 5, 7, 31] .L))) (.W 33292033 [3, 7] (.B .L (.W
  66584067 [3, 5, 7, 31] .L))))))))))) (.W 2562927 [3, 7] (.W 4194271 [3, 5, 41] (.B (.W 8388543
  [3, 5, 7] (.W 16777085 [3, 11, 47, 113, 1447] (.W 16777183 [] (.B (.W 33554167 [3, 7, 79] .L) (.W
  33554167 [3, 7, 79] .L))))) (.W 8388543 [3, 5] (.W 16777085 [3, 11, 47, 113, 1447] .L)))))))))))) (.W
  1048575 [3, 13, 17] (.W 1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] (.W 4194271 [5, 41]
  (.B (.W 8388543 [3, 7] (.W 16777085 [3, 7, 13, 47, 113, 1447] .L)) (.W 8388543 [3] (.W 16777085
  [3, 7, 13, 47, 113, 1447] .L))))) (.W 2562927 [3, 5, 7] (.W 4194271 [3, 5, 41] (.B (.W 8388543
  [3, 5, 7] .L) (.W 8388543 [3, 5] .L)))))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] (.W 4194271 [5, 41]
  (.B (.W 8388543 [3, 5, 7] .L) (.W 8388543 [3, 5] .L)))) (.W 2562927 [3, 7] (.W 4194271 [3, 5, 41] (.B
  (.W 8388543 [3, 5, 7] .L) (.W 8388543 [3, 5] .L))))))))))) (.W 524287 [3] (.B (.W 1048573 [3, 13, 17]
  (.B (.W 1153183 [3] (.B (.W 1281463 [] (.B (.J 1668591 (.W 3337181 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B
  (.W 8388543 [3, 7, 137] (.W 16777085 [3, 7, 13, 47, 113] (.W 33554167 [3, 761] (.B (.W 67108335
  [3, 5, 17, 31, 61] .L) (.W 67108335 [3, 5, 31, 61] .L))))) (.W 8388543 [3, 137] (.W 16777085
  [3, 7, 13, 47, 113] (.W 33292033 [3, 71] .L))))))) (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W
  8388543 [3, 5, 7, 137] (.W 16777085 [3, 7, 13, 47, 113] .L)) (.W 8388543 [3, 5, 137] (.W 16777085
  [3, 7, 13, 47, 113] .L))))))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W
  8388543 [3, 5, 7, 137] (.W 16777085 [3, 7, 11, 47, 113] .L)) (.W 8388543 [3, 5, 137] (.W 16777085
  [3, 7, 11, 47, 113] .L))))) (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W 8388543 [3, 5, 7, 137]
  (.W 16777085 [3, 7, 11, 47, 113] .L)) (.W 8388543 [3, 5, 137] .L)))))))) (.W 1153183 [3] (.B (.W
  1281463 [] (.B (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W 8388543 [3, 5, 7, 137] (.W 16777085
  [3, 7, 13, 47, 113] .L)) (.W 8388543 [3, 5, 137] (.W 16777085 [3, 7, 13, 47, 113] .L))))) (.W 2562927
  [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W 8388543 [3, 5, 7, 137] (.W 16777085 [3, 13, 47, 113] .L)) (.W
  8388543 [3, 5, 137] .L)))))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W
  8388543 [3, 5, 7, 137] .L) (.W 8388543 [3, 5, 137] .L)))) (.W 2562927 [3, 7, 13] (.W 4194271 [3, 5] (.B
  (.W 8388543 [3, 5, 7, 137] .L) (.W 8388543 [3, 5, 137] .L)))))))))) (.W 1048575 [3, 13, 17] (.W 1153183
  [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] (.B (.W 8388543 [3, 7, 137] .L)
  (.W 8388543 [3, 137] .L)))) (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] .L)))) (.W 1281463 [] (.B (.W
  2562927 [3, 5, 7, 13] (.W 4194271 [3, 5] .L)) (.W 2562927 [3, 7, 13] (.W 4194271 [3, 5] .L)))))))))))
  (.W 524223 [3, 5, 11] (.W 524287 [3] (.B (.W 1048447 [3, 17] (.B (.W 1048573 [13] (.B (.W 1153183 [3]
  (.B (.W 1281463 [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] (.W 4194271 [] (.B (.W 8388543 [3, 7]
  .L) (.W 8388543 [3] .L)))) (.W 4193787 [3, 5, 7] (.W 4194271 [3] (.B (.W 8388543 [3, 5, 7] .L) (.W
  8388543 [3, 5] .L)))))) (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] (.W 4194271 [] (.B (.W 8388543
  [3, 5, 7] .L) (.W 8388543 [3, 5] .L)))) (.W 4193787 [3, 5, 7] (.W 4194271 [3] (.B (.W 8388543 [3, 5, 7]
  .L) (.W 8388543 [3, 5] .L)))))))) (.W 1281463 [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] (.W
  4194271 [] (.B (.W 8388543 [3, 5, 7] .L) (.W 8388543 [3, 5] .L)))) (.W 4193787 [3, 5, 7] .L))) (.W
  2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))))))) (.W 1153183 [3] (.B (.W
  1281463 [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] (.W 4194271 [] (.B (.W 8388543 [3, 5, 7] .L)
  (.W 8388543 [3, 5] .L)))) (.W 4193787 [3, 5, 7] .L))) (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W
  4193787 [3, 5, 7] .L))))) (.W 1281463 [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787
  [3, 5, 7] .L))) (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))))))))) (.W
  1048573 [13] (.B (.W 1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 71] (.W 4194271 [3, 5, 7]
  .L)) (.W 2562927 [3, 5, 7, 71] (.W 4194271 [3, 5, 7] .L)))) (.W 1281463 [] (.B (.W 2562927
  [3, 5, 7, 71] (.W 4194271 [3, 5, 7] .L)) (.W 2562927 [3, 5, 7, 71] (.W 4194271 [3, 5, 7] .L)))))) (.W
  1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 71] (.W 4194271 [3, 5, 7] .L)) (.W 2562927
  [3, 5, 7, 71] (.W 4194271 [3, 5, 7] .L)))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 71] (.W 4194271
  [3, 5, 7] .L)) (.W 2562927 [3, 7, 71] (.W 4194271 [3, 5, 7] .L)))))))))) (.W 1048447 [3, 17] (.B (.W
  1153183 [3, 13] (.B (.W 1281463 [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787
  [3, 5, 7] .L))) (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))))) (.W 1281463
  [] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))) (.W 2096893 [3]
  .L))))) (.W 1153183 [3, 13] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 71] .L) (.W 2562927
  [3, 5, 7, 71] .L))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 71] .L) (.W 2562927 [3, 7, 71]
  .L)))))))))))) (.W 262111 [5] (.B (.W 524221 [3, 5, 11] (.B (.W 524287 [3] (.B (.W 1048573
  [3, 5, 13, 17] (.B (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7] (.W 2562943 [] (.B (.W 4194271 [5, 41] .L)
  (.W 4194271 [5, 41] .L)))) (.W 2306367 [3, 5, 7] (.W 2562943 [3] (.B (.W 4194271 [5, 41] .L) (.W
  4194271 [5, 41] .L)))))) (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7] (.W 2562943 [] (.B (.W 4194271
  [5, 41] .L) (.W 4194271 [5, 41] .L)))) (.W 2306367 [3, 7] (.W 2562943 [3] .L)))))) (.W 1048575
  [3, 5, 13, 17] (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7] .L) (.W 2306367 [3, 7] .L)))))) (.W 524287 [3]
  (.B (.W 1048573 [3, 5, 13, 17] (.B (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 13] (.W 2562943 [] .L))
  (.W 2306367 [3, 5, 7, 13] .L))) (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 13] .L) (.W 2306367
  [3, 7, 13] .L))))) (.W 1048575 [3, 5, 13, 17] (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 13] .L) (.W
  2306367 [3, 7, 13] .L)))))))) (.W 524223 [3, 5, 11] (.W 524287 [3] (.B (.W 1048447 [3, 5, 17] (.B (.W
  1048573 [13] (.B (.W 1153183 [3] (.B (.W 2096893 [3] .L) (.W 2096893 [3] .L))) (.W 1153183 [3] (.B (.W
  2096893 [3] .L) (.W 2096893 [3] .L))))) (.W 1048573 [13] (.B (.W 1153183 [3] (.B (.W 2306367
  [3, 5, 7, 71] .L) (.W 2306367 [3, 5, 7, 71] .L))) (.W 1153183 [3] (.B (.W 2306367 [3, 5, 7, 71] .L) (.W
  2306367 [3, 7, 71] .L))))))) (.W 1048447 [3, 5, 17] .L)))))))) (.W 160183 [3] (.B (.W 262111 [5] (.B
  (.W 524221 [3, 5] (.B (.W 524287 [] (.B (.W 1048573 [3, 17] (.B (.W 1153183 [3] (.B (.W 1281463 [] (.B
  (.W 2562927 [3, 5, 7] .L) (.W 2562927 [3, 5, 7] .L))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] .L) (.W
  2562927 [3, 5, 7] .L))))) (.W 1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] .L) (.W 2562927
  [3, 5, 7] .L))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] .L) (.W 2562927 [3, 7] .L))))))) (.W 1048575
  [3, 17] (.W 1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927 [3, 5, 7] .L) (.W 2562927 [3, 5, 7] .L)))
  (.W 1281463 [] .L)))))) (.W 524287 [] (.B (.W 1048573 [3, 17] (.B (.W 1153183 [3] (.B (.W 1281463 []
  (.B (.W 2562927 [3, 5, 7, 13] .L) (.W 2562927 [3, 5, 7, 13] .L))) (.W 1281463 [] (.B (.W 2562927
  [3, 5, 7, 13] .L) (.W 2562927 [3, 5, 7, 13] .L))))) (.W 1153183 [3] (.B (.W 1281463 [] (.B (.W 2562927
  [3, 5, 7, 13] .L) (.W 2562927 [3, 5, 7, 13] .L))) (.W 1281463 [] (.B (.W 2562927 [3, 5, 7, 13] .L) (.W
  2562927 [3, 7, 13] .L))))))) (.W 1048575 [3, 17] .L))))) (.W 524223 [3, 5] (.W 524287 [3] (.B (.W
  1048447 [3, 17] .L) (.W 1048447 [3, 17] .L)))))) (.W 262111 [5] (.B (.W 524221 [3, 5] (.B (.W 524287 []
  (.B (.W 1048573 [3, 5, 17] .L) (.W 1048575 [3, 5, 17] .L))) (.W 524287 [] (.B (.W 1048573 [3, 5, 17]
  .L) (.W 1048575 [3, 5, 17] .L))))) (.W 524223 [3, 5] (.W 524287 [3] (.B (.W 1048447 [3, 5, 17] .L) (.W
  1048447 [3, 5, 17] .L))))))))))))) (.W 37591 [] (.B (.J 41767 (.W 75181 [3, 5, 7] (.B (.J 93974 (.W
  131071 [3] (.B (.J 332023 (.W 524287 [3] (.B (.J 905397 (.W 1048447 [5] (.B (.J 6635864 (.W 9623167
  [3, 5, 47] (.B (.J 21376481 (.W 41007103 [3, 29, 31] (.B (.J 44654091 (.W 67108351 [3, 47] (.B (.J
  133456296 (.W 266912591 [3, 5, 7, 31] (.W 533825181 [3, 7, 29, 307] (.W 536866807 [7] (.B (.W
  1073733615 [3, 7, 19, 29, 233] (.W 2147467229 [3, 5, 19] (.W 2147483647 [3] (.B (.W 4294967295
  [3, 5, 17, 59, 9241] .L) (.W 4294967295 [3, 5, 17, 59] .L))))) (.W 1073733615 [3, 7, 19, 233] (.W
  2147467229 [3, 5, 19] (.W 2147483647 [3, 7] (.B (.W 4294967295 [3, 5, 17, 59, 9241] .L) (.W 4294967295
  [3, 5, 17, 59] .L)))))))))) (.W 134216703 [3, 5, 349] (.W 268433405 [3, 5, 7] (.W 536866809
  [3, 5, 7, 11, 29, 307] (.W 1073733617 [3, 7, 19, 233] .L))))))) (.W 67108351 [3, 47] (.B (.W 134216703
  [3, 5, 13, 31] (.W 268433405 [3, 5, 7] (.W 536866807 [3, 7, 29, 251] (.B (.W 1073733615
  [3, 7, 19, 23, 29, 233] .L) (.W 1073733615 [3, 7, 19, 23, 233] .L))))) (.W 134216703 [3, 5, 13, 349]
  (.W 268433405 [3, 5, 7] (.W 536866809 [3, 5, 7, 11, 29, 251] .L)))))))) (.W 16777183 [3, 5, 71] (.B (.W
  19502401 [3] (.B (.J 25115673 (.W 50231345 [3, 5, 7, 11, 29, 31] (.W 67108351 [3] (.B (.W 134216703
  [3, 5, 31] (.W 156019207 [7, 13, 19] (.B (.W 312038415 [3, 41] (.W 536866807 [7] (.B (.W 1073733615
  [3, 5, 11, 29, 233] .L) (.W 1073733615 [3, 5, 11, 233] .L)))) (.W 312038415 [3] (.W 536866807 [3, 7]
  (.B (.W 1073733615 [3, 5, 7, 11, 29, 233] .L) (.W 1073733615 [3, 5, 7, 11, 233] .L))))))) (.W 134216703
  [3, 5] (.W 156019207 [3, 7, 13, 19] (.B (.W 312038415 [3, 11, 41] (.W 624076829 [3, 5, 7, 11, 233] .L))
  (.W 312038415 [3, 11] (.W 624076829 [3, 5, 7, 11, 233] .L))))))))) (.W 39004803 [3, 5, 7, 29, 31] (.W
  41007103 [3] (.B (.W 67108351 [3, 47] (.B (.W 134216703 [3, 5, 7, 31] (.W 268433405 [3, 5, 7, 13, 19]
  (.W 536866807 [3, 5, 7, 307] .L))) (.W 134216703 [3, 5, 7, 349] (.W 268433405 [3, 5, 7, 13, 19] (.W
  536866809 [3, 5, 7, 11, 307] .L))))) (.W 67108351 [3, 47] (.B (.W 134216703 [3, 5, 7, 13, 31] (.W
  268433405 [3, 5, 7, 13, 19] .L)) (.W 134216703 [3, 5, 7, 13, 349] (.W 268433405 [3, 5, 7, 13, 19]
  .L))))))))) (.W 19502401 [3] (.B (.W 39004803 [3, 7, 11, 29, 31] (.W 67108351 [3] (.B (.W 134216703
  [3, 5, 31] (.W 156019207 [3, 7, 13] (.B (.W 312038415 [3, 7, 41] .L) (.W 312038415 [3, 7] .L)))) (.W
  134216703 [3, 5] (.W 156019207 [3, 7, 13] (.B (.W 312038415 [3, 7, 11, 41] .L) (.W 312038415 [3, 7, 11]
  .L))))))) (.W 39004803 [3, 7, 29, 31] (.W 41007103 [3] (.B (.W 67108351 [3, 47] (.B (.W 134216703
  [3, 5, 7, 31] (.W 268433405 [3, 5, 7, 13] .L)) (.W 134216703 [3, 5, 7, 349] (.W 268433405 [3, 5, 7, 13]
  .L)))) (.W 67108351 [3, 47] (.B (.W 134216703 [3, 5, 7, 13, 31] .L) (.W 134216703 [3, 5, 7, 13, 349]
  .L))))))))))))) (.W 1048573 [13] (.B (.J 6630821 (.W 9623167 [3, 7, 47] (.B (.J 21324238 (.W 41007103
  [3, 5, 31] (.B (.J 44426722 (.W 67108351 [3, 11, 47] (.B (.J 131445766 (.W 262891531 [3, 5, 7, 13, 31]
  (.W 525783061 [3, 5, 7, 29, 307] (.W 536866807 [3] (.B (.W 1073733615 [3, 5, 7, 19, 29, 233] (.W
  2147467229 [3, 5, 14923] (.W 2147477503 [] (.B (.W 2147483647 [] (.B (.W 4294967295 [3, 5, 9241, 33601]
  .L) (.W 4294967295 [3, 5, 33601] .L))) (.W 2147483647 [] (.B (.W 4294967295 [3, 5, 19, 9241, 33601] .L)
  (.W 4294967295 [3, 5, 19, 33601] .L))))))) (.W 1073733615 [3, 5, 7, 19, 233] (.W 2147467229
  [3, 5, 14923] (.W 2147477503 [7] (.B (.W 2147483647 [] (.B (.W 4294967295 [3, 5, 9241, 33601] .L) (.W
  4294967295 [3, 5, 33601] .L))) (.W 2147483647 [] (.B (.W 4294967295 [3, 5, 19, 9241, 33601] .L) (.W
  4294967295 [3, 5, 19, 33601] .L)))))))))))) (.W 134216703 [3, 5, 11, 349] (.W 268433405 [3, 5, 7, 13]
  (.W 536866809 [3, 5, 11, 29, 307] (.W 1073733617 [3, 5, 7, 19, 233] .L))))))) (.W 67108351 [3, 11, 47]
  (.B (.W 134216703 [3, 5, 11, 13, 31] (.W 268433405 [3, 5, 7, 13] (.W 536866807 [3, 5, 29, 251] (.B (.W
  1073733615 [3, 5, 7, 19, 23, 29, 233] .L) (.W 1073733615 [3, 5, 7, 19, 23, 233] .L))))) (.W 134216703
  [3, 5, 11, 13, 349] (.W 268433405 [3, 5, 7, 13] (.W 536866809 [3, 5, 11, 29, 251] .L)))))))) (.W
  19246335 [3, 5, 71, 1531] (.W 19502401 [3] (.B (.W 39004803 [3, 5, 7, 11, 31] (.W 67108351 [11] (.B (.W
  134216703 [3, 31] (.W 156019207 [7, 13] (.B (.W 312038415 [3, 7, 41] .L) (.W 312038415 [3, 7] .L))))
  (.W 134216703 [3] (.W 156019207 [3, 7, 13] (.B (.W 312038415 [3, 7, 11, 41] .L) (.W 312038415
  [3, 7, 11] .L))))))) (.W 39004803 [3, 5, 7, 31] (.W 41007103 [3] (.B (.W 67108351 [3, 11, 47] (.B (.W
  134216703 [3, 5, 7, 11, 31] (.W 268433405 [3, 5, 7, 13] .L)) (.W 134216703 [3, 5, 7, 11, 349] (.W
  268433405 [3, 5, 7, 13] .L)))) (.W 67108351 [3, 11, 47] (.B (.W 134216703 [3, 7, 11, 13, 31] .L) (.W
  134216703 [3, 7, 11, 13, 349] .L)))))))))))) (.W 2097147 [3] (.W 2405791 [3, 7] (.B (.W 2562943 [] (.B
  (.J 3348429 (.W 4194271 [7] (.B (.J 16603834 (.W 16777183 [3, 1531] (.B (.J 1606956859 (.W 2147483647
  [3, 17, 31, 14923] (.B (.J 6384352537 (.W 12768705073 [3, 5, 7, 17, 43] (.W 19708239871 [3, 5, 7, 59]
  (.B (.W 39416479743 [3, 5, 7, 31, 4937, 33773] (.W 78832959485 [3, 5, 7, 11, 17, 89, 1171] (.W
  137437872127 [3, 5, 887] (.B (.W 261455619871 [3, 5, 47, 223, 619, 88093] .L) (.W 261455619871
  [3, 5, 47, 223, 619, 88093] .L))))) (.W 37491846943 [3, 5, 7, 31, 33773] (.B (.W 74983693887
  [3, 5, 7, 11, 17] (.W 137437872127 [3, 887] (.B (.W 274875744255 [3, 5, 11, 23, 47, 223] .L) (.W
  274875744255 [3, 5, 23, 47, 223, 347] .L)))) (.W 39411668161 [] (.B (.W 78823336321
  [3, 5, 7, 17, 89, 1171] (.B (.W 137437872127 [3, 887] (.B (.W 261455619871 [3, 5, 71, 223, 88093] .L)
  (.W 261455619871 [3, 5, 71, 223, 88093] .L))) (.W 137437872127 [3, 887] .L))) (.W 78823336323
  [3, 5, 7, 11, 17, 89, 1171] (.W 137437872127 [3, 5, 17, 887] .L)))))))))) (.W 4085219953 [3, 113, 151]
  (.B (.W 8170439907 [3, 5, 19, 419, 33601] (.W 16340879813 [3, 5, 7] (.W 19708239871 [3, 7] (.B (.W
  32681759623 [5] (.B (.W 65363519247 [3, 5, 31, 4937, 33773] .L) (.W 65363519247 [3, 5, 31, 4937, 33773]
  .L))) (.W 32681759623 [5] (.B (.W 39411668161 [3, 31, 33773] (.B (.W 78823336321 [3, 5] .L) (.W
  78823336323 [3, 5, 11] .L))) (.W 39411668161 [3, 31, 33773] (.B (.W 78823336321 [3] .L) (.W 78823336323
  [3, 5, 11] .L))))))))) (.W 8170439907 [3, 5, 19, 419, 33601] (.W 16340879813 [3, 5, 7, 17, 43] (.W
  19708239871 [3, 5, 7, 59] (.B (.W 39416479743 [3, 5, 7, 31, 4937, 33773] .L) (.W 37491846943
  [3, 5, 7, 31, 33773] .L)))))))))) (.W 33554167 [3, 5, 37, 2357] (.B (.W 67108335 [3, 11, 17, 31, 47]
  (.W 134216669 [3, 5, 11, 13] (.W 268433337 [3, 5, 7] (.W 536866673 [3, 5, 7, 13, 17] (.W 1073733343
  [3, 19, 233] .L))))) (.W 67108335 [3, 11, 31, 47] (.W 134216669 [3, 5, 11, 13] (.W 268433337
  [3, 5, 7, 229] (.W 536866673 [3, 5, 7, 13, 17] .L))))))))) (.W 4811581 [3, 5] (.B (.J 11011323 (.W
  16777183 [3, 5, 71, 1531] (.B (.J 32040143 (.W 64080285 [3, 5, 31, 47, 61] (.W 67108351 [11] (.B (.W
  134216703 [3, 5, 11, 31] (.W 153970591 [7, 19] (.B (.W 307941183 [3, 5, 7, 23] (.W 536866807 [3, 5, 13]
  (.B (.W 1073733615 [3, 5, 19, 29, 233] (.W 1231764727 [3] (.B (.W 2147483647 [3, 5, 17, 14923] (.B (.W
  4294967295 [3, 5, 7, 151, 9241, 33601] .L) (.W 4294967295 [3, 5, 7, 151, 33601] .L))) (.W 2147483647
  [3, 5, 17, 14923] (.B (.W 4294967295 [3, 5, 151, 9241, 33601] .L) (.W 4294967295 [3, 5, 151, 33601]
  .L)))))) (.W 1073733615 [3, 5, 19, 233] (.W 1231764727 [3] (.B (.W 2147483647 [3, 5, 7, 17, 14923] .L)
  (.W 2147483647 [3, 5, 7, 17, 14923] .L))))))) (.W 307941183 [3, 5, 7] (.W 536866807 [3, 5, 13] (.B (.W
  1073733615 [3, 5, 19, 29, 233] (.W 2147467229 [3, 5, 14923] .L)) (.W 1073733615 [3, 5, 19, 29, 233] (.W
  2147467229 [3, 5, 14923] .L)))))))) (.W 134216703 [3, 5, 11, 349] (.W 153970591 [3, 7, 19] (.B (.W
  307941183 [3, 5, 7, 11, 23] (.W 615882365 [3, 5, 13, 233] (.W 1231764727 [3, 19, 8941] .L))) (.W
  307941183 [3, 5, 7, 11] (.W 615882365 [3, 5, 13, 233] .L))))))))) (.W 33554367 [3, 5, 2357] (.W
  67108351 [3, 11, 31, 47, 61] (.B (.W 134216703 [3, 5, 11, 31] (.W 153970591 [3, 7] (.B (.W 307941183
  [3, 5, 7, 23] .L) (.W 307941183 [3, 5, 7] .L)))) (.W 134216703 [3, 5, 11, 349] (.W 153970591 [3, 7] (.B
  (.W 307941183 [3, 5, 7, 11, 23] .L) (.W 307941183 [3, 5, 7, 11] .L)))))))))) (.W 9623163 [3, 5, 7, 47]
  (.W 16777183 [3, 5, 71, 1531] (.B (.W 33554367 [3, 5, 37, 2357] (.W 67108351 [3, 11, 31, 47] (.B (.W
  134216703 [3, 5, 11, 13, 31] .L) (.W 134216703 [3, 5, 11, 13, 349] .L)))) (.W 33554367 [3, 5, 37, 2357]
  (.W 67108351 [3, 11, 31, 47] .L)))))))))) (.W 4194271 [7] (.B (.W 4811581 [3, 5] (.B (.W 9623161
  [3, 7, 47] (.B (.W 16777183 [3, 5, 1531] (.B (.W 19502401 [3, 1571] (.B (.J 36003466 (.W 72006931
  [3, 11] (.W 76985287 [] (.B (.W 153970575 [3, 7, 19, 43, 229] (.W 156019207 [] (.B (.W 312038415
  [3, 7, 41] (.W 624076829 [3, 5, 7, 233] (.W 1248153657 [3, 5, 19] (.W 2147483647 [3, 17, 31] .L)))) (.W
  312038415 [3, 7] (.W 624076829 [3, 5, 7, 233] (.W 1248153657 [3, 7, 19] .L)))))) (.W 153970575
  [3, 7, 19, 229] (.W 156019207 [3] (.B (.W 312038415 [3, 7, 41] (.W 624076829 [3, 5, 7, 233] (.W
  1231764607 [3, 19] .L))) (.W 312038415 [3, 7] (.W 624076829 [3, 5, 7, 233] .L))))))))) (.W 33554167
  [3, 5] (.B (.W 41007103 [3, 5, 31] (.B (.W 76985287 [3, 11, 17, 47] (.B (.J 84226348 (.W 168452695
  [3, 7, 11, 19, 43] (.W 336905389 [3, 5, 7, 307] (.W 673810777 [3, 5, 233] (.W 1073733343 [3, 19] (.B
  (.W 2147466687 [3, 5, 14923] .L) (.W 2147466687 [3, 5, 14923] .L))))))) (.W 153970575 [3, 5, 7, 11, 19]
  (.W 307941149 [3, 5, 7] (.W 615882297 [3, 5, 7, 233, 307] (.W 1073733343 [3, 19] .L)))))) (.W 76985287
  [3, 11, 17, 47] (.B (.W 153970575 [3, 7, 11, 13, 19, 43] (.W 307941149 [3, 5, 7] (.W 615882297
  [3, 5, 233, 251] .L))) (.W 153970575 [3, 7, 11, 13, 19] (.W 307941149 [3, 5, 7] (.W 615882297
  [3, 5, 7, 233, 251] .L))))))) (.W 41007103 [3, 5, 31] (.B (.W 76985287 [3, 11, 47] (.B (.W 153970575
  [3, 5, 7, 11, 19, 43, 229] (.W 307941149 [3, 5, 7] (.W 615882297 [3, 5, 7, 233, 307] .L))) (.W
  153970575 [3, 5, 7, 11, 19, 229] (.W 307941149 [3, 5, 7] (.W 615882297 [3, 5, 7, 233, 307] .L))))) (.W
  76985287 [3, 11, 47] (.B (.W 153970575 [3, 7, 11, 13, 19, 43, 229] (.W 307941149 [3, 5, 7] .L)) (.W
  153970575 [3, 7, 11, 13, 19, 229] (.W 307941149 [3, 5, 7] .L)))))))))) (.W 19502401 [3, 1571] (.B (.W
  33554167 [3] (.B (.W 67108335 [3, 11, 17, 31] (.W 76985287 [3, 5] (.B (.W 153970575 [3, 7, 43] (.W
  156019207 [] (.B (.W 312038415 [3, 5, 7, 41] (.W 624076829 [3, 5, 233] .L)) (.W 312038415 [3, 5, 7] (.W
  624076829 [3, 5, 233] .L))))) (.W 153970575 [3, 7] (.W 156019207 [3] (.B (.W 312038415 [3, 5, 7, 41]
  (.W 624076829 [3, 233] .L)) (.W 312038415 [3, 5, 7] .L))))))) (.W 67108335 [3, 11, 31] (.W 76985287
  [3, 5] (.B (.W 153970575 [3, 7, 43, 229] (.W 156019207 [] (.B (.W 312038415 [3, 7, 41] .L) (.W
  312038415 [3, 7] .L)))) (.W 153970575 [3, 7, 229] (.W 156019207 [3] (.B (.W 312038415 [3, 7, 41] .L)
  (.W 312038415 [3, 7] .L))))))))) (.W 33554167 [3, 5] (.B (.W 41007103 [3, 31] (.B (.W 76985287
  [3, 5, 11, 17, 47] (.B (.W 153970575 [3, 5, 7, 11, 43] (.W 307941149 [3, 5, 7] .L)) (.W 153970575
  [3, 5, 7, 11] (.W 307941149 [3, 5, 7] .L)))) (.W 76985287 [3, 5, 11, 17, 47] (.B (.W 153970575
  [3, 7, 11, 13, 43] (.W 307941149 [3, 5, 7] .L)) (.W 153970575 [3, 7, 11, 13] (.W 307941149 [3, 5, 7]
  .L)))))) (.W 41007103 [3, 31] (.B (.W 76985287 [3, 5, 11, 47] (.B (.W 153970575 [3, 5, 7, 11, 43, 229]
  (.W 307941149 [3, 5, 7] .L)) (.W 153970575 [3, 5, 7, 11, 229] (.W 307941149 [3, 5, 7] .L)))) (.W
  76985287 [3, 5, 11, 47] (.B (.W 153970575 [3, 7, 11, 13, 43, 229] .L) (.W 153970575 [3, 7, 11, 13, 229]
  .L))))))))))) (.W 16777183 [3, 5, 1531] (.B (.W 19502401 [3] (.B (.W 33554167 [3] (.B (.W 67108335
  [5, 11, 17, 31, 61] (.W 134216669 [3] (.W 153970591 [7, 19] (.B (.W 156019207 [] (.B (.W 312038415
  [3, 5, 7, 23, 41] .L) (.W 312038415 [3, 5, 7, 23] .L))) (.W 156019207 [] (.B (.W 312038415
  [3, 5, 7, 41] .L) (.W 312038415 [3, 5, 7] .L))))))) (.W 67108335 [3, 5, 11, 31, 61] (.W 134216669 [3]
  .L)))) (.W 33554167 [3, 5] (.B (.W 41007103 [3, 5, 31, 61] (.B (.W 82014207 [3, 5, 11, 17, 47] (.W
  153970591 [3, 7, 11, 19] .L)) (.W 82014207 [3, 11, 13, 17, 47] (.W 153970591 [3, 7, 11, 19] .L)))) (.W
  41007103 [3, 5, 31, 61] (.B (.W 82014207 [3, 5, 11, 47] (.W 153970591 [3, 7, 11, 19, 229] .L)) (.W
  82014207 [3, 11, 13, 47] (.W 153970591 [3, 7, 11, 19, 229] .L)))))))) (.W 19502401 [3] (.B (.W 33554167
  [3] (.B (.W 67108335 [3, 11, 17, 31, 61] (.W 134216669 [3, 5] .L)) (.W 67108335 [3, 11, 31, 61] (.W
  134216669 [3, 5] .L)))) (.W 33554167 [3, 5] (.B (.W 41007103 [3, 31, 61] (.B (.W 82014207
  [3, 5, 11, 17, 47] (.W 153970591 [3, 7, 11] .L)) (.W 82014207 [3, 5, 11, 13, 17, 47] (.W 153970591
  [3, 7, 11] .L)))) (.W 41007103 [3, 31, 61] (.B (.W 82014207 [3, 5, 11, 47] (.W 153970591
  [3, 7, 11, 229] .L)) (.W 82014207 [3, 5, 11, 13, 47] .L))))))))))) (.W 9623163 [3, 7, 47] (.W 16777183
  [3, 5, 1531] (.B (.W 19502401 [3, 37] (.B (.W 33554167 [3] (.B (.W 67108335 [3, 5, 11, 17, 31] .L) (.W
  67108335 [3, 5, 11, 31] .L))) (.W 33554167 [3, 5] (.B (.W 41007103 [3, 5, 31] (.B (.W 82014207
  [3, 5, 11, 13, 17, 47] .L) (.W 82014207 [3, 11, 13, 17, 47] .L))) (.W 41007103 [3, 5, 31] (.B (.W
  82014207 [3, 5, 11, 13, 47] .L) (.W 82014207 [3, 11, 13, 47] .L))))))) (.W 19502401 [3, 37] (.B (.W
  33554167 [3] (.B (.W 67108335 [3, 11, 17, 31] .L) (.W 67108335 [3, 11, 31] .L))) (.W 33554167 [3, 5]
  (.B (.W 41007103 [3, 31] (.B (.W 82014207 [3, 5, 11, 13, 17, 47] .L) (.W 82014207
  [3, 5, 11, 13, 17, 47] .L))) (.W 41007103 [3, 31] .L)))))))))) (.W 4811581 [3, 5] (.B (.W 9623161
  [3, 7, 47] (.B (.W 16777183 [3, 5, 71, 1531] (.B (.W 19502401 [3, 1571] (.B (.W 39004803 [3, 5, 11, 31]
  (.W 67108351 [11] .L)) (.W 39004803 [3, 5, 31] (.W 41007103 [3] (.B (.W 67108351 [3, 11, 47] .L) (.W
  67108351 [3, 11, 47] .L)))))) (.W 19502401 [3, 1571] (.B (.W 39004803 [3, 11, 31] (.W 67108351 [11]
  .L)) (.W 39004803 [3, 5, 31] (.W 41007103 [3] (.B (.W 67108351 [3, 11, 47] .L) (.W 67108351 [3, 11, 47]
  .L)))))))) (.W 16777183 [3, 5, 71, 1531] (.B (.W 19502401 [3] (.B (.W 39004803 [3, 5, 11, 31, 61] (.W
  67108351 [11] .L)) (.W 39004803 [3, 5, 31, 61] (.W 41007103 [3] (.B (.W 67108351 [3, 11, 47] .L) (.W
  67108351 [3, 11, 47] .L)))))) (.W 19502401 [3] (.B (.W 39004803 [3, 11, 31, 61] .L) (.W 39004803
  [3, 5, 31, 61] .L))))))) (.W 9623163 [3, 7, 47] (.W 16777183 [3, 5, 71, 1531] (.B (.W 19502401 [3, 37]
  (.B (.W 39004803 [3, 5, 11, 31] .L) (.W 39004803 [3, 5, 31] .L))) (.W 19502401 [3, 37] (.B (.W 39004803
  [3, 11, 31] .L) (.W 39004803 [3, 5, 31] .L)))))))))))) (.W 2562943 [] (.B (.W 4194271 [7] (.B (.W
  8388543 [3, 5, 7] (.W 9623167 [3, 47] (.B (.W 16777183 [3, 5, 1531] (.B (.W 33554167 [3, 5, 1259, 2357]
  (.B (.W 67108335 [3, 5, 11, 17, 31, 47] .L) (.W 67108335 [3, 5, 11, 31, 47] .L))) (.W 33554167
  [3, 5, 1259, 2357] (.B (.W 67108335 [3, 11, 17, 31, 47] .L) (.W 67108335 [3, 11, 31, 47] .L))))) (.W
  16777183 [3, 5, 1531] (.B (.W 33554167 [3, 5, 2357] (.B (.W 67108335 [3, 5, 7, 11, 17, 31, 47] .L) (.W
  67108335 [3, 5, 7, 11, 31, 47] .L))) (.W 33554167 [3, 5, 2357] (.B (.W 67108335 [3, 7, 11, 17, 31, 47]
  .L) (.W 67108335 [3, 7, 11, 31, 47] .L)))))))) (.W 8388543 [3, 5, 7] (.W 9623167 [3, 47] (.B (.W
  16777183 [3, 5, 71, 1531] (.B (.W 33554367 [3, 5, 1259, 2357] .L) (.W 33554367 [3, 5, 1259, 2357] .L)))
  (.W 16777183 [3, 5, 71, 1531] (.B (.W 33554367 [3, 5, 2357] .L) (.W 33554367 [3, 5, 2357] .L))))))))
  (.W 4194271 [7] (.B (.W 8388543 [3, 5, 7] (.W 9623167 [3, 47] (.B (.W 16777183 [3, 5, 1531] (.B (.W
  19502401 [3, 1259] (.B (.W 33554167 [3] .L) (.W 33554167 [3, 5] .L))) (.W 19502401 [3, 1259] (.B (.W
  33554167 [3] .L) (.W 33554167 [3, 5] .L))))) (.W 16777183 [3, 5, 1531] (.B (.W 19502401 [3] (.B (.W
  33554167 [3] .L) (.W 33554167 [3, 5] .L))) (.W 19502401 [3] (.B (.W 33554167 [3] .L) (.W 33554167
  [3, 5] .L)))))))) (.W 8388543 [3, 5, 7] (.W 9623167 [3, 47] (.B (.W 16777183 [3, 5, 71, 1531] (.B (.W
  19502401 [3, 1259] .L) (.W 19502401 [3, 1259] .L))) (.W 16777183 [3, 5, 71, 1531] .L))))))))))))))))
  (.W 1048447 [5, 7] (.B (.W 2096893 [3, 13] (.B (.W 2405791 [3, 7] (.B (.W 2562943 [] (.B (.W 4194271
  [5, 7] (.B (.W 4811581 [3] (.B (.W 9623161 [3, 5, 7, 47] (.B (.W 19246323 [3, 5, 7, 1571] (.W 33554167
  [3, 2357] (.B (.W 67108335 [3, 5, 17, 31, 47] (.W 76985287 [3] (.B (.W 153970575 [3, 5, 7, 43] .L) (.W
  153970575 [3, 5, 7] .L)))) (.W 67108335 [3, 5, 31, 47] (.W 76985287 [3] .L))))) (.W 19246323 [3, 5, 7]
  (.W 33554167 [3, 2357] (.B (.W 67108335 [3, 5, 17, 31, 47, 61] .L) (.W 67108335 [3, 5, 31, 47, 61]
  .L)))))) (.W 9623163 [3, 5, 7, 47] (.W 19246325 [3, 5, 7] (.W 33554167 [3, 37, 2357] .L))))) (.W
  4811581 [3] (.B (.W 9623161 [3, 5, 47] (.B (.W 19246323 [3, 5, 7, 71, 1571] (.W 38492645 [3, 31, 2357]
  .L)) (.W 19246323 [3, 5, 7, 71] (.W 38492645 [3, 31, 2357] .L)))) (.W 9623163 [3, 5, 47] (.W 19246325
  [3, 5, 7, 71] (.W 38492649 [3, 31, 37, 2357] .L))))))) (.W 4194271 [5, 7] (.B (.W 4811581 [3] (.B (.W
  9623161 [3, 7, 47] (.B (.W 19246323 [3, 5, 7, 1571] (.W 19502401 [] (.B (.W 33554167 [3] .L) (.W
  33554167 [3] .L)))) (.W 19246323 [3, 5, 7] (.W 19502401 [3] (.B (.W 33554167 [3] .L) (.W 33554167 [3]
  .L)))))) (.W 9623163 [3, 7, 47] (.W 19246325 [3, 5, 7] .L)))) (.W 4811581 [3] (.B (.W 9623161 [3, 47]
  (.B (.W 19246323 [3, 5, 7, 71, 1571] .L) (.W 19246323 [3, 5, 7, 71] .L))) (.W 9623163 [3, 47] (.W
  19246325 [3, 5, 7, 71] .L)))))))) (.W 2562943 [] (.B (.W 4194271 [5, 7] (.B (.W 8388543 [3, 5, 7] (.W
  9623167 [47] (.B (.W 19246335 [3, 5, 7, 1259] .L) (.W 19246335 [3, 5, 7] .L)))) (.W 8388543 [3, 5] (.W
  9623167 [3, 47] (.B (.W 19246335 [3, 5, 7, 71, 1259] .L) (.W 19246335 [3, 5, 7, 71] .L)))))) (.W
  4194271 [5, 7] (.B (.W 8388543 [3, 7] (.W 9623167 [47] (.B (.W 19246335 [3, 5, 7, 1259] .L) (.W
  19246335 [3, 5, 7] .L)))) (.W 8388543 [3] (.W 9623167 [3, 47] (.B (.W 19246335 [3, 5, 7, 71, 1259] .L)
  (.W 19246335 [3, 5, 7, 71] .L)))))))))) (.W 2405791 [3, 7] (.B (.W 2562943 [] (.B (.W 4194271 [3, 7]
  (.B (.W 4811581 [3] (.B (.W 9623161 [3, 5, 7, 47] (.B (.W 19246323 [3, 5, 1571] (.W 33554167
  [3, 29, 2357] .L)) (.W 19246323 [3, 5] (.W 33554167 [3, 29, 2357] .L)))) (.W 9623163 [3, 5, 7, 47] (.W
  19246325 [3, 5] .L)))) (.W 4811581 [3] (.B (.W 9623161 [3, 5, 47] (.B (.W 19246323 [3, 5, 71, 1571] .L)
  (.W 19246323 [3, 5, 71] .L))) (.W 9623163 [3, 5, 47] (.W 19246325 [3, 5, 71] .L)))))) (.W 4194271
  [3, 7] (.B (.W 4811581 [3] (.B (.W 9623161 [3, 5, 7, 47] (.B (.W 19246323 [3, 5, 1571] .L) (.W 19246323
  [3, 5] .L))) (.W 9623163 [3, 5, 7, 47] (.W 19246325 [3, 5] .L)))) (.W 4811581 [3] (.B (.W 9623161
  [3, 5, 47] (.B (.W 19246323 [3, 5, 71, 1571] .L) (.W 19246323 [3, 5, 71] .L))) (.W 9623163 [3, 5, 47]
  (.W 19246325 [3, 5, 71] .L)))))))) (.W 2562943 [] (.B (.W 4194271 [3, 7] (.B (.W 8388543 [3, 5, 7] (.W
  9623167 [47] (.B (.W 19246335 [3, 5, 1259] .L) (.W 19246335 [3, 5] .L)))) (.W 8388543 [3, 5] (.W
  9623167 [3, 47] .L)))) (.W 4194271 [3, 7] (.B (.W 8388543 [3, 5, 7] (.W 9623167 [47] .L)) (.W 8388543
  [3, 5] .L))))))))) (.W 2096895 [3, 13] (.W 2405791 [3, 7] (.B (.W 2562943 [] (.B (.W 4194271 [7] (.B
  (.W 4811581 [3] (.B (.W 9623161 [3, 5, 7, 47] .L) (.W 9623163 [3, 5, 7, 47] .L))) (.W 4811581 [3] (.B
  (.W 9623161 [3, 5, 7, 47] .L) (.W 9623163 [3, 5, 7, 47] .L))))) (.W 4194271 [7] (.B (.W 4811581 [3] (.B
  (.W 9623161 [3, 7, 47] .L) (.W 9623163 [3, 7, 47] .L))) (.W 4811581 [3] (.B (.W 9623161 [3, 7, 47] .L)
  (.W 9623163 [3, 7, 47] .L))))))) (.W 2562943 [] (.B (.W 4194271 [7] (.B (.W 8388543 [3, 5, 7] .L) (.W
  8388543 [3, 5, 7] .L))) (.W 4194271 [7] (.B (.W 8388543 [3, 7] .L) (.W 8388543 [3, 7] .L)))))))))))))
  (.W 160183 [53] (.B (.J 227354 (.W 262111 [23] (.B (.J 1714528 (.W 2405791 [3, 7, 13] (.B (.J 5967034
  (.W 11934067 [3, 47, 137] (.W 23868133 [3, 5, 37, 79] (.W 47736265 [3, 31, 761] (.W 95472529
  [3, 5, 13, 47] .L))))) (.W 4811583 [3, 7] (.W 9623165 [3, 5, 47, 137] (.W 9623167 [] (.B (.W 19246335
  [3, 5, 1259] (.W 38492669 [3, 31, 79, 761] .L)) (.W 19246335 [3, 5] (.W 38492669 [3, 31, 79, 761]
  .L))))))))) (.W 524223 [3, 5] (.W 524287 [3] (.B (.W 1048447 [3, 5, 7] (.B (.W 1048573 [] (.B (.J
  1713493 (.W 2096893 [3] (.B (.J 9371445 (.W 9623167 [] (.B (.J 358263133 (.W 716526265 [3, 5, 7, 233]
  (.W 1433052529 [3, 5, 7, 19] (.W 2147477503 [3, 7] (.B (.W 2147483647 [] (.B (.W 4294967295
  [3, 5, 47, 9241, 21407] (.W 5248876543 [3, 7] (.B (.W 8169495127 [] (.B (.W 16338990255 [3, 5, 7, 29]
  .L) (.W 16338990255 [3, 5, 7] .L))) (.W 8169495127 [] (.B (.W 16338990255 [3, 7, 29] .L) (.W
  16338990255 [3, 7, 31] .L)))))) (.W 4294967295 [3, 5, 47, 21407] (.W 5248876543 [3, 7] (.B (.W
  8169495127 [] .L) (.W 8169495127 [] .L)))))) (.W 2147483647 [] (.B (.W 4294967295
  [3, 5, 19, 47, 9241, 21407] (.W 5248876543 [3, 7] (.B (.W 8169495127 [] (.B .L (.W 16338990255
  [3, 5, 7] .L))) (.W 8169495127 [] .L)))) (.W 4294967295 [3, 5, 19, 47, 21407] (.W 5248876543 [3, 7] (.B
  (.W 8169495127 [] .L) (.W 8169495127 [] .L))))))))))) (.W 19246335 [3, 5, 7] (.W 38492669
  [3, 5, 31, 79] (.W 76985337 [3, 5, 7, 47] (.W 153970673 [3, 5, 7, 13] .L))))))) (.W 2405791 [5, 7] (.B
  (.J 5954527 (.W 11909053 [3, 5, 7, 47] (.W 23818105 [3, 5, 37, 79] (.W 47636209 [3, 5, 29, 31] (.W
  95272417 [3, 5, 13, 47] (.W 156018241 [3, 5, 7, 13] .L)))))) (.W 4811583 [3, 7] (.W 9623165
  [3, 5, 7, 47] (.W 9623167 [] (.B (.W 19246335 [3, 5, 1259] (.W 38492669 [3, 5, 29, 31, 79] .L)) (.W
  19246335 [3, 5] (.W 38492669 [3, 5, 29, 31, 79] .L))))))))))) (.W 1281463 [3] (.B (.J 1321140 (.W
  2096893 [3] (.B (.J 3571098 (.W 7142195 [3, 5, 7] (.W 9623167 [3, 47] (.B (.W 16777183 [5, 7] (.B (.W
  33554367 [3, 5, 1259] (.W 67108733 [3, 5, 31, 47] (.W 134217465 [3, 5, 19] (.W 164027263 [3, 7] .L))))
  (.W 33554367 [3, 1259] (.W 67108733 [3, 5, 31, 47] (.W 134217465 [3, 5] .L))))) (.W 16777183 [5, 7] (.B
  (.W 33554367 [3, 5] (.W 67108733 [3, 5, 7, 31, 47] (.W 134217465 [3, 7, 19] .L))) (.W 33554367 [3] (.W
  67108733 [3, 5, 7, 31, 47] .L)))))))) (.W 2405791 [3, 7] (.B (.J 2930332 (.W 4811581 [3, 5, 7] (.B (.J
  7494769 (.W 9623161 [3, 5, 47] (.B (.J 33886303 (.W 67772605 [3, 5, 47] (.W 76985287 [] (.B (.W
  153970575 [3, 5, 7, 43] (.W 164027263 [] (.B (.W 328054527 [3, 5, 7] (.W 656109053 [3, 5, 7, 233] (.W
  1312218105 [3, 5, 7, 19] (.W 2147483647 [3, 5, 19] .L)))) (.W 328054527 [3, 5, 7] (.W 656109053
  [3, 5, 7, 233] (.W 1312218105 [3, 5, 7, 19] .L)))))) (.W 153970575 [3, 5, 7] (.W 164027263 [3] (.B (.W
  328054527 [3, 5, 7] (.W 656109053 [3, 7, 233] (.W 1231764607 [3, 5, 7, 19] .L))) (.W 328054527
  [3, 5, 7] (.W 656109053 [3, 7, 233] .L))))))))) (.W 16777183 [3, 5, 7] (.B (.W 33554367 [3, 5, 29] (.W
  67108733 [3, 5, 31, 47, 61] (.W 134217465 [3, 5, 19] (.W 153970591 [7] (.B (.W 164027263 [] (.B (.W
  328054527 [3, 5, 23] .L) (.W 328054527 [3, 5, 23] .L))) (.W 164027263 [] (.B (.W 328054527 [3, 5] .L)
  (.W 328054527 [3, 5] .L)))))))) (.W 33554367 [3, 29] (.W 67108733 [3, 5, 31, 47, 61] (.W 134217465
  [3, 5] .L)))))))) (.W 9623163 [3, 5, 47] (.W 16777183 [3, 5, 7] (.B (.W 33554367 [3, 5, 29, 37] (.W
  67108733 [3, 5, 31, 47] .L)) (.W 33554367 [3, 29, 37] (.W 67108733 [3, 5, 31, 47] .L)))))))) (.W
  4811583 [3, 5, 7] (.W 9623165 [3, 5, 47] (.W 9623167 [] (.B (.W 16777183 [3, 5, 7] (.B (.W 33554367
  [3, 5, 29, 1259] .L) (.W 33554367 [3, 29, 1259] .L))) (.W 16777183 [3, 5, 7] (.B (.W 33554367
  [3, 5, 29] .L) (.W 33554367 [3, 29] .L)))))))))))) (.W 2096893 [3] (.B (.W 2405791 [3, 7] (.B (.W
  4811581 [3, 5, 7] (.B (.W 9623161 [3, 5, 47] (.B (.W 16777183 [3, 5, 7] (.B (.W 33554367
  [3, 5, 79, 1571] (.W 67108733 [3, 5, 31, 47] .L)) (.W 33554367 [3, 79, 1571] (.W 67108733
  [3, 5, 31, 47] .L)))) (.W 16777183 [3, 5, 7] (.B (.W 33554367 [3, 5, 79] (.W 67108733
  [3, 5, 31, 47, 61] .L)) (.W 33554367 [3, 79] (.W 67108733 [3, 5, 31, 47, 61] .L)))))) (.W 9623163
  [3, 5, 47] (.W 16777183 [3, 5, 7] (.B (.W 33554367 [3, 5, 37, 79] .L) (.W 33554367 [3, 37, 79] .L))))))
  (.W 4811583 [3, 5, 7] (.W 9623165 [3, 5, 47] (.W 9623167 [] (.B (.W 16777183 [3, 5, 7] .L) (.W 16777183
  [3, 5, 7] .L))))))) (.W 2405791 [3, 7] (.B (.W 4811581 [3, 5, 7] (.B (.W 9623161 [3, 5, 47] (.B (.W
  16777183 [3, 5] (.B (.W 33554367 [3, 5, 29, 79, 1571] .L) (.W 33554367 [3, 29, 79, 1571] .L))) (.W
  16777183 [3, 5] (.B (.W 33554367 [3, 5, 29, 79] .L) (.W 33554367 [3, 29, 79] .L))))) (.W 9623163
  [3, 5, 47] (.W 16777183 [3, 5] .L)))) (.W 4811583 [3, 5, 7] (.W 9623165 [3, 5, 47] (.W 9623167 [] (.B
  (.W 16777183 [3, 5] .L) (.W 16777183 [3, 5] .L))))))))))))) (.W 1048573 [] (.B (.W 1281463 [3] (.B (.J
  1320940 (.W 2405791 [3, 5, 7] (.B (.J 2929348 (.W 4811581 [3, 7] (.B (.J 7488336 (.W 9623161 [3, 7, 47]
  (.B (.J 33755207 (.W 67510413 [3, 5, 11, 47] (.W 76985287 [] (.B (.W 153970575 [3, 7, 11, 13, 43] (.W
  164027263 [] (.B (.W 328054527 [3, 5, 7] (.W 656109053 [3, 5, 233] (.W 1312218105 [3, 7, 19] (.W
  2147477503 [3, 14923] .L)))) (.W 328054527 [3, 5, 7] (.W 656109053 [3, 5, 233] (.W 1312218105
  [3, 5, 7, 19] .L)))))) (.W 153970575 [3, 7, 11, 13] (.W 164027263 [3] (.B (.W 328054527 [3, 5, 7] (.W
  656109053 [3, 5, 233] (.W 1231764607 [3, 7, 19] .L))) (.W 328054527 [3, 5, 7] (.W 656109053 [3, 5, 233]
  .L))))))))) (.W 19246323 [3, 5, 7, 1531] (.W 38492645 [3, 5, 31] (.W 76985289 [3, 5, 11, 47, 61] (.W
  153970577 [3, 7, 11, 13] .L))))))) (.W 9623163 [3, 7, 47] (.W 19246325 [3, 5, 7, 1531] (.W 38492649
  [3, 5, 31, 37] (.W 76985297 [3, 5, 11, 47] .L))))))) (.W 4811583 [3, 5, 7] (.W 9623165 [3, 7, 47] (.W
  9623167 [] (.B (.W 19246335 [3, 5, 7, 1259, 1531] (.W 38492669 [3, 5, 31] .L)) (.W 19246335
  [3, 5, 7, 1531] (.W 38492669 [3, 5, 31] .L))))))))) (.W 2405791 [3, 5, 7] (.B (.W 4811581 [3, 7] (.B
  (.W 9623161 [3, 5, 7, 47] (.B (.W 19246323 [3, 5, 1531, 1571] (.W 38492645 [3, 5, 31, 79] .L)) (.W
  19246323 [3, 5, 1531] .L))) (.W 9623163 [3, 5, 7, 47] (.W 19246325 [3, 5, 1531] .L)))) (.W 4811583
  [3, 7] (.W 9623165 [3, 5, 7, 47] (.W 9623167 [] (.B (.W 19246335 [3, 5, 1259, 1531] .L) (.W 19246335
  [3, 5, 1531] .L))))))))) (.W 1281463 [3] (.B (.W 2405791 [3, 7] (.B (.W 4811581 [3, 5, 7] (.B (.W
  9623161 [3, 7, 47] (.B (.W 16777183 [3, 5, 7, 1531] .L) (.W 16777183 [3, 5, 7, 1531] .L))) (.W 9623163
  [3, 7, 47] (.W 16777183 [3, 5, 7, 1531] .L)))) (.W 4811583 [3, 5, 7] (.W 9623165 [3, 7, 47] .L)))) (.W
  2405791 [3, 7] (.B (.W 4811581 [3, 5, 7] (.B (.W 9623161 [3, 5, 7, 47] .L) (.W 9623163 [3, 5, 7, 47]
  .L))) (.W 4811583 [3, 5, 7] (.W 9623165 [3, 5, 7, 47] .L)))))))))) (.W 1048447 [3, 5, 7] (.B (.W
  1281463 [3] (.B (.W 2096893 [3] (.B (.W 2405791 [7] (.B (.W 4811581 [3, 5, 7] (.B (.W 9623161 [3, 47]
  .L) (.W 9623163 [3, 47] .L))) (.W 4811583 [3, 5, 7] (.W 9623165 [3, 47] .L)))) (.W 2405791 [7] (.B (.W
  4811581 [3, 5, 7] (.B (.W 9623161 [3, 5, 47] .L) (.W 9623163 [3, 5, 47] .L))) (.W 4811583 [3, 5, 7] (.W
  9623165 [3, 5, 47] .L)))))) (.W 2096893 [3] (.B (.W 2405791 [7] (.B (.W 4811581 [3, 5, 7] (.B (.W
  9623161 [3, 5, 47] .L) (.W 9623163 [3, 5, 47] .L))) (.W 4811583 [3, 5, 7] .L))) (.W 2405791 [7] (.B (.W
  4811581 [3, 7] .L) (.W 4811583 [3, 7] .L))))))) (.W 1281463 [3] (.B (.W 2405791 [3, 7] (.B (.W 4811581
  [3, 5, 7] .L) (.W 4811583 [3, 5, 7] .L))) (.W 2405791 [3, 7] (.B (.W 4811581 [3, 7] .L) (.W 4811583
  [3, 7] .L))))))))))))) (.W 262111 [23] (.B (.W 524221 [3] (.B (.W 524287 [] (.B (.W 1048573 [5, 7, 17]
  (.B (.W 2097147 [3, 5] (.W 2405791 [7] (.B (.W 2562943 [] (.B (.W 4811581 [3, 7, 41] (.B (.W 9623161
  [3, 5, 7, 47] (.B (.W 19246323 [3, 5, 1447, 1571] .L) (.W 19246323 [3, 5, 1447] .L))) (.W 9623163
  [3, 5, 7, 47] (.W 19246325 [3, 5, 1447] .L)))) (.W 4811581 [3, 7, 41] (.B (.W 9623161 [3, 7, 47] (.B
  (.W 19246323 [3, 5, 1447, 1571] .L) (.W 19246323 [3, 5, 1447] .L))) (.W 9623163 [3, 7, 47] (.W 19246325
  [3, 5, 1447] .L)))))) (.W 2562943 [] (.B (.W 5125887 [3, 5, 7, 41] (.W 9623167 [3, 7, 47] .L)) (.W
  5125887 [3, 7, 41] (.W 9623167 [3, 7, 47] .L))))))) (.W 2097147 [3] (.W 2405791 [3, 7] (.B (.W 2562943
  [] (.B (.W 4811581 [3, 5, 7, 41] (.B (.W 9623161 [3, 5, 47] .L) (.W 9623163 [3, 5, 47] .L))) (.W
  4811581 [3, 5, 7, 41] (.B (.W 9623161 [3, 47] .L) (.W 9623163 [3, 47] .L))))) (.W 2562943 [] (.B (.W
  5125887 [3, 5, 7, 41] (.W 9623167 [3, 47] .L)) (.W 5125887 [3, 5, 7, 41] (.W 9623167 [3, 47]
  .L))))))))) (.W 1048575 [3, 5, 7, 17] (.W 2097149 [3] (.W 2405791 [7] (.B (.W 2562943 [] (.B (.W
  4811581 [3, 7, 41] .L) (.W 4811581 [3, 7, 41] .L))) (.W 2562943 [] (.B (.W 5125887 [3, 5, 7, 41] .L)
  (.W 5125887 [3, 7, 41] .L))))))))) (.W 524287 [] (.B (.W 1048573 [3, 5, 7] (.B (.W 2097147 [3, 5, 13]
  (.W 2405791 [7] (.B (.W 2562943 [] (.B (.W 4811581 [3, 7] (.B (.W 9623161 [3, 5, 7, 47, 137] .L) (.W
  9623163 [3, 5, 7, 47, 137] .L))) (.W 4811581 [3, 7] .L))) (.W 2562943 [] (.B (.W 5125887 [3, 5, 7] .L)
  (.W 5125887 [3, 7] .L)))))) (.W 2097147 [3, 13] (.W 2405791 [3, 7] (.B (.W 2562943 [] (.B (.W 4811581
  [3, 5, 7] .L) (.W 4811581 [3, 5, 7] .L))) (.W 2562943 [] (.B (.W 5125887 [3, 5, 7] .L) (.W 5125887
  [3, 5, 7] .L)))))))) (.W 1048575 [3, 5, 7] (.W 2097149 [3, 13] .L)))))) (.W 524223 [3] (.W 524287 [3]
  (.B (.W 1048447 [5, 7] (.B (.W 1048573 [] (.B (.W 2096893 [3] (.B (.W 2405791 [5, 7] (.B (.W 2562943 []
  (.B (.W 4811581 [3, 5, 7] .L) (.W 4811581 [3, 5, 7] .L))) (.W 2562943 [] .L))) (.W 2405791 [5, 7] .L)))
  (.W 2096893 [3] .L))) (.W 1048573 [] (.B (.W 2097147 [3, 5] .L) (.W 2097147 [3] .L))))) (.W 1048447
  [5, 7] (.B (.W 2096893 [3] .L) (.W 2096895 [3] .L))))))))))))) (.W 131071 [3] (.B (.W 160183 [3] (.B
  (.W 262111 [23] (.B (.W 524221 [3, 5, 7, 11] (.B (.W 524287 [3] (.B (.W 1048573 [3, 5, 13, 17] (.B (.W
  1281463 [3, 211] (.B (.J 1416437 (.W 2832873 [3, 5, 7] (.W 4194271 [7, 41] (.B (.W 4811647 [3] (.B (.W
  9623295 [3, 7, 37, 47] (.W 19246589 [3, 5, 7, 1447] (.W 33554167 [3] (.B (.W 67108335
  [5, 17, 29, 31, 47] (.W 134216669 [3] .L)) (.W 67108335 [3, 5, 29, 31, 47] (.W 134216669 [3] .L))))))
  (.W 9623295 [3, 7, 47] (.W 19246589 [3, 5, 7, 1447] (.W 33554167 [3, 7] (.B (.W 67108335
  [3, 5, 7, 17, 29, 31, 47] .L) (.W 67108335 [3, 5, 7, 29, 31, 47] .L))))))) (.W 4811647 [3] (.B (.W
  9623295 [3, 7, 37, 47] (.W 19246589 [3, 5, 7, 71, 1447] (.W 38493177 [3, 5, 31] .L))) (.W 9623295
  [3, 7, 47] (.W 19246589 [3, 5, 7, 71, 1447] (.W 38493177 [3, 5, 7, 31] .L))))))))) (.W 2562927
  [3, 5, 7] (.W 4194271 [3, 7, 41] (.B (.W 4811647 [3] (.B (.W 9623295 [3, 5, 7, 37, 47] (.W 19246589
  [3, 5, 1447] .L)) (.W 9623295 [3, 5, 7, 47] (.W 19246589 [3, 5, 1447] .L)))) (.W 4811647 [3] (.B (.W
  9623295 [3, 5, 7, 37, 47] (.W 19246589 [3, 5, 71, 1447] .L)) (.W 9623295 [3, 5, 7, 47] (.W 19246589
  [3, 5, 71, 1447] .L))))))))) (.W 1281463 [3, 211] (.B (.W 2562927 [3, 5, 7] (.W 4194271 [7, 41] (.B (.W
  4811647 [3, 5] (.B (.W 9623295 [3, 7, 37, 47] (.W 16777183 [3, 5, 7, 1447] .L)) (.W 9623295 [3, 7, 47]
  (.W 16777183 [3, 5, 7, 1447] .L)))) (.W 4811647 [3, 5] (.B (.W 9623295 [3, 37, 47] (.W 16777183
  [5, 7, 71, 1447] .L)) (.W 9623295 [3, 47] (.W 16777183 [3, 5, 7, 71, 1447] .L))))))) (.W 2562927 [3, 7]
  (.W 4194271 [3, 7, 41] (.B (.W 4811647 [3, 5] (.B (.W 9623295 [3, 5, 7, 37, 47] .L) (.W 9623295
  [3, 5, 7, 47] .L))) (.W 4811647 [3, 5] (.B (.W 9623295 [3, 5, 37, 47] .L) (.W 9623295 [3, 5, 47]
  .L)))))))))) (.W 1048575 [3, 5, 13, 17] (.W 1281463 [3, 211] (.B (.W 2562927 [3, 5, 7] (.W 4194271
  [7, 41] (.B (.W 4811647 [3] .L) (.W 4811647 [3] .L)))) (.W 2562927 [3, 7] (.W 4194271 [3, 7, 41]
  .L))))))) (.W 524287 [3] (.B (.W 1048573 [3, 5, 13] (.B (.W 1281463 [3, 211] (.B (.W 2562927
  [3, 5, 7, 13] (.W 4194271 [3, 7] (.B (.W 4811647 [3] (.B (.W 9623295 [3, 7, 37, 47, 137] .L) (.W
  9623295 [3, 7, 47, 137] .L))) (.W 4811647 [3] (.B (.W 9623295 [3, 7, 37, 47, 137] .L) (.W 9623295
  [3, 7, 47, 137] .L)))))) (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 7] (.B (.W 4811647 [3] (.B (.W
  9623295 [3, 5, 7, 37, 47, 137] .L) (.W 9623295 [3, 5, 7, 47, 137] .L))) (.W 4811647 [3] (.B (.W 9623295
  [3, 5, 7, 37, 47, 137] .L) (.W 9623295 [3, 5, 7, 47, 137] .L)))))))) (.W 1281463 [3, 211] (.B (.W
  2562927 [3, 5, 7, 13] (.W 4194271 [3, 7] (.B (.W 4811647 [3, 5] (.B (.W 9623295 [3, 7, 37, 47, 137] .L)
  (.W 9623295 [3, 7, 47, 137] .L))) (.W 4811647 [3, 5] (.B (.W 9623295 [3, 37, 47, 137] .L) (.W 9623295
  [3, 47, 137] .L)))))) (.W 2562927 [3, 7, 13] (.W 4194271 [3, 7] .L)))))) (.W 1048575 [3, 5, 13] (.W
  1281463 [3, 211] (.B (.W 2562927 [3, 5, 7, 13] (.W 4194271 [3, 7] .L)) (.W 2562927 [3, 7, 13]
  .L)))))))) (.W 524223 [3, 5, 7, 11] (.W 524287 [3] (.B (.W 1048447 [3, 5] (.B (.W 1048573 [13] (.B (.W
  1281463 [3, 211] (.B (.W 2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))) (.W
  2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))))) (.W 1281463 [3, 211] (.B (.W
  2096893 [3] (.B (.W 4193787 [3, 5, 7] .L) (.W 4193787 [3, 5, 7] .L))) (.W 2096893 [3] (.B (.W 4193787
  [3, 5, 7] .L) (.W 4193787 [3, 7] .L))))))) (.W 1048573 [13] (.B (.W 1281463 [3, 211] (.B (.W 2562927
  [3, 5, 7] (.W 4194271 [7] .L)) (.W 2562927 [3, 5, 7] .L))) (.W 1281463 [3, 211] (.B (.W 2562927
  [3, 5, 7] .L) (.W 2562927 [3, 7] .L))))))) (.W 1048447 [3, 5] (.B (.W 1281463 [3, 13, 211] (.B (.W
  2096893 [3] .L) (.W 2096893 [3] .L))) (.W 1281463 [3, 13, 211] (.B (.W 2562927 [3, 5, 7] .L) (.W
  2562927 [3, 7] .L)))))))))) (.W 262111 [23] (.B (.W 524221 [3, 7, 11] (.B (.W 524287 [3] (.B (.W
  1048573 [3, 5, 13, 17] (.B (.W 2097147 [3, 5, 211] (.W 2562943 [3, 7] .L)) (.W 2097147 [3, 211] .L)))
  (.W 1048575 [3, 5, 13, 17] (.W 2097149 [3, 211] .L)))) (.W 524287 [3] (.B (.W 1048573 [3, 5, 13] (.B
  (.W 2097147 [3, 5, 13, 211] .L) (.W 2097147 [3, 13, 211] .L))) (.W 1048575 [3, 5, 13] (.W 2097149
  [3, 13, 211] .L)))))) (.W 524223 [3, 7, 11] (.W 524287 [3] (.B (.W 1048447 [3, 5] (.B (.W 1048573 [13]
  (.B (.W 2096893 [3, 211] .L) (.W 2096893 [3, 211] .L))) (.W 1048573 [13] (.B (.W 2097147 [3, 5, 211]
  .L) (.W 2097147 [3, 211] .L))))) (.W 1048447 [3, 5] .L)))))))) (.W 160183 [3] (.B (.W 262111 [23] (.B
  (.W 524221 [3, 5, 7] (.B (.W 524287 [] (.B (.W 1048573 [3, 5, 17] (.B (.W 1281463 [3, 211] (.B (.W
  2562927 [3, 5, 7] .L) (.W 2562927 [3, 5, 7] .L))) (.W 1281463 [3, 211] (.B (.W 2562927 [3, 5, 7] .L)
  (.W 2562927 [3, 7] .L))))) (.W 1048575 [3, 5, 17] (.W 1281463 [3, 211] .L)))) (.W 524287 [] (.B (.W
  1048573 [3, 5] (.B (.W 1281463 [3, 211] (.B (.W 2562927 [3, 5, 7, 13] .L) (.W 2562927 [3, 5, 7, 13]
  .L))) (.W 1281463 [3, 211] .L))) (.W 1048575 [3, 5] .L))))) (.W 524223 [3, 5, 7] (.W 524287 [3] (.B (.W
  1048447 [3, 5] .L) (.W 1048447 [3, 5] .L)))))) (.W 262111 [23] (.B (.W 524221 [3, 7] (.B (.W 524287 []
  (.B (.W 1048573 [3, 5, 17] .L) (.W 1048575 [3, 5, 17] .L))) (.W 524287 [] (.B (.W 1048573 [3, 5] .L)
  (.W 1048575 [3, 5] .L))))) (.W 524223 [3, 7] .L)))))))))) (.W 75183 [3, 5, 7] (.W 131071 [3, 5, 7] (.B
  (.W 160183 [3, 7] (.B (.W 262111 [3, 5, 23] (.B (.W 524221 [3, 5, 11, 47] .L) (.W 524223 [3, 5, 11, 47]
  .L))) (.W 262111 [3, 5, 23] (.B (.W 524221 [3, 11, 47] .L) (.W 524223 [3, 11, 47] .L))))) (.W 160183
  [3, 7] (.B (.W 262111 [3, 5, 23] (.B (.W 524221 [3, 5, 11, 47] .L) (.W 524223 [3, 5, 11, 47] .L))) (.W
  262111 [3, 5, 23] (.B (.W 524221 [3, 11, 47] .L) (.W 524223 [3, 11, 47] .L)))))))))))) (.W 36037 [3, 7]
  (.B (.W 72073 [3, 7] (.B (.W 131071 [3, 5] (.B (.W 262111 [3, 5] (.B (.W 524221 [3, 7, 11] .L) (.W
  524223 [3, 7, 11] .L))) (.W 262111 [3, 5] .L))) (.W 131071 [3, 5] (.B (.W 262111 [3, 5] .L) (.W 262111
  [3, 5] .L))))) (.W 37591 [] (.B (.W 75181 [3, 5, 7] (.B (.W 131071 [3, 5] (.B (.W 262111 [3, 23, 53]
  (.B (.W 524221 [3, 7, 11] .L) (.W 524223 [3, 7, 11] .L))) (.W 262111 [3, 23, 53] .L))) (.W 131071
  [3, 5] (.B (.W 262111 [3, 23] .L) (.W 262111 [3, 23] .L))))) (.W 75183 [3, 5, 7] (.W 131071 [3, 5, 7]
  (.B (.W 185221 [3, 7] .L) (.W 185221 [3, 7] .L))))))))))))))) (.W 9397 [] (.B (.W 15583 [3] (.B (.J
  19238 (.W 20023 [] (.B (.J 490145 (.W 524287 [5] (.B (.J 7526644 (.W 15053287 [3, 5, 47] (.W 16777183
  [3] (.B (.W 33554367 [3, 5, 139] (.W 41007103 [3, 31] (.B (.W 82014207 [3, 5, 31] (.W 164028413
  [3, 5, 7, 19] (.W 328056825 [3, 5, 307, 313] .L))) (.W 82014207 [3, 31] (.W 164028413 [3, 5, 7, 19] (.W
  328056825 [3, 5, 313] .L)))))) (.W 33554367 [3, 5, 139] (.W 41007103 [3, 31] (.B (.W 82014207
  [3, 5, 31] (.W 164028413 [3, 5, 7] .L)) (.W 82014207 [3, 5, 31] (.W 164028413 [3, 5, 7] .L))))))))) (.W
  1048575 [3, 5] (.W 1994623 [3, 5] (.B (.W 2562943 [3, 7] (.B (.W 4811263 [3, 5] (.B (.W 9622527
  [3, 5, 47] (.W 19245053 [3, 7] .L)) (.W 9622527 [3, 5, 47] (.W 19245053 [3, 7] .L)))) (.W 4811263
  [3, 5] (.B (.W 9622527 [3, 5, 47] .L) (.W 9622527 [3, 47] .L))))) (.W 2562943 [3, 7] (.B (.W 4811263
  [3] (.B (.W 9622527 [5, 47] .L) (.W 9622527 [3, 5, 47] .L))) (.W 4811263 [3] (.B (.W 9622527 [3, 5, 47]
  .L) (.W 9622527 [3, 5, 47] .L))))))))))) (.W 40047 [3, 5, 7] (.W 80093 [3, 5] (.W 131071 [5, 7] (.B (.W
  262143 [3, 11] (.W 524285 [3, 5, 7, 13] .L)) (.W 262143 [3] .L)))))))) (.W 18793 [3] (.B (.W 20023 []
  (.B (.J 76919 (.W 131071 [3] (.B (.J 186173 (.W 372345 [3, 11, 23] (.W 524287 [3] (.B (.W 1048573
  [5, 13] (.B (.W 2097147 [3, 5] (.W 2562943 [7, 97] (.B (.W 4194271 [7] (.B (.W 8388543 [3, 5, 7] (.W
  16777085 [3, 5, 7, 47] .L)) (.W 8388543 [3, 5] .L))) (.W 4194271 [7] (.B (.W 8388543 [3, 7] .L) (.W
  8388543 [3] .L)))))) (.W 2097147 [3] (.W 2562943 [3, 7, 97] (.B (.W 4194271 [7] (.B (.W 8388543
  [3, 5, 7] .L) (.W 8388543 [3, 5] .L))) (.W 4194271 [7] (.B (.W 8388543 [3, 5, 7] .L) (.W 8388543 [3, 5]
  .L)))))))) (.W 1048575 [3, 5, 13] (.W 2097149 [3] (.W 2562943 [7, 97] (.B (.W 4194271 [7] .L) (.W
  4194271 [7] .L))))))))) (.W 150343 [] (.B (.J 157497 (.W 160183 [] (.B (.J 9390821 (.W 18781641 [3, 5]
  (.W 37563281 [3, 7, 31, 79] (.W 75126561 [3, 47] (.W 150253121 [3, 5, 7, 5779] .L))))) (.W 320367
  [3, 5, 23] (.W 524287 [3] (.B (.W 1048573 [3, 5] (.B (.W 1202743 [3] (.B (.W 2405487 [3, 5, 7] (.W
  2562943 [] (.B (.W 5125887 [3, 5, 7] (.W 9621943 [3, 7, 47] .L)) (.W 5125887 [3, 7] (.W 9621943
  [3, 7, 47] .L))))) (.W 2405487 [3, 5, 7] (.W 2562943 [3] (.B (.W 5125887 [3, 5, 7] .L) (.W 5125887
  [3, 5, 7] .L)))))) (.W 1202743 [3] (.B (.W 2405487 [3, 5, 7] (.W 2562943 [] (.B (.W 5125887 [3, 5, 7]
  .L) (.W 5125887 [3, 5, 7] .L)))) (.W 2405487 [3, 7] (.W 2562943 [3] (.B (.W 5125887 [3, 5, 7] .L) (.W
  5125887 [3, 5, 7] .L)))))))) (.W 1048575 [3, 5] (.W 1202743 [3] (.B (.W 2405487 [3, 5, 7] .L) (.W
  2405487 [3, 7] .L)))))))))) (.W 160183 [] (.B (.W 320367 [3, 5, 23] (.W 524287 [3] (.B (.W 1048573
  [3, 5] (.B (.W 1281463 [3] (.B (.W 2562927 [3, 5, 7, 97] (.W 5125853 [3, 7] .L)) (.W 2562927
  [3, 5, 7, 97] (.W 5125853 [3, 7] .L)))) (.W 1281463 [3] (.B (.W 2562927 [3, 5, 7, 97] (.W 5125853
  [3, 5, 7] .L)) (.W 2562927 [3, 7, 97] (.W 5125853 [3, 5, 7] .L)))))) (.W 1048575 [3, 5] (.W 1281463 [3]
  (.B (.W 2562927 [3, 5, 7, 97] .L) (.W 2562927 [3, 7, 97] .L))))))) (.W 320367 [3, 23] (.W 524287 [3]
  (.B (.W 1048573 [5] (.B (.W 2097147 [3, 5] .L) (.W 2097147 [3] .L))) (.W 1048575 [3, 5] .L)))))))))))
  (.W 40047 [3, 5, 7] (.W 80093 [3, 5] (.W 131071 [3, 5] (.B (.W 150343 [] (.B (.W 300687 [3, 5, 11, 23]
  .L) (.W 300687 [3, 11, 23] .L))) (.W 150343 [] (.B (.W 300687 [3, 5, 23] .L) (.W 300687 [3, 23]
  .L))))))))) (.W 20023 [] (.B (.W 40047 [3, 5, 7] (.W 80093 [3, 5] (.W 131071 [3] (.B (.W 160183 [3] (.B
  (.W 320367 [3, 5, 11, 13, 23] .L) (.W 320367 [3, 11, 13, 23] .L))) (.W 160183 [3] .L))))) (.W 40047
  [3, 7] (.W 80093 [3, 5] (.W 131071 [3, 5] .L))))))))) (.W 15583 [3] (.B (.W 20023 [3, 5, 19] (.B (.W
  37591 [3, 5, 7] (.B (.W 75181 [3, 5] (.B (.W 131071 [3, 7] (.B (.W 160183 [53] (.B (.W 320367
  [3, 5, 11] .L) (.W 320367 [3, 11] .L))) (.W 160183 [53] .L))) (.W 131071 [3, 7] .L))) (.W 75183
  [3, 5, 7] (.W 131071 [3, 5, 7] .L)))) (.W 37591 [3, 5, 7] (.B (.W 75181 [3] (.B (.W 131071 [5, 7] .L)
  (.W 131071 [5, 7] .L))) (.W 75183 [3, 7] (.W 131071 [3, 5, 7] .L)))))) (.W 20023 [3, 5, 19] (.B (.W
  36037 [3, 7] (.B (.W 72073 [3, 5, 7] .L) (.W 37591 [] (.B (.W 75181 [3, 5] .L) (.W 75183 [3, 5, 7]
  .L))))) (.W 36037 [3, 7] (.B (.W 72073 [3, 7] .L) (.W 37591 [] (.B (.W 75181 [3, 5] .L) (.W 75183
  [3, 5, 7] .L)))))))))))))) (.W 5007 [3, 5, 17] (.W 8191 [3] (.B (.W 9397 [] (.B (.W 15583 [5] (.B (.W
  16381 [] (.B (.W 18793 [3] (.B (.W 37587 [3, 5, 7, 181] (.W 40063 [] (.B (.W 80127 [3, 5] .L) (.W 80127
  [3] .L)))) (.W 37587 [3, 5, 7, 181] (.W 40063 [3] (.B (.W 80127 [3, 5] .L) (.W 80127 [3, 5] .L))))))
  (.W 18793 [3] (.B (.W 37587 [3, 5, 7] (.W 40063 [] (.B (.W 80127 [3, 5, 7] .L) (.W 80127 [3, 7] .L))))
  (.W 37587 [3, 5, 7] .L))))) (.W 16381 [] (.B (.W 18793 [3] (.B (.W 37587 [3, 5, 7, 181] (.W 40063 []
  (.B (.W 80127 [3, 5] .L) (.W 80127 [3, 5] .L)))) (.W 37587 [3, 7, 181] .L))) (.W 18793 [3] (.B (.W
  37587 [3, 5, 7] .L) (.W 37587 [3, 7] .L))))))) (.W 15583 [3, 5] (.B (.W 16381 [5] (.B (.W 32763
  [3, 5, 19, 181] (.W 37591 [7] .L)) (.W 32763 [3, 5, 19] .L))) (.W 16381 [5] (.B (.W 32763 [3, 19, 181]
  .L) (.W 32763 [3, 19] .L))))))) (.W 9397 [] (.B (.W 15583 [5] (.B (.W 18793 [3] (.B (.W 37587 [3, 5, 7]
  .L) (.W 37587 [3, 5, 7] .L))) (.W 18793 [3] (.B (.W 37587 [3, 5, 7] .L) (.W 37587 [3, 7] .L))))) (.W
  15583 [3, 5] (.B (.W 31167 [3, 5, 19] .L) (.W 31167 [3, 5, 19] .L))))))))))) (.W 975 [3, 5, 7] (.W 1949
  [3, 5, 7] (.W 1951 [] (.B (.W 2503 [3, 23] (.B (.W 5007 [3, 5, 17, 47] (.W 8191 [3] .L)) (.W 5007
  [3, 5, 17, 47] (.W 8191 [3] .L)))) (.W 2503 [3, 23] (.B (.W 4513 [3, 17] (.B (.W 8191 [3, 5] .L) (.W
  8191 [3, 5, 37] .L))) (.W 4513 [3, 17] .L)))))))))) (.W 487 [] (.B (.W 975 [3, 7] (.W 1949 [3, 5, 7]
  (.W 3897 [3, 5, 23] .L))) (.W 975 [3, 7] (.W 1949 [3, 5, 7] (.W 1951 [] (.B (.W 3903 [3, 23, 47] .L)
  (.W 3903 [3, 23] .L)))))))))) (.W 315 [3, 5, 11] (.W 487 [3] (.B (.W 631 [3, 7] (.B (.W 1263
  [3, 5, 7, 13] (.W 2525 [3, 23] .L)) (.W 1263 [3, 5, 7] .L))) (.W 631 [3, 7] (.B (.W 1263 [3, 5, 7, 13]
  .L) (.W 1263 [3, 5, 7] .L)))))))) (.W 157 [3] (.B (.W 313 [3, 5] (.B (.W 487 [] (.B (.W 975 [3, 5, 7]
  (.W 1949 [3, 7] .L)) (.W 975 [3, 5, 7] .L))) (.W 487 [] (.B (.W 975 [3, 7] .L) (.W 975 [3, 7] .L)))))
  (.W 315 [3, 5] (.W 487 [3] (.B (.W 631 [3, 7] .L) (.W 631 [3, 7] .L)))))))))) (.W 73 [3] (.B (.W 127
  [3] (.B (.W 157 [5] (.B (.W 313 [3, 11, 13] (.B (.W 627 [3, 5, 7, 11] (.W 991 [] (.B (.W 1983 [3, 5, 7]
  (.W 2503 [3, 5, 23] (.B (.W 5007 [3, 5, 17] .L) (.W 5007 [3, 17] .L)))) (.W 1983 [3, 5] (.W 2503
  [3, 5, 23] .L))))) (.W 627 [3, 7, 11] (.W 991 [3] (.B (.W 1983 [3, 5, 7] .L) (.W 1983 [3, 5] .L))))))
  (.W 315 [3, 11, 13] (.W 629 [3, 7, 11] (.W 631 [] (.B (.W 991 [] .L) (.W 991 [] .L))))))) (.W 157 [5]
  (.B (.W 313 [3, 13] (.B (.W 627 [3, 5, 7, 11] (.W 991 [] .L)) (.W 627 [3, 7, 11] .L))) (.W 315 [3, 13]
  (.W 629 [3, 7, 11] .L)))))) (.W 127 [3] (.B (.W 157 [3] (.B (.W 313 [3, 5, 11, 13] (.B (.W 627
  [3, 5, 7] (.W 991 [] .L)) (.W 627 [3, 7] .L))) (.W 315 [3, 5, 11, 13] (.W 629 [3, 7] .L)))) (.W 157 [3]
  (.B (.W 313 [3, 5, 13] (.B (.W 627 [3, 5, 7] .L) (.W 627 [3, 7] .L))) (.W 315 [3, 5, 13] .L)))))))))
  (.W 61 [] (.B (.W 123 [3, 11] (.W 127 [] (.B (.W 151 [] (.B (.W 157 [] (.B (.W 313 [3, 7, 11] (.B (.W
  487 [] (.B (.W 975 [3, 5, 7] .L) (.W 975 [3, 5, 7] .L))) (.W 487 [] .L))) (.W 315 [3, 7, 11] (.W 487
  [3] .L)))) (.W 157 [] (.B (.W 313 [3, 11] (.B (.W 487 [] .L) (.W 487 [] .L))) (.W 315 [3, 11] .L)))))
  (.W 151 [] (.B (.W 157 [] (.B (.W 313 [3, 7] .L) (.W 315 [3, 7] .L))) (.W 157 [] (.B (.W 313 [3] .L)
  (.W 315 [3] .L)))))))) (.W 123 [3] (.W 127 [3] (.B (.W 151 [] (.B (.W 157 [] (.B (.W 313 [3, 7, 11, 13]
  .L) (.W 315 [3, 7, 11, 13] .L))) (.W 157 [] (.B (.W 313 [3, 11, 13] .L) (.W 315 [3, 11, 13] .L))))) (.W
  151 [] (.B (.W 157 [] (.B (.W 313 [3, 7, 13] .L) (.W 315 [3, 7, 13] .L))) (.W 157 [] (.B (.W 313
  [3, 13] .L) (.W 315 [3, 13] .L)))))))))))) (.W 37 [] (.B (.W 73 [3] (.B (.W 127 [] (.B (.W 157 [5] (.B
  (.W 313 [3, 11] .L) (.W 315 [3, 11] .L))) (.W 157 [5] .L))) (.W 127 [] .L))) (.W 75 [3] (.W 127 [3]
  .L))))))))

set_option maxHeartbeats 8000000 in
theorem tree_ok : chk tree [3, 7, 13, 19, 79] 2 = true := by decide +kernel

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H3 := by
  refine ⟨0, fun n h hS he h43 ha4 hR5 _ => ?_⟩
  exfalso
  obtain ⟨hP, h5P, E⟩ := setup h hS
  rw [he] at E
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) = P at hP h5P E
  generalize padicValNat 2 n = m at E h43 ha4 hR5
  have h20 : 2 ^ 20 ∣ m := two_pow_20_dvd ha4 hR5
  have hm64 : 64 ≤ m := by
    have hle : 2 ^ 20 ≤ m := Nat.le_of_dvd (by omega) h20
    norm_num at hle
    omega
  obtain ⟨h3P, h3big, h13P, h7P, hc13⟩ := core25_even_data hP E h20 (by omega)
  obtain ⟨h19P, h79P⟩ := mem_19_and_79 hP h5P E h43 (fun p hp hd => (h3big p hp hd).1)
  have hno5 : ∀ p ∈ P, p ≠ 19 → p ≠ 79 → ¬ 5 ∣ p + 1 := fun p hp hp19 hp79 hd5 => by
    have hsub : ({p, 19, 79} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hprod : ∏ q ∈ ({p, 19, 79} : Finset ℕ), (q + 1) = (p + 1) * (19 + 1) * (79 + 1) := by
      rw [Finset.prod_insert (by simp [hp19, hp79]), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      ring
    apply ledger5 hP h5P E hsub
    rw [hprod, show (5 : ℕ) ^ 3 = 5 * 5 * 5 by norm_num]
    exact mul_dvd_mul (mul_dvd_mul hd5 (by norm_num)) (by norm_num)
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have hn5 : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have e1 : (1 + 5 ^ 2 : ℕ) = 26 := by norm_num
  have e2 : (5 ^ 2 : ℕ) = 25 := by norm_num
  have C : Ctx P m :=
    { hP := hP
      E := by rw [e1, e2] at E; exact E
      s1 := fun c hc hc2 hc5 p hp hd => S1 c hc hc2 (hn5 hc5) p hp hd
      s3 := fun c hc hc2 hc5 p hp p' hp' hd hd' => S3 c hc hc2 (hn5 hc5) p hp p' hp' hd hd'
      s6 := fun c hc hc2 hc5 p hp => S6 c hc hc2 (hn5 hc5) p hp
      hc13 := hc13
      h3big := h3big
      hno5 := hno5
      hm := hm64 }
  refine sound C tree [3, 7, 13, 19, 79] 2 tree_ok
    ⟨fun x hx => ?_, by decide, by decide, by decide, fun p hp hp2 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · have := (hP p hp).1.two_le
    omega

end OMA.P_Erdos1052_z5_e2_even

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H3 :=
  OMA.P_Erdos1052_z5_e2_even.step_proof
