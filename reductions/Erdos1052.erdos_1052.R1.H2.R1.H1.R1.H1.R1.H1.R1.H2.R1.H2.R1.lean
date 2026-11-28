import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2.R1
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2.R1 (3 is the only repeated odd prime of the unitary perfect
-- number n, its exponent is 7, a = padicValNat 2 n >= 262 is even with 16 not dividing a, and a avoids the
-- classes excluded there) by the exact power of 2 in a, with new excluded classes proved below.
-- Proving H1, H2 and H3 proves the step.
--
-- Notation as in the parent files: a is an ODD MULTIPLE of d when a mod 2d = d; then 2^d + 1 divides 2^a + 1.
-- Balance equation: (2^a + 1)(3^7 + 1) prod (p + 1) = 2^(a+1) 3^7 prod p over the simple primes p.
-- When a is an odd multiple of d, a and d have the same power of 2, so only the classes d with v2(d) = v2(a)
-- carry information: each Hk keeps exactly the parent classes with v2(d) = k and adds the new ones.
--
-- PROVED BELOW (no hypothesis needed), by the forced-root method of the parent (shared lemmas reused):
--   w52_sieve1: a is no odd multiple of any of 75 values d = 2 mod 4, 2986 <= d <= 4474;
--   w52_sieve2: a is no odd multiple of any of 150 values d = 4 mod 8, 3028 <= d <= 15772;
--   w52_sieve3: a is no odd multiple of any of 78 values d = 8 mod 16, 3064 <= d <= 15944.
--   None of these values is an odd multiple of a class already excluded upstream (or of an earlier new one).
--   Each case: primes q of 2^d + 1 are simple primes of n, odd primes other than 3 of q + 1 are simple again,
--   and the chain ends in a prime with two sources, a square, or more than 7 factors of 3 on the left.
--   The comment on each case names the contradiction. Primes above 4.3 * 10^7 carry a Lucas certificate
--   (theorems lp_<p>).
--   main: the three classes v2(a) = 1, 2, 3 cover the parent's hypotheses (a even, 16 does not divide a).
--
-- H1 (OPEN): a = 2 mod 4.   H2 (OPEN): a = 4 mod 8.   H3 (OPEN): a = 8 mod 16.
-- No known unitary perfect number satisfies the hypotheses of the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1 hiding H1 H2 H3 main

-- H1: a is bounded when a = 2 mod 4.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 2 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ((({262, 274, 278, 298, 302, 314, 326, 334, 346, 358, 362, 382, 386, 394, 398, 422, 446, 454, 458, 466, 478, 482, 502, 514, 526} : Finset ℕ) ∪
      ({538, 542, 554, 562, 586, 614, 622, 626, 634, 662, 674, 694, 698, 718, 758, 766, 778, 794, 802, 818, 838, 842, 862, 866, 878} : Finset ℕ) ∪
      ({898, 914, 922, 934, 958, 974, 982, 998, 1006, 1018, 1042, 1046, 1082, 1126, 1138, 1142, 1154, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294} : Finset ℕ) ∪
      ({1318, 1346, 1382, 1418, 1438, 1454, 1466, 1478, 1502, 1522, 1546, 1574, 1618, 1622, 1646, 1654, 1678, 1698, 1706, 1718, 1726, 1754, 1762, 1766, 1822} : Finset ℕ) ∪
      ({1838, 1858, 1874, 1882, 1894, 1934, 1942, 1982, 1994, 2018, 2026, 2038, 2062, 2066, 2098, 2102, 2126, 2138, 2174, 2182, 2186, 2194, 2206, 2218, 2234} : Finset ℕ) ∪
      ({2238, 2246, 2302, 2306, 2326, 2342, 2362, 2374, 2402, 2434, 2446, 2458, 2462, 2474, 2498, 2518, 2554, 2566, 2578, 2594, 2602, 2606, 2614, 2638, 2654} : Finset ℕ) ∪
      ({2722, 2734, 2762, 2778, 2798, 2818, 2846, 2854, 2858, 2878, 2902, 2906, 2942, 2962, 2966, 2974, 2978} : Finset ℕ)) ∪
      (({2986, 3022, 3086, 3134, 3142, 3158, 3166, 3194, 3202, 3214, 3218, 3238, 3242, 3254, 3274, 3282, 3326, 3334, 3386, 3394, 3398, 3418, 3466, 3494, 3506} : Finset ℕ) ∪
      ({3554, 3558, 3566, 3574, 3578, 3622, 3642, 3646, 3662, 3694, 3722, 3734, 3742, 3746, 3758, 3778, 3814, 3858, 3862, 3866, 3898, 3902, 3918, 3946, 3966} : Finset ℕ) ∪
      ({3974, 3986, 4034, 4054, 4058, 4062, 4078, 4098, 4138, 4162, 4166, 4178, 4198, 4206, 4222, 4262, 4274, 4282, 4286, 4306, 4406, 4414, 4426, 4442, 4474} : Finset ℕ))),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when a = 4 mod 8.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 8 = 4 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ((({268, 284, 316, 388, 412, 428, 436, 452, 508, 548, 604, 628, 652, 724, 788, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468} : Finset ℕ) ∪
      ({1492, 1604, 1636, 1756, 1796, 1844, 1868, 2188, 2284, 2308, 2348, 2372, 2396, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2644, 2692, 2764, 2908, 2932} : Finset ℕ) ∪
      ({2972} : Finset ℕ)) ∪
      (({3028, 3076, 3092, 3244, 3284, 3292, 3316, 3412, 3428, 3628, 3644, 3748, 4084, 4132, 4204, 4348, 4364, 4372, 4412, 4436, 4492, 4516, 4684, 4868, 4924} : Finset ℕ) ∪
      ({4996, 5036, 5108, 5116, 5188, 5204, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996, 6124, 6268, 6388, 6404, 6428, 6652, 6676} : Finset ℕ) ∪
      ({6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324, 8332, 8396, 8452, 8524, 8612, 8644, 8812} : Finset ℕ) ∪
      ({8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10684, 10732, 10796, 10876, 10916, 10924, 11156} : Finset ℕ) ∪
      ({11164, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228, 13316, 13444, 13484} : Finset ℕ) ∪
      ({13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14804, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692, 15724, 15772} : Finset ℕ))),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: a is bounded when a = 8 mod 16.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n → padicValNat 2 n % 16 = 8 →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ((({296, 328, 344, 376, 536, 568, 632, 712, 776, 824, 856, 904, 1048, 1304, 1384, 1432, 1528, 1544, 1688, 1784, 1816, 1832, 1864, 1912, 2056} : Finset ℕ) ∪
      ({2104, 2168, 2216, 2536, 2648, 2824} : Finset ℕ)) ∪
      (({3064, 3176, 3272, 3352, 3544, 3592, 3704, 3832, 3896, 4024, 4184, 4376, 4568, 4856, 4904, 5128, 5384, 5608, 5752, 6008, 6056, 6152, 6296, 6568, 6616} : Finset ℕ) ∪
      ({6856, 7016, 7048, 7096, 7256, 7528, 7768, 8104, 8728, 9208, 9304, 9544, 9704, 9784, 9832, 9896, 10264, 10312, 10424, 10552, 10568, 11416, 11624, 11768, 11864} : Finset ℕ) ∪
      ({11992, 12088, 12424, 12472, 12536, 12568, 12664, 12968, 13016, 13256, 13336, 13544, 13768, 13864, 13928, 14072, 14216, 14296, 14312, 14648, 14968, 14984, 15032, 15256, 15304} : Finset ℕ) ∪
      ({15464, 15608, 15944} : Finset ℕ))),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1. Lucas certificates and the new sieve.



theorem w52_v1_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2986, 3022, 3086, 3134, 3142, 3158, 3166, 3194, 3202, 3214, 3218, 3238, 3242, 3254, 3274, 3282, 3326, 3334, 3386, 3394, 3398, 3418, 3466, 3494, 3506} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2986) h  -- d = 2986: 5 | 2^2986+1, 173189+1
    rw [show (2:ℕ) ^ 2986 = (2 ^ 200) ^ 14 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g173189 : 173189 ∈ P := S2 173189 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 173189 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 173189 g173189 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3022) h  -- d = 3022: 5 | 2^3022+1, 41594809+1
    rw [show (2:ℕ) ^ 3022 = (2 ^ 200) ^ 15 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41594809 : 41594809 ∈ P := S2 41594809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41594809 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 41594809 g41594809 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3086) h  -- d = 3086: 7^2 | 6173+1
    rw [show (2:ℕ) ^ 3086 = (2 ^ 200) ^ 15 * 2 ^ 86 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 86 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6173 : 6173 ∈ P := S2 6173 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6173 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 6173 g6173 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3134) h  -- d = 3134: 5 | 2^3134+1, 6269+1
    rw [show (2:ℕ) ^ 3134 = (2 ^ 200) ^ 15 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6269 : 6269 ∈ P := S2 6269 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6269 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 6269 g6269 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3142) h  -- d = 3142: 5 | 2^3142+1, 5009+1
    rw [show (2:ℕ) ^ 3142 = (2 ^ 200) ^ 15 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g691241 : 691241 ∈ P := S2 691241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 691241 (by norm_num))
    have g5009 : 5009 ∈ P := S1 5009 (by norm_num) (by norm_num) (hnz (by norm_num)) 691241 g691241 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 5009 g5009 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3158) h  -- d = 3158: 7 | 33064261+1, 13+1
    rw [show (2:ℕ) ^ 3158 = (2 ^ 200) ^ 15 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33064261 : 33064261 ∈ P := S2 33064261 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33064261 (by norm_num))
    have g6317 : 6317 ∈ P := S2 6317 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6317 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 6317 g6317 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 33064261 g33064261 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3166) h  -- d = 3166: 5 | 2^3166+1, 29+1
    rw [show (2:ℕ) ^ 3166 = (2 ^ 200) ^ 15 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5654477 : 5654477 ∈ P := S2 5654477 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5654477 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 5654477 g5654477 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 29 g29 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3194) h  -- d = 3194: 5 | 2^3194+1, 6389+1
    rw [show (2:ℕ) ^ 3194 = (2 ^ 200) ^ 15 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6389 : 6389 ∈ P := S2 6389 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6389 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 6389 g6389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3202) h  -- d = 3202: 5 | 2^3202+1, 12809+1
    rw [show (2:ℕ) ^ 3202 = (2 ^ 200) ^ 16 * 2 ^ 2 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 2 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12809 : 12809 ∈ P := S2 12809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12809 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 12809 g12809 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3214) h  -- d = 3214: 7 | 668513+1, 181+1
    rw [show (2:ℕ) ^ 3214 = (2 ^ 200) ^ 16 * 2 ^ 14 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 14 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g668513 : 668513 ∈ P := S2 668513 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 668513 (by norm_num))
    have g1447 : 1447 ∈ P := S1 1447 (by norm_num) (by norm_num) (hnz (by norm_num)) 668513 g668513 (by norm_num)
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 1447 g1447 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 668513 g668513 181 g181 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3218) h  -- d = 3218: 5 | 2^3218+1, 19309+1
    rw [show (2:ℕ) ^ 3218 = (2 ^ 200) ^ 16 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19309 : 19309 ∈ P := S2 19309 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19309 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19309 g19309 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3238) h  -- d = 3238: 5 | 2^3238+1, 19429+1
    rw [show (2:ℕ) ^ 3238 = (2 ^ 200) ^ 16 * 2 ^ 38 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 38 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19429 : 19429 ∈ P := S2 19429 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19429 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19429 g19429 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3242) h  -- d = 3242: 5 | 2^3242+1, 19+1
    rw [show (2:ℕ) ^ 3242 = (2 ^ 200) ^ 16 * 2 ^ 42 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 42 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g26675177 : 26675177 ∈ P := S2 26675177 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26675177 (by norm_num))
    have g72883 : 72883 ∈ P := S1 72883 (by norm_num) (by norm_num) (hnz (by norm_num)) 26675177 g26675177 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 72883 g72883 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3254) h  -- d = 3254: 3^8 | (2^3254+1) prod (p+1), p in {5, 45557, 16230953, 2531, 17, 227}
    rw [show (2:ℕ) ^ 3254 = (2 ^ 200) ^ 16 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5 : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num))
    have g45557 : 45557 ∈ P := S2 45557 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 45557 (by norm_num))
    have g16230953 : 16230953 ∈ P := S2 16230953 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16230953 (by norm_num))
    have g2531 : 2531 ∈ P := S1 2531 (by norm_num) (by norm_num) (hnz (by norm_num)) 45557 g45557 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 16230953 g16230953 (by norm_num)
    have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 16230953 g16230953 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b2 := bud_cons b1 g45557 (by simp) (by norm_num : 3 ^ 2 ∣ 45557 + 1)
    have b3 := bud_cons b2 g16230953 (by simp) (by norm_num : 3 ^ 1 ∣ 16230953 + 1)
    have b4 := bud_cons b3 g2531 (by simp) (by norm_num : 3 ^ 1 ∣ 2531 + 1)
    have b5 := bud_cons b4 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b6 := bud_cons b5 g227 (by simp) (by norm_num : 3 ^ 1 ∣ 227 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3274) h  -- d = 3274: 5 | 2^3274+1, 859+1
    rw [show (2:ℕ) ^ 3274 = (2 ^ 200) ^ 16 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15381253 : 15381253 ∈ P := S2 15381253 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15381253 (by norm_num))
    have g859 : 859 ∈ P := S1 859 (by norm_num) (by norm_num) (hnz (by norm_num)) 15381253 g15381253 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 859 g859 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3282) h  -- d = 3282: 5 | 2^3282+1, 144409+1
    rw [show (2:ℕ) ^ 3282 = (2 ^ 200) ^ 16 * 2 ^ 82 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 82 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g288817 : 288817 ∈ P := S2 288817 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 288817 (by norm_num))
    have g144409 : 144409 ∈ P := S1 144409 (by norm_num) (by norm_num) (hnz (by norm_num)) 288817 g288817 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 144409 g144409 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3326) h  -- d = 3326: 5 | 2^3326+1, 1109+1
    rw [show (2:ℕ) ^ 3326 = (2 ^ 200) ^ 16 * 2 ^ 126 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 126 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6653 : 6653 ∈ P := S2 6653 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6653 (by norm_num))
    have g1109 : 1109 ∈ P := S1 1109 (by norm_num) (by norm_num) (hnz (by norm_num)) 6653 g6653 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1109 g1109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3334) h  -- d = 3334: 5 | 2^3334+1, 38180969+1
    rw [show (2:ℕ) ^ 3334 = (2 ^ 200) ^ 16 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38180969 : 38180969 ∈ P := S2 38180969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38180969 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 38180969 g38180969 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3386) h  -- d = 3386: 5 | 2^3386+1, 29+1
    rw [show (2:ℕ) ^ 3386 = (2 ^ 200) ^ 16 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10381477 : 10381477 ∈ P := S2 10381477 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10381477 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 10381477 g10381477 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 29 g29 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3394) h  -- d = 3394: 19^2 | 1622333+1
    rw [show (2:ℕ) ^ 3394 = (2 ^ 200) ^ 16 * 2 ^ 194 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 194 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1622333 : 1622333 ∈ P := S2 1622333 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1622333 (by norm_num))
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1622333 g1622333 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3398) h  -- d = 3398: 5 | 2^3398+1, 20389+1
    rw [show (2:ℕ) ^ 3398 = (2 ^ 200) ^ 16 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20389 : 20389 ∈ P := S2 20389 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20389 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 20389 g20389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3418) h  -- d = 3418: 41^2 | 205081+1
    rw [show (2:ℕ) ^ 3418 = (2 ^ 200) ^ 17 * 2 ^ 18 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 18 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g205081 : 205081 ∈ P := S2 205081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 205081 (by norm_num))
    exact S6 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 205081 g205081 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3466) h  -- d = 3466: 7^2 | 97+1
    rw [show (2:ℕ) ^ 3466 = (2 ^ 200) ^ 17 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1060597 : 1060597 ∈ P := S2 1060597 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1060597 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 1060597 g1060597 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3494) h  -- d = 3494: 19 | 5927+1, 37+1
    rw [show (2:ℕ) ^ 3494 = (2 ^ 200) ^ 17 * 2 ^ 94 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 94 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2264113 : 2264113 ∈ P := S2 2264113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2264113 (by norm_num))
    have g5927 : 5927 ∈ P := S1 5927 (by norm_num) (by norm_num) (hnz (by norm_num)) 2264113 g2264113 (by norm_num)
    have g27953 : 27953 ∈ P := S2 27953 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27953 (by norm_num))
    have g1553 : 1553 ∈ P := S1 1553 (by norm_num) (by norm_num) (hnz (by norm_num)) 27953 g27953 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1553 g1553 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 5927 g5927 37 g37 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3506) h  -- d = 3506: 5 | 2^3506+1, 15840109+1
    rw [show (2:ℕ) ^ 3506 = (2 ^ 200) ^ 17 * 2 ^ 106 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 106 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15840109 : 15840109 ∈ P := S2 15840109 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15840109 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 15840109 g15840109 (by norm_num)

theorem w52_v1_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3554, 3558, 3566, 3574, 3578, 3622, 3642, 3646, 3662, 3694, 3722, 3734, 3742, 3746, 3758, 3778, 3814, 3858, 3862, 3866, 3898, 3902, 3918, 3946, 3966} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3554) h  -- d = 3554: 5 | 2^3554+1, 7109+1
    rw [show (2:ℕ) ^ 3554 = (2 ^ 200) ^ 17 * 2 ^ 154 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 154 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7109 : 7109 ∈ P := S2 7109 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7109 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 7109 g7109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3558) h  -- d = 3558: 5 | 2^3558+1, 56929+1
    rw [show (2:ℕ) ^ 3558 = (2 ^ 200) ^ 17 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g56929 : 56929 ∈ P := S2 56929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 56929 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 56929 g56929 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3566) h  -- d = 3566: 5 | 2^3566+1, 171169+1
    rw [show (2:ℕ) ^ 3566 = (2 ^ 200) ^ 17 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g171169 : 171169 ∈ P := S2 171169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 171169 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 171169 g171169 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3574) h  -- d = 3574: 5 | 2^3574+1, 1329529+1
    rw [show (2:ℕ) ^ 3574 = (2 ^ 200) ^ 17 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1329529 : 1329529 ∈ P := S2 1329529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1329529 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1329529 g1329529 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3578) h  -- d = 3578: 13^2 | 5796361+1
    rw [show (2:ℕ) ^ 3578 = (2 ^ 200) ^ 17 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5796361 : 5796361 ∈ P := S2 5796361 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5796361 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 5796361 g5796361 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3622) h  -- d = 3622: 5 | 2^3622+1, 14489+1
    rw [show (2:ℕ) ^ 3622 = (2 ^ 200) ^ 18 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14489 : 14489 ∈ P := S2 14489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14489 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 14489 g14489 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3642) h  -- d = 3642: 13 | 2^3642+1, 857+1
    rw [show (2:ℕ) ^ 3642 = (2 ^ 200) ^ 18 * 2 ^ 42 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 42 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29137 : 29137 ∈ P := S2 29137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29137 (by norm_num))
    have g857 : 857 ∈ P := S1 857 (by norm_num) (by norm_num) (hnz (by norm_num)) 29137 g29137 (by norm_num)
    exact S4 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13 (by norm_num)) 857 g857 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3646) h  -- d = 3646: 5 | 2^3646+1, 29+1
    rw [show (2:ℕ) ^ 3646 = (2 ^ 200) ^ 18 * 2 ^ 46 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 46 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g58337 : 58337 ∈ P := S2 58337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 58337 (by norm_num))
    have g463 : 463 ∈ P := S1 463 (by norm_num) (by norm_num) (hnz (by norm_num)) 58337 g58337 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 463 g463 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 29 g29 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3662) h  -- d = 3662: 7 | 95213+1, 2267+1
    rw [show (2:ℕ) ^ 3662 = (2 ^ 200) ^ 18 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g95213 : 95213 ∈ P := S2 95213 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 95213 (by norm_num))
    have g2267 : 2267 ∈ P := S1 2267 (by norm_num) (by norm_num) (hnz (by norm_num)) 95213 g95213 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 95213 g95213 2267 g2267 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3694) h  -- d = 3694: 11^2 | 125597+1
    rw [show (2:ℕ) ^ 3694 = (2 ^ 200) ^ 18 * 2 ^ 94 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 94 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g125597 : 125597 ∈ P := S2 125597 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 125597 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 125597 g125597 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3722) h  -- d = 3722: 7^2 | 2009881+1
    rw [show (2:ℕ) ^ 3722 = (2 ^ 200) ^ 18 * 2 ^ 122 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 122 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2009881 : 2009881 ∈ P := S2 2009881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2009881 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2009881 g2009881 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3734) h  -- d = 3734: 5 | 2^3734+1, 44809+1
    rw [show (2:ℕ) ^ 3734 = (2 ^ 200) ^ 18 * 2 ^ 134 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 134 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g44809 : 44809 ∈ P := S2 44809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44809 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 44809 g44809 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3742) h  -- d = 3742: 5 | 2^3742+1, 109+1
    rw [show (2:ℕ) ^ 3742 = (2 ^ 200) ^ 18 * 2 ^ 142 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 142 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g22453 : 22453 ∈ P := S2 22453 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22453 (by norm_num))
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 22453 g22453 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 109 g109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3746) h  -- d = 3746: 13^2 | 44953+1
    rw [show (2:ℕ) ^ 3746 = (2 ^ 200) ^ 18 * 2 ^ 146 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 146 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g44953 : 44953 ∈ P := S2 44953 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44953 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 44953 g44953 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3758) h  -- d = 3758: 5 | 2^3758+1, 179+1
    rw [show (2:ℕ) ^ 3758 = (2 ^ 200) ^ 18 * 2 ^ 158 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 158 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7517 : 7517 ∈ P := S2 7517 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7517 (by norm_num))
    have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 7517 g7517 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 179 g179 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3778) h  -- d = 3778: 5 | 2^3778+1, 22669+1
    rw [show (2:ℕ) ^ 3778 = (2 ^ 200) ^ 18 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g45337 : 45337 ∈ P := S2 45337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 45337 (by norm_num))
    have g22669 : 22669 ∈ P := S1 22669 (by norm_num) (by norm_num) (hnz (by norm_num)) 45337 g45337 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 22669 g22669 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3814) h  -- d = 3814: 5 | 2^3814+1, 903919+1
    rw [show (2:ℕ) ^ 3814 = (2 ^ 200) ^ 19 * 2 ^ 14 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 14 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1807837 : 1807837 ∈ P := S2 1807837 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1807837 (by norm_num))
    have g903919 : 903919 ∈ P := S1 903919 (by norm_num) (by norm_num) (hnz (by norm_num)) 1807837 g1807837 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 903919 g903919 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3858) h  -- d = 3858: 13 | 2^3858+1, 169753+1
    rw [show (2:ℕ) ^ 3858 = (2 ^ 200) ^ 19 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g169753 : 169753 ∈ P := S2 169753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 169753 (by norm_num))
    exact S4 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13 (by norm_num)) 169753 g169753 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3862) h  -- d = 3862: 5 | 2^3862+1, 8550469+1
    rw [show (2:ℕ) ^ 3862 = (2 ^ 200) ^ 19 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8550469 : 8550469 ∈ P := S2 8550469 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8550469 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8550469 g8550469 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3866) h  -- d = 3866: 5 | 2^3866+1, 533509+1
    rw [show (2:ℕ) ^ 3866 = (2 ^ 200) ^ 19 * 2 ^ 66 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 66 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g533509 : 533509 ∈ P := S2 533509 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 533509 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 533509 g533509 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3898) h  -- d = 3898: 5 | 2^3898+1, 29+1
    rw [show (2:ℕ) ^ 3898 = (2 ^ 200) ^ 19 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g26818241 : 26818241 ∈ P := S2 26818241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26818241 (by norm_num))
    have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 26818241 g26818241 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 29 g29 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3902) h  -- d = 3902: 5 | 2^3902+1, 54629+1
    rw [show (2:ℕ) ^ 3902 = (2 ^ 200) ^ 19 * 2 ^ 102 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 102 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g54629 : 54629 ∈ P := S2 54629 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 54629 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 54629 g54629 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3918) h  -- d = 3918: 5 | 2^3918+1, 1069+1
    rw [show (2:ℕ) ^ 3918 = (2 ^ 200) ^ 19 * 2 ^ 118 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 118 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1684741 : 1684741 ∈ P := S2 1684741 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1684741 (by norm_num))
    have g842371 : 842371 ∈ P := S1 842371 (by norm_num) (by norm_num) (hnz (by norm_num)) 1684741 g1684741 (by norm_num)
    have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 842371 g842371 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1069 g1069 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3946) h  -- d = 3946: 5 | 2^3946+1, 11839+1
    rw [show (2:ℕ) ^ 3946 = (2 ^ 200) ^ 19 * 2 ^ 146 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 146 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g23677 : 23677 ∈ P := S2 23677 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23677 (by norm_num))
    have g11839 : 11839 ∈ P := S1 11839 (by norm_num) (by norm_num) (hnz (by norm_num)) 23677 g23677 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 11839 g11839 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3966) h  -- d = 3966: 31 | 126913+1, 3967+1
    rw [show (2:ℕ) ^ 3966 = (2 ^ 200) ^ 19 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g126913 : 126913 ∈ P := S2 126913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 126913 (by norm_num))
    have g7933 : 7933 ∈ P := S2 7933 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7933 (by norm_num))
    have g3967 : 3967 ∈ P := S1 3967 (by norm_num) (by norm_num) (hnz (by norm_num)) 7933 g7933 (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 126913 g126913 3967 g3967 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v1_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3974, 3986, 4034, 4054, 4058, 4062, 4078, 4098, 4138, 4162, 4166, 4178, 4198, 4206, 4222, 4262, 4274, 4282, 4286, 4306, 4406, 4414, 4426, 4442, 4474} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3974) h  -- d = 3974: 5^2 | 7949+1
    rw [show (2:ℕ) ^ 3974 = (2 ^ 200) ^ 19 * 2 ^ 174 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 174 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7949 : 7949 ∈ P := S2 7949 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7949 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7949 g7949 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3986) h  -- d = 3986: 5 | 2^3986+1, 1028389+1
    rw [show (2:ℕ) ^ 3986 = (2 ^ 200) ^ 19 * 2 ^ 186 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 186 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2056777 : 2056777 ∈ P := S2 2056777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2056777 (by norm_num))
    have g1028389 : 1028389 ∈ P := S1 1028389 (by norm_num) (by norm_num) (hnz (by norm_num)) 2056777 g2056777 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1028389 g1028389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4034) h  -- d = 4034: 5 | 2^4034+1, 8069+1
    rw [show (2:ℕ) ^ 4034 = (2 ^ 200) ^ 20 * 2 ^ 34 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 34 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8069 : 8069 ∈ P := S2 8069 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8069 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 8069 g8069 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4054) h  -- d = 4054: 5 | 2^4054+1, 12332269+1
    rw [show (2:ℕ) ^ 4054 = (2 ^ 200) ^ 20 * 2 ^ 54 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 54 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12332269 : 12332269 ∈ P := S2 12332269 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12332269 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 12332269 g12332269 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4058) h  -- d = 4058: 5 | 2^4058+1, 348989+1
    rw [show (2:ℕ) ^ 4058 = (2 ^ 200) ^ 20 * 2 ^ 58 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 58 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g348989 : 348989 ∈ P := S2 348989 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 348989 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 348989 g348989 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4062) h  -- d = 4062: 7 | 13+1, 5417+1
    rw [show (2:ℕ) ^ 4062 = (2 ^ 200) ^ 20 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13 (by norm_num))
    have g5417 : 5417 ∈ P := S2 5417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5417 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 5417 g5417 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4078) h  -- d = 4078: 5 | 2^4078+1, 24469+1
    rw [show (2:ℕ) ^ 4078 = (2 ^ 200) ^ 20 * 2 ^ 78 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 78 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g24469 : 24469 ∈ P := S2 24469 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 24469 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 24469 g24469 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4098) h  -- d = 4098: 5 | 2^4098+1, 967129+1
    rw [show (2:ℕ) ^ 4098 = (2 ^ 200) ^ 20 * 2 ^ 98 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 98 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g967129 : 967129 ∈ P := S2 967129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 967129 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 967129 g967129 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4138) h  -- d = 4138: 11^2 | 41381+1
    rw [show (2:ℕ) ^ 4138 = (2 ^ 200) ^ 20 * 2 ^ 138 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 138 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41381 : 41381 ∈ P := S2 41381 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41381 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 41381 g41381 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4162) h  -- d = 4162: 7 | 41621+1, 41+1
    rw [show (2:ℕ) ^ 4162 = (2 ^ 200) ^ 20 * 2 ^ 162 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 162 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41621 : 41621 ∈ P := S2 41621 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41621 (by norm_num))
    have g665921 : 665921 ∈ P := S2 665921 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 665921 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 665921 g665921 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41621 g41621 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4166) h  -- d = 4166: 5 | 2^4166+1, 19+1
    rw [show (2:ℕ) ^ 4166 = (2 ^ 200) ^ 20 * 2 ^ 166 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 166 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1674733 : 1674733 ∈ P := S2 1674733 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1674733 (by norm_num))
    have g837367 : 837367 ∈ P := S1 837367 (by norm_num) (by norm_num) (hnz (by norm_num)) 1674733 g1674733 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 837367 g837367 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4178) h  -- d = 4178: 5 | 2^4178+1, 19+1
    rw [show (2:ℕ) ^ 4178 = (2 ^ 200) ^ 20 * 2 ^ 178 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 178 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g83561 : 83561 ∈ P := S2 83561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 83561 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 83561 g83561 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 19 g19 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4198) h  -- d = 4198: 7 | 92357+1, 944551+1
    rw [show (2:ℕ) ^ 4198 = (2 ^ 200) ^ 20 * 2 ^ 198 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 198 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g92357 : 92357 ∈ P := S2 92357 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 92357 (by norm_num))
    have g1889101 : 1889101 ∈ P := S2 1889101 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1889101 (by norm_num))
    have g944551 : 944551 ∈ P := S1 944551 (by norm_num) (by norm_num) (hnz (by norm_num)) 1889101 g1889101 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 92357 g92357 944551 g944551 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4206) h  -- d = 4206: 7 | 13+1, 3305917+1
    rw [show (2:ℕ) ^ 4206 = (2 ^ 200) ^ 21 * 2 ^ 6 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 6 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13 (by norm_num))
    have g3305917 : 3305917 ∈ P := S2 3305917 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3305917 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 3305917 g3305917 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4222) h  -- d = 4222: 5 | 2^4222+1, 16889+1
    rw [show (2:ℕ) ^ 4222 = (2 ^ 200) ^ 21 * 2 ^ 22 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 22 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16889 : 16889 ∈ P := S2 16889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16889 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 16889 g16889 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4262) h  -- d = 4262: 5 | 2^4262+1, 2389+1
    rw [show (2:ℕ) ^ 4262 = (2 ^ 200) ^ 21 * 2 ^ 62 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 62 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33584561 : 33584561 ∈ P := S2 33584561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33584561 (by norm_num))
    have g2389 : 2389 ∈ P := S1 2389 (by norm_num) (by norm_num) (hnz (by norm_num)) 33584561 g33584561 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 2389 g2389 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4274) h  -- d = 4274: 5 | 2^4274+1, 1162529+1
    rw [show (2:ℕ) ^ 4274 = (2 ^ 200) ^ 21 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1162529 : 1162529 ∈ P := S2 1162529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1162529 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 1162529 g1162529 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4282) h  -- d = 4282: 5 | 2^4282+1, 20014069+1
    rw [show (2:ℕ) ^ 4282 = (2 ^ 200) ^ 21 * 2 ^ 82 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 82 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20014069 : 20014069 ∈ P := S2 20014069 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20014069 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 20014069 g20014069 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4286) h  -- d = 4286: 7 | 385741+1, 17186861+1
    rw [show (2:ℕ) ^ 4286 = (2 ^ 200) ^ 21 * 2 ^ 86 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 86 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g385741 : 385741 ∈ P := S2 385741 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 385741 (by norm_num))
    have g17186861 : 17186861 ∈ P := S2 17186861 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17186861 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 385741 g385741 17186861 g17186861 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4306) h  -- d = 4306: 7 | 51673+1, 13+1
    rw [show (2:ℕ) ^ 4306 = (2 ^ 200) ^ 21 * 2 ^ 106 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 106 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g51673 : 51673 ∈ P := S2 51673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 51673 (by norm_num))
    have g3691 : 3691 ∈ P := S1 3691 (by norm_num) (by norm_num) (hnz (by norm_num)) 51673 g51673 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3691 g3691 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 51673 g51673 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4406) h  -- d = 4406: 5 | 2^4406+1, 13219+1
    rw [show (2:ℕ) ^ 4406 = (2 ^ 200) ^ 22 * 2 ^ 6 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 6 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g26437 : 26437 ∈ P := S2 26437 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26437 (by norm_num))
    have g13219 : 13219 ∈ P := S1 13219 (by norm_num) (by norm_num) (hnz (by norm_num)) 26437 g26437 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 13219 g13219 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4414) h  -- d = 4414: 5 | 2^4414+1, 109+1
    rw [show (2:ℕ) ^ 4414 = (2 ^ 200) ^ 22 * 2 ^ 14 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 14 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17657 : 17657 ∈ P := S2 17657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17657 (by norm_num))
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 17657 g17657 (by norm_num)
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 109 g109 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4426) h  -- d = 4426: 5 | 2^4426+1, 79669+1
    rw [show (2:ℕ) ^ 4426 = (2 ^ 200) ^ 22 * 2 ^ 26 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 26 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g79669 : 79669 ∈ P := S2 79669 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 79669 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 79669 g79669 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4442) h  -- d = 4442: 5 | 2^4442+1, 7658009+1
    rw [show (2:ℕ) ^ 4442 = (2 ^ 200) ^ 22 * 2 ^ 42 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 42 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7658009 : 7658009 ∈ P := S2 7658009 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7658009 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 7658009 g7658009 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4474) h  -- d = 4474: 5 | 2^4474+1, 30253189+1
    rw [show (2:ℕ) ^ 4474 = (2 ^ 200) ^ 22 * 2 ^ 74 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 74 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30253189 : 30253189 ∈ P := S2 30253189 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30253189 (by norm_num))
    exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5 (by norm_num)) 30253189 g30253189 (by norm_num)

theorem w52_v2_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3028, 3076, 3092, 3244, 3284, 3292, 3316, 3412, 3428, 3628, 3644, 3748, 4084, 4132, 4204, 4348, 4364, 4372, 4412, 4436, 4492, 4516, 4684, 4868, 4924} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3028) h  -- d = 3028: 13^2 | 337+1
    rw [show (2:ℕ) ^ 3028 = (2 ^ 200) ^ 15 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12113 : 12113 ∈ P := S2 12113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12113 (by norm_num))
    have g673 : 673 ∈ P := S1 673 (by norm_num) (by norm_num) (hnz (by norm_num)) 12113 g12113 (by norm_num)
    have g337 : 337 ∈ P := S1 337 (by norm_num) (by norm_num) (hnz (by norm_num)) 673 g673 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 337 g337 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3076) h  -- d = 3076: 5 | 270689+1, 1289+1
    rw [show (2:ℕ) ^ 3076 = (2 ^ 200) ^ 15 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g270689 : 270689 ∈ P := S2 270689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 270689 (by norm_num))
    have g1289 : 1289 ∈ P := S1 1289 (by norm_num) (by norm_num) (hnz (by norm_num)) 270689 g270689 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 270689 g270689 1289 g1289 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3092) h  -- d = 3092: 5 | 1620209+1, 1019+1
    rw [show (2:ℕ) ^ 3092 = (2 ^ 200) ^ 15 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1620209 : 1620209 ∈ P := S2 1620209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1620209 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 1620209 g1620209 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1620209 g1620209 1019 g1019 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3244) h  -- d = 3244: 5 | 15139+1, 140419+1
    rw [show (2:ℕ) ^ 3244 = (2 ^ 200) ^ 16 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g90833 : 90833 ∈ P := S2 90833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 90833 (by norm_num))
    have g15139 : 15139 ∈ P := S1 15139 (by norm_num) (by norm_num) (hnz (by norm_num)) 90833 g90833 (by norm_num)
    have g15726913 : 15726913 ∈ P := S2 15726913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15726913 (by norm_num))
    have g1123351 : 1123351 ∈ P := S1 1123351 (by norm_num) (by norm_num) (hnz (by norm_num)) 15726913 g15726913 (by norm_num)
    have g140419 : 140419 ∈ P := S1 140419 (by norm_num) (by norm_num) (hnz (by norm_num)) 1123351 g1123351 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 15139 g15139 140419 g140419 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3284) h  -- d = 3284: 5^2 | 236449+1
    rw [show (2:ℕ) ^ 3284 = (2 ^ 200) ^ 16 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g236449 : 236449 ∈ P := S2 236449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 236449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 236449 g236449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3292) h  -- d = 3292: 5 | 8779+1, 439+1
    rw [show (2:ℕ) ^ 3292 = (2 ^ 200) ^ 16 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g52673 : 52673 ∈ P := S2 52673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 52673 (by norm_num))
    have g8779 : 8779 ∈ P := S1 8779 (by norm_num) (by norm_num) (hnz (by norm_num)) 52673 g52673 (by norm_num)
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 8779 g8779 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8779 g8779 439 g439 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3316) h  -- d = 3316: 3^8 | (2^3316+1) prod (p+1), p in {17, 11, 76871, 3203, 89}
    rw [show (2:ℕ) ^ 3316 = (2 ^ 200) ^ 16 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g3382321 : 3382321 ∈ P := S2 3382321 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3382321 (by norm_num))
    have g1691161 : 1691161 ∈ P := S1 1691161 (by norm_num) (by norm_num) (hnz (by norm_num)) 3382321 g3382321 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1691161 g1691161 (by norm_num)
    have g76871 : 76871 ∈ P := S1 76871 (by norm_num) (by norm_num) (hnz (by norm_num)) 1691161 g1691161 (by norm_num)
    have g3203 : 3203 ∈ P := S1 3203 (by norm_num) (by norm_num) (hnz (by norm_num)) 76871 g76871 (by norm_num)
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 3203 g3203 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b3 := bud_cons b2 g76871 (by simp) (by norm_num : 3 ^ 1 ∣ 76871 + 1)
    have b4 := bud_cons b3 g3203 (by simp) (by norm_num : 3 ^ 2 ∣ 3203 + 1)
    have b5 := bud_cons b4 g89 (by simp) (by norm_num : 3 ^ 2 ∣ 89 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3412) h  -- d = 3412: 5^2 | 13649+1
    rw [show (2:ℕ) ^ 3412 = (2 ^ 200) ^ 17 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13649 : 13649 ∈ P := S2 13649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13649 g13649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3428) h  -- d = 3428: 5^2 | 4511249+1
    rw [show (2:ℕ) ^ 3428 = (2 ^ 200) ^ 17 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4511249 : 4511249 ∈ P := S2 4511249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4511249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4511249 g4511249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3628) h  -- d = 3628: 7^2 | 97+1
    rw [show (2:ℕ) ^ 3628 = (2 ^ 200) ^ 18 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g667553 : 667553 ∈ P := S2 667553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 667553 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 667553 g667553 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3644) h  -- d = 3644: 5^2 | 335249+1
    rw [show (2:ℕ) ^ 3644 = (2 ^ 200) ^ 18 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g335249 : 335249 ∈ P := S2 335249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 335249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 335249 g335249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3748) h  -- d = 3748: 5^2 | 5532049+1
    rw [show (2:ℕ) ^ 3748 = (2 ^ 200) ^ 18 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5532049 : 5532049 ∈ P := S2 5532049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5532049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5532049 g5532049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4084) h  -- d = 4084: 5 | 1289+1, 79+1
    rw [show (2:ℕ) ^ 4084 = (2 ^ 200) ^ 20 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4851793 : 4851793 ∈ P := S2 4851793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4851793 (by norm_num))
    have g2425897 : 2425897 ∈ P := S1 2425897 (by norm_num) (by norm_num) (hnz (by norm_num)) 4851793 g4851793 (by norm_num)
    have g1289 : 1289 ∈ P := S1 1289 (by norm_num) (by norm_num) (hnz (by norm_num)) 2425897 g2425897 (by norm_num)
    have g941 : 941 ∈ P := S1 941 (by norm_num) (by norm_num) (hnz (by norm_num)) 2425897 g2425897 (by norm_num)
    have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 941 g941 (by norm_num)
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1289 g1289 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4132) h  -- d = 4132: 5 | 16529+1, 19+1
    rw [show (2:ℕ) ^ 4132 = (2 ^ 200) ^ 20 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16529 : 16529 ∈ P := S2 16529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16529 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 16529 g16529 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 16529 g16529 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4204) h  -- d = 4204: 3^8 | (2^4204+1) prod (p+1), p in {17, 317, 557, 53}
    rw [show (2:ℕ) ^ 4204 = (2 ^ 200) ^ 21 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g353137 : 353137 ∈ P := S2 353137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 353137 (by norm_num))
    have g317 : 317 ∈ P := S1 317 (by norm_num) (by norm_num) (hnz (by norm_num)) 353137 g353137 (by norm_num)
    have g557 : 557 ∈ P := S1 557 (by norm_num) (by norm_num) (hnz (by norm_num)) 353137 g353137 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g317 (by simp) (by norm_num : 3 ^ 1 ∣ 317 + 1)
    have b3 := bud_cons b2 g557 (by simp) (by norm_num : 3 ^ 2 ∣ 557 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4348) h  -- d = 4348: 7 | 13+1, 223+1
    rw [show (2:ℕ) ^ 4348 = (2 ^ 200) ^ 21 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17393 : 17393 ∈ P := S2 17393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17393 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 17393 g17393 (by norm_num)
    have g223 : 223 ∈ P := S1 223 (by norm_num) (by norm_num) (hnz (by norm_num)) 17393 g17393 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 223 g223 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4364) h  -- d = 4364: 3^8 | (2^4364+1) prod (p+1), p in {17, 23967089, 5}
    rw [show (2:ℕ) ^ 4364 = (2 ^ 200) ^ 21 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g23967089 : 23967089 ∈ P := S2 23967089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23967089 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 23967089 g23967089 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g23967089 (by simp) (by norm_num : 3 ^ 5 ∣ 23967089 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4372) h  -- d = 4372: 3^8 | (2^4372+1) prod (p+1), p in {17, 17489, 5, 11, 53}
    rw [show (2:ℕ) ^ 4372 = (2 ^ 200) ^ 21 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g17489 : 17489 ∈ P := S2 17489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17489 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 17489 g17489 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 17489 g17489 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 17489 g17489 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g17489 (by simp) (by norm_num : 3 ^ 1 ∣ 17489 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4412) h  -- d = 4412: 5 | 41179+1, 29+1
    rw [show (2:ℕ) ^ 4412 = (2 ^ 200) ^ 22 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g247073 : 247073 ∈ P := S2 247073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 247073 (by norm_num))
    have g41179 : 41179 ∈ P := S1 41179 (by norm_num) (by norm_num) (hnz (by norm_num)) 247073 g247073 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 41179 g41179 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 41179 g41179 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4436) h  -- d = 4436: 5 | 619+1, 612169+1
    rw [show (2:ℕ) ^ 4436 = (2 ^ 200) ^ 22 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g53233 : 53233 ∈ P := S2 53233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 53233 (by norm_num))
    have g619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 53233 g53233 (by norm_num)
    have g1224337 : 1224337 ∈ P := S2 1224337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1224337 (by norm_num))
    have g612169 : 612169 ∈ P := S1 612169 (by norm_num) (by norm_num) (hnz (by norm_num)) 1224337 g1224337 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 619 g619 612169 g612169 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4492) h  -- d = 4492: 13 | 215617+1, 8293+1
    rw [show (2:ℕ) ^ 4492 = (2 ^ 200) ^ 22 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g215617 : 215617 ∈ P := S2 215617 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 215617 (by norm_num))
    have g8293 : 8293 ∈ P := S1 8293 (by norm_num) (by norm_num) (hnz (by norm_num)) 215617 g215617 (by norm_num)
    exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 215617 g215617 8293 g8293 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4516) h  -- d = 4516: 7 | 1571569+1, 13+1
    rw [show (2:ℕ) ^ 4516 = (2 ^ 200) ^ 22 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1571569 : 1571569 ∈ P := S2 1571569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1571569 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1571569 g1571569 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1571569 g1571569 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4684) h  -- d = 4684: 5 | 56209+1, 19+1
    rw [show (2:ℕ) ^ 4684 = (2 ^ 200) ^ 23 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 23 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g56209 : 56209 ∈ P := S2 56209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 56209 (by norm_num))
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 56209 g56209 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 56209 g56209 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4868) h  -- d = 4868: 13^2 | 2044561+1
    rw [show (2:ℕ) ^ 4868 = (2 ^ 200) ^ 24 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 24 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2044561 : 2044561 ∈ P := S2 2044561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2044561 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2044561 g2044561 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4924) h  -- d = 4924: 7^2 | 19697+1
    rw [show (2:ℕ) ^ 4924 = (2 ^ 200) ^ 24 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 24 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g19697 : 19697 ∈ P := S2 19697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 19697 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 19697 g19697 (by norm_num)

theorem w52_v2_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({4996, 5036, 5108, 5116, 5188, 5204, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996, 6124, 6268, 6388, 6404, 6428, 6652, 6676} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4996) h  -- d = 4996: 5 | 19+1, 619+1
    rw [show (2:ℕ) ^ 4996 = (2 ^ 200) ^ 24 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 24 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1099121 : 1099121 ∈ P := S2 1099121 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1099121 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1099121 g1099121 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    have g4951 : 4951 ∈ P := S1 4951 (by norm_num) (by norm_num) (hnz (by norm_num)) 1099121 g1099121 (by norm_num)
    have g619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 4951 g4951 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 619 g619 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5036) h  -- d = 5036: 17 | 2^5036+1, 40289+1
    rw [show (2:ℕ) ^ 5036 = (2 ^ 200) ^ 25 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g40289 : 40289 ∈ P := S2 40289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 40289 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 40289 g40289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5108) h  -- d = 5108: 7 | 4903681+1, 41+1
    rw [show (2:ℕ) ^ 5108 = (2 ^ 200) ^ 25 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4903681 : 4903681 ∈ P := S2 4903681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4903681 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 4903681 g4903681 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4903681 g4903681 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5116) h  -- d = 5116: 3^8 | (2^5116+1) prod (p+1), p in {17, 1800833, 53, 809}
    rw [show (2:ℕ) ^ 5116 = (2 ^ 200) ^ 25 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g1800833 : 1800833 ∈ P := S2 1800833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1800833 (by norm_num))
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 1800833 g1800833 (by norm_num)
    have g809 : 809 ∈ P := S1 809 (by norm_num) (by norm_num) (hnz (by norm_num)) 1800833 g1800833 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g1800833 (by simp) (by norm_num : 3 ^ 1 ∣ 1800833 + 1)
    have b3 := bud_cons b2 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    have b4 := bud_cons b3 g809 (by simp) (by norm_num : 3 ^ 4 ∣ 809 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5188) h  -- d = 5188: 17^2 | 577+1
    rw [show (2:ℕ) ^ 5188 = (2 ^ 200) ^ 25 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20753 : 20753 ∈ P := S2 20753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20753 (by norm_num))
    have g1153 : 1153 ∈ P := S1 1153 (by norm_num) (by norm_num) (hnz (by norm_num)) 20753 g20753 (by norm_num)
    have g577 : 577 ∈ P := S1 577 (by norm_num) (by norm_num) (hnz (by norm_num)) 1153 g1153 (by norm_num)
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5204) h  -- d = 5204: 3^8 | (2^5204+1) prod (p+1), p in {17, 197, 317, 11, 53}
    rw [show (2:ℕ) ^ 5204 = (2 ^ 200) ^ 26 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 26 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g124897 : 124897 ∈ P := S2 124897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 124897 (by norm_num))
    have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 124897 g124897 (by norm_num)
    have g317 : 317 ∈ P := S1 317 (by norm_num) (by norm_num) (hnz (by norm_num)) 124897 g124897 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 197 g197 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g197 (by simp) (by norm_num : 3 ^ 2 ∣ 197 + 1)
    have b3 := bud_cons b2 g317 (by simp) (by norm_num : 3 ^ 1 ∣ 317 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5212) h  -- d = 5212: 5^2 | 20849+1
    rw [show (2:ℕ) ^ 5212 = (2 ^ 200) ^ 26 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 26 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20849 : 20849 ∈ P := S2 20849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 20849 g20849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5276) h  -- d = 5276: 17 | 2^5276+1, 67+1
    rw [show (2:ℕ) ^ 5276 = (2 ^ 200) ^ 26 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 26 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g42209 : 42209 ∈ P := S2 42209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42209 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 42209 g42209 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5308) h  -- d = 5308: 5 | 3588209+1, 39869+1
    rw [show (2:ℕ) ^ 5308 = (2 ^ 200) ^ 26 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 26 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3588209 : 3588209 ∈ P := S2 3588209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3588209 (by norm_num))
    have g39869 : 39869 ∈ P := S1 39869 (by norm_num) (by norm_num) (hnz (by norm_num)) 3588209 g3588209 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3588209 g3588209 39869 g39869 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5492) h  -- d = 5492: 11 | 14696593+1, 197+1
    rw [show (2:ℕ) ^ 5492 = (2 ^ 200) ^ 27 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 27 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14696593 : 14696593 ∈ P := S2 14696593 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14696593 (by norm_num))
    have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 14696593 g14696593 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 14696593 g14696593 197 g197 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5524) h  -- d = 5524: 11^2 | 15246241+1
    rw [show (2:ℕ) ^ 5524 = (2 ^ 200) ^ 27 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 27 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15246241 : 15246241 ∈ P := S2 15246241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15246241 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 15246241 g15246241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5716) h  -- d = 5716: 11^2 | 5081+1
    rw [show (2:ℕ) ^ 5716 = (2 ^ 200) ^ 28 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 28 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g91457 : 91457 ∈ P := S2 91457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 91457 (by norm_num))
    have g5081 : 5081 ∈ P := S1 5081 (by norm_num) (by norm_num) (hnz (by norm_num)) 91457 g91457 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 5081 g5081 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5732) h  -- d = 5732: 7 | 252209+1, 601+1
    rw [show (2:ℕ) ^ 5732 = (2 ^ 200) ^ 28 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 28 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g252209 : 252209 ∈ P := S2 252209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 252209 (by norm_num))
    have g1201 : 1201 ∈ P := S1 1201 (by norm_num) (by norm_num) (hnz (by norm_num)) 252209 g252209 (by norm_num)
    have g601 : 601 ∈ P := S1 601 (by norm_num) (by norm_num) (hnz (by norm_num)) 1201 g1201 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 252209 g252209 601 g601 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5804) h  -- d = 5804: 17^2 | 139297+1
    rw [show (2:ℕ) ^ 5804 = (2 ^ 200) ^ 29 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 29 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g139297 : 139297 ∈ P := S2 139297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 139297 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 139297 g139297 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5836) h  -- d = 5836: 7 | 2334401+1, 210097+1
    rw [show (2:ℕ) ^ 5836 = (2 ^ 200) ^ 29 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 29 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2334401 : 2334401 ∈ P := S2 2334401 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2334401 (by norm_num))
    have g420193 : 420193 ∈ P := S2 420193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 420193 (by norm_num))
    have g210097 : 210097 ∈ P := S1 210097 (by norm_num) (by norm_num) (hnz (by norm_num)) 420193 g420193 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2334401 g2334401 210097 g210097 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5932) h  -- d = 5932: 5 | 142369+1, 619+1
    rw [show (2:ℕ) ^ 5932 = (2 ^ 200) ^ 29 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 29 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g142369 : 142369 ∈ P := S2 142369 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 142369 (by norm_num))
    have g619 : 619 ∈ P := S1 619 (by norm_num) (by norm_num) (hnz (by norm_num)) 142369 g142369 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 142369 g142369 619 g619 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5948) h  -- d = 5948: 7^2 | 214129+1
    rw [show (2:ℕ) ^ 5948 = (2 ^ 200) ^ 29 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 29 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g214129 : 214129 ∈ P := S2 214129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 214129 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 214129 g214129 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5996) h  -- d = 5996: 7^2 | 97+1
    rw [show (2:ℕ) ^ 5996 = (2 ^ 200) ^ 29 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 29 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1487009 : 1487009 ∈ P := S2 1487009 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1487009 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 1487009 g1487009 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6124) h  -- d = 6124: 7^2 | 612401+1
    rw [show (2:ℕ) ^ 6124 = (2 ^ 200) ^ 30 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 30 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g612401 : 612401 ∈ P := S2 612401 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 612401 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 612401 g612401 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6268) h  -- d = 6268: 5^2 | 199+1
    rw [show (2:ℕ) ^ 6268 = (2 ^ 200) ^ 31 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 31 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g25073 : 25073 ∈ P := S2 25073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 25073 (by norm_num))
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 25073 g25073 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6388) h  -- d = 6388: 7 | 153313+1, 13+1
    rw [show (2:ℕ) ^ 6388 = (2 ^ 200) ^ 31 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 31 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g153313 : 153313 ∈ P := S2 153313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 153313 (by norm_num))
    have g233 : 233 ∈ P := S1 233 (by norm_num) (by norm_num) (hnz (by norm_num)) 153313 g153313 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 233 g233 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 153313 g153313 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6404) h  -- d = 6404: 5 | 370009+1, 19+1
    rw [show (2:ℕ) ^ 6404 = (2 ^ 200) ^ 32 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 32 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6660161 : 6660161 ∈ P := S2 6660161 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6660161 (by norm_num))
    have g370009 : 370009 ∈ P := S1 370009 (by norm_num) (by norm_num) (hnz (by norm_num)) 6660161 g6660161 (by norm_num)
    have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 370009 g370009 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 370009 g370009 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6428) h  -- d = 6428: 5 | 38569+1, 19+1
    rw [show (2:ℕ) ^ 6428 = (2 ^ 200) ^ 32 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 32 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g77137 : 77137 ∈ P := S2 77137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 77137 (by norm_num))
    have g38569 : 38569 ∈ P := S1 38569 (by norm_num) (by norm_num) (hnz (by norm_num)) 77137 g77137 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 38569 g38569 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 38569 g38569 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6652) h  -- d = 6652: 17 | 2^6652+1, 67+1
    rw [show (2:ℕ) ^ 6652 = (2 ^ 200) ^ 33 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 33 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38421953 : 38421953 ∈ P := S2 38421953 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38421953 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 38421953 g38421953 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6676) h  -- d = 6676: 127 | 386587+1, 761+1
    rw [show (2:ℕ) ^ 6676 = (2 ^ 200) ^ 33 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 33 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33246481 : 33246481 ∈ P := S2 33246481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33246481 (by norm_num))
    have g386587 : 386587 ∈ P := S1 386587 (by norm_num) (by norm_num) (hnz (by norm_num)) 33246481 g33246481 (by norm_num)
    have g761 : 761 ∈ P := S1 761 (by norm_num) (by norm_num) (hnz (by norm_num)) 386587 g386587 (by norm_num)
    exact absurd (S3 127 (by norm_num) (by norm_num) (hnz (by norm_num)) 386587 g386587 761 g761 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v2_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324, 8332, 8396, 8452, 8524, 8612, 8644, 8812} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6884) h  -- d = 6884: 5^2 | 349+1
    rw [show (2:ℕ) ^ 6884 = (2 ^ 200) ^ 34 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 34 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g550721 : 550721 ∈ P := S2 550721 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 550721 (by norm_num))
    have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 550721 g550721 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 349 g349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6932) h  -- d = 6932: 5 | 29+1, 19+1
    rw [show (2:ℕ) ^ 6932 = (2 ^ 200) ^ 34 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 34 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1996417 : 1996417 ∈ P := S2 1996417 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1996417 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1996417 g1996417 (by norm_num)
    have g34421 : 34421 ∈ P := S1 34421 (by norm_num) (by norm_num) (hnz (by norm_num)) 1996417 g1996417 (by norm_num)
    have g5737 : 5737 ∈ P := S1 5737 (by norm_num) (by norm_num) (hnz (by norm_num)) 34421 g34421 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 5737 g5737 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7108) h  -- d = 7108: 5^2 | 42649+1
    rw [show (2:ℕ) ^ 7108 = (2 ^ 200) ^ 35 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 35 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g85297 : 85297 ∈ P := S2 85297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 85297 (by norm_num))
    have g42649 : 42649 ∈ P := S1 42649 (by norm_num) (by norm_num) (hnz (by norm_num)) 85297 g85297 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 42649 g42649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7132) h  -- d = 7132: 17 | 2^7132+1, 67+1
    rw [show (2:ℕ) ^ 7132 = (2 ^ 200) ^ 35 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 35 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g199697 : 199697 ∈ P := S2 199697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 199697 (by norm_num))
    have g401 : 401 ∈ P := S1 401 (by norm_num) (by norm_num) (hnz (by norm_num)) 199697 g199697 (by norm_num)
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 401 g401 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7324) h  -- d = 7324: 5 | 19+1, 389+1
    rw [show (2:ℕ) ^ 7324 = (2 ^ 200) ^ 36 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 36 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29297 : 29297 ∈ P := S2 29297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29297 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 29297 g29297 (by norm_num)
    have g39461713 : 39461713 ∈ P := S2 39461713 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39461713 (by norm_num))
    have g19730857 : 19730857 ∈ P := S1 19730857 (by norm_num) (by norm_num) (hnz (by norm_num)) 39461713 g39461713 (by norm_num)
    have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 19730857 g19730857 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 389 g389 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7444) h  -- d = 7444: 5^2 | 1429249+1
    rw [show (2:ℕ) ^ 7444 = (2 ^ 200) ^ 37 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 37 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1429249 : 1429249 ∈ P := S2 1429249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1429249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1429249 g1429249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7516) h  -- d = 7516: 7^2 | 270577+1
    rw [show (2:ℕ) ^ 7516 = (2 ^ 200) ^ 37 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 37 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g270577 : 270577 ∈ P := S2 270577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 270577 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 270577 g270577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7556) h  -- d = 7556: 5^2 | 60449+1
    rw [show (2:ℕ) ^ 7556 = (2 ^ 200) ^ 37 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 37 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g60449 : 60449 ∈ P := S2 60449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 60449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 60449 g60449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7796) h  -- d = 7796: 17 | 2^7796+1, 21589+1
    rw [show (2:ℕ) ^ 7796 = (2 ^ 200) ^ 38 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 38 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g561313 : 561313 ∈ P := S2 561313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 561313 (by norm_num))
    have g21589 : 21589 ∈ P := S1 21589 (by norm_num) (by norm_num) (hnz (by norm_num)) 561313 g561313 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 21589 g21589 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7804) h  -- d = 7804: 5 | 19+1, 109+1
    rw [show (2:ℕ) ^ 7804 = (2 ^ 200) ^ 39 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5993473 : 5993473 ∈ P := S2 5993473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5993473 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 5993473 g5993473 (by norm_num)
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 5993473 g5993473 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 109 g109 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7892) h  -- d = 7892: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 7892 = (2 ^ 200) ^ 39 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8586497 : 8586497 ∈ P := S2 8586497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8586497 (by norm_num))
    have g1447 : 1447 ∈ P := S1 1447 (by norm_num) (by norm_num) (hnz (by norm_num)) 8586497 g8586497 (by norm_num)
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 1447 g1447 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7916) h  -- d = 7916: 5 | 79+1, 19+1
    rw [show (2:ℕ) ^ 7916 = (2 ^ 200) ^ 39 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11177393 : 11177393 ∈ P := S2 11177393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11177393 (by norm_num))
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 11177393 g11177393 (by norm_num)
    have g23581 : 23581 ∈ P := S1 23581 (by norm_num) (by norm_num) (hnz (by norm_num)) 11177393 g11177393 (by norm_num)
    have g907 : 907 ∈ P := S1 907 (by norm_num) (by norm_num) (hnz (by norm_num)) 23581 g23581 (by norm_num)
    have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 907 g907 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 79 g79 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7948) h  -- d = 7948: 5 | 379+1, 19+1
    rw [show (2:ℕ) ^ 7948 = (2 ^ 200) ^ 39 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g31793 : 31793 ∈ P := S2 31793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31793 (by norm_num))
    have g757 : 757 ∈ P := S1 757 (by norm_num) (by norm_num) (hnz (by norm_num)) 31793 g31793 (by norm_num)
    have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 757 g757 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 379 g379 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7988) h  -- d = 7988: 5 | 18180689+1, 1489+1
    rw [show (2:ℕ) ^ 7988 = (2 ^ 200) ^ 39 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g18180689 : 18180689 ∈ P := S2 18180689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 18180689 (by norm_num))
    have g1489 : 1489 ∈ P := S1 1489 (by norm_num) (by norm_num) (hnz (by norm_num)) 18180689 g18180689 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 18180689 g18180689 1489 g1489 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7996) h  -- d = 7996: 5 | 239+1, 29+1
    rw [show (2:ℕ) ^ 7996 = (2 ^ 200) ^ 39 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 39 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41867057 : 41867057 ∈ P := S2 41867057 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41867057 (by norm_num))
    have g6977843 : 6977843 ∈ P := S1 6977843 (by norm_num) (by norm_num) (hnz (by norm_num)) 41867057 g41867057 (by norm_num)
    have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 6977843 g6977843 (by norm_num)
    have g811 : 811 ∈ P := S1 811 (by norm_num) (by norm_num) (hnz (by norm_num)) 6977843 g6977843 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 811 g811 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 239 g239 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8212) h  -- d = 8212: 5 | 197089+1, 19709+1
    rw [show (2:ℕ) ^ 8212 = (2 ^ 200) ^ 41 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 41 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g197089 : 197089 ∈ P := S2 197089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 197089 (by norm_num))
    have g19709 : 19709 ∈ P := S1 19709 (by norm_num) (by norm_num) (hnz (by norm_num)) 197089 g197089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197089 g197089 19709 g19709 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8276) h  -- d = 8276: 5 | 8507729+1, 29+1
    rw [show (2:ℕ) ^ 8276 = (2 ^ 200) ^ 41 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 41 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8507729 : 8507729 ∈ P := S2 8507729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8507729 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 8507729 g8507729 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8507729 g8507729 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8324) h  -- d = 8324: 17 | 2^8324+1, 101+1
    rw [show (2:ℕ) ^ 8324 = (2 ^ 200) ^ 41 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 41 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g66593 : 66593 ∈ P := S2 66593 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 66593 (by norm_num))
    have g1009 : 1009 ∈ P := S1 1009 (by norm_num) (by norm_num) (hnz (by norm_num)) 66593 g66593 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 1009 g1009 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 101 g101 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8332) h  -- d = 8332: 17 | 2^8332+1, 101+1
    rw [show (2:ℕ) ^ 8332 = (2 ^ 200) ^ 41 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 41 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33329 : 33329 ∈ P := S2 33329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33329 (by norm_num))
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 33329 g33329 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 101 g101 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8396) h  -- d = 8396: 5 | 2585969+1, 59+1
    rw [show (2:ℕ) ^ 8396 = (2 ^ 200) ^ 41 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 41 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2585969 : 2585969 ∈ P := S2 2585969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2585969 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 2585969 g2585969 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2585969 g2585969 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8452) h  -- d = 8452: 7^2 | 33809+1
    rw [show (2:ℕ) ^ 8452 = (2 ^ 200) ^ 42 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 42 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g33809 : 33809 ∈ P := S2 33809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 33809 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 33809 g33809 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8524) h  -- d = 8524: 13^2 | 3041+1
    rw [show (2:ℕ) ^ 8524 = (2 ^ 200) ^ 42 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 42 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1125169 : 1125169 ∈ P := S2 1125169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1125169 (by norm_num))
    have g3041 : 3041 ∈ P := S1 3041 (by norm_num) (by norm_num) (hnz (by norm_num)) 1125169 g1125169 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3041 g3041 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8612) h  -- d = 8612: 3^8 | (2^8612+1) prod (p+1), p in {17, 68897, 11483, 11, 29, 5}
    rw [show (2:ℕ) ^ 8612 = (2 ^ 200) ^ 43 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 43 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g68897 : 68897 ∈ P := S2 68897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 68897 (by norm_num))
    have g11483 : 11483 ∈ P := S1 11483 (by norm_num) (by norm_num) (hnz (by norm_num)) 68897 g68897 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 11483 g11483 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 11483 g11483 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g68897 (by simp) (by norm_num : 3 ^ 1 ∣ 68897 + 1)
    have b3 := bud_cons b2 g11483 (by simp) (by norm_num : 3 ^ 2 ∣ 11483 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b6 := bud_cons b5 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8644) h  -- d = 8644: 3^8 | (2^8644+1) prod (p+1), p in {17, 28559777, 47, 2207, 227, 1613, 23}
    rw [show (2:ℕ) ^ 8644 = (2 ^ 200) ^ 43 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 43 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g28559777 : 28559777 ∈ P := S2 28559777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28559777 (by norm_num))
    have g207457 : 207457 ∈ P := S2 207457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 207457 (by norm_num))
    have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 207457 g207457 (by norm_num)
    have g2207 : 2207 ∈ P := S1 2207 (by norm_num) (by norm_num) (hnz (by norm_num)) 207457 g207457 (by norm_num)
    have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 28559777 g28559777 (by norm_num)
    have g1613 : 1613 ∈ P := S1 1613 (by norm_num) (by norm_num) (hnz (by norm_num)) 28559777 g28559777 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2207 g2207 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g28559777 (by simp) (by norm_num : 3 ^ 1 ∣ 28559777 + 1)
    have b3 := bud_cons b2 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
    have b4 := bud_cons b3 g2207 (by simp) (by norm_num : 3 ^ 1 ∣ 2207 + 1)
    have b5 := bud_cons b4 g227 (by simp) (by norm_num : 3 ^ 1 ∣ 227 + 1)
    have b6 := bud_cons b5 g1613 (by simp) (by norm_num : 3 ^ 1 ∣ 1613 + 1)
    have b7 := bud_cons b6 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b7.1 ((pow_dvd_pow 3 (by norm_num)).trans b7.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8812) h  -- d = 8812: 5 | 4519+1, 19+1
    rw [show (2:ℕ) ^ 8812 = (2 ^ 200) ^ 44 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 44 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g352481 : 352481 ∈ P := S2 352481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 352481 (by norm_num))
    have g4519 : 4519 ∈ P := S1 4519 (by norm_num) (by norm_num) (hnz (by norm_num)) 352481 g352481 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 4519 g4519 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4519 g4519 19 g19 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v2_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10684, 10732, 10796, 10876, 10916, 10924, 11156} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8852) h  -- d = 8852: 17 | 2^8852+1, 82619+1
    rw [show (2:ℕ) ^ 8852 = (2 ^ 200) ^ 44 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 44 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g495713 : 495713 ∈ P := S2 495713 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 495713 (by norm_num))
    have g82619 : 82619 ∈ P := S1 82619 (by norm_num) (by norm_num) (hnz (by norm_num)) 495713 g495713 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 82619 g82619 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9068) h  -- d = 9068: 5^2 | 326449+1
    rw [show (2:ℕ) ^ 9068 = (2 ^ 200) ^ 45 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 45 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g326449 : 326449 ∈ P := S2 326449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 326449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 326449 g326449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9124) h  -- d = 9124: 7 | 36497+1, 547441+1
    rw [show (2:ℕ) ^ 9124 = (2 ^ 200) ^ 45 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 45 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g36497 : 36497 ∈ P := S2 36497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 36497 (by norm_num))
    have g547441 : 547441 ∈ P := S2 547441 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 547441 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 36497 g36497 547441 g547441 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9172) h  -- d = 9172: 5 | 1137329+1, 89+1
    rw [show (2:ℕ) ^ 9172 = (2 ^ 200) ^ 45 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 45 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1137329 : 1137329 ∈ P := S2 1137329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1137329 (by norm_num))
    have g12637 : 12637 ∈ P := S1 12637 (by norm_num) (by norm_num) (hnz (by norm_num)) 1137329 g1137329 (by norm_num)
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 12637 g12637 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1137329 g1137329 89 g89 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9388) h  -- d = 9388: 7 | 112657+1, 13+1
    rw [show (2:ℕ) ^ 9388 = (2 ^ 200) ^ 46 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 46 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g112657 : 112657 ∈ P := S2 112657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 112657 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 112657 g112657 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 112657 g112657 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9572) h  -- d = 9572: 5^2 | 5590049+1
    rw [show (2:ℕ) ^ 9572 = (2 ^ 200) ^ 47 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 47 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5590049 : 5590049 ∈ P := S2 5590049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5590049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5590049 g5590049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9692) h  -- d = 9692: 11^2 | 193841+1
    rw [show (2:ℕ) ^ 9692 = (2 ^ 200) ^ 48 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 48 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g193841 : 193841 ∈ P := S2 193841 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 193841 (by norm_num))
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 193841 g193841 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9748) h  -- d = 9748: 17 | 2^9748+1, 67+1
    rw [show (2:ℕ) ^ 9748 = (2 ^ 200) ^ 48 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 48 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38993 : 38993 ∈ P := S2 38993 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38993 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 38993 g38993 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9788) h  -- d = 9788: 5 | 59+1, 79+1
    rw [show (2:ℕ) ^ 9788 = (2 ^ 200) ^ 48 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 48 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g195761 : 195761 ∈ P := S2 195761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 195761 (by norm_num))
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 195761 g195761 (by norm_num)
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 195761 g195761 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9892) h  -- d = 9892: 5 | 39569+1, 1319+1
    rw [show (2:ℕ) ^ 9892 = (2 ^ 200) ^ 49 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 49 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39569 : 39569 ∈ P := S2 39569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39569 (by norm_num))
    have g1319 : 1319 ∈ P := S1 1319 (by norm_num) (by norm_num) (hnz (by norm_num)) 39569 g39569 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 39569 g39569 1319 g1319 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9908) h  -- d = 9908: 5^2 | 349+1
    rw [show (2:ℕ) ^ 9908 = (2 ^ 200) ^ 49 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 49 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2694977 : 2694977 ∈ P := S2 2694977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2694977 (by norm_num))
    have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 2694977 g2694977 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 349 g349 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10012) h  -- d = 10012: 7^2 | 293+1
    rw [show (2:ℕ) ^ 10012 = (2 ^ 200) ^ 50 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 50 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g400481 : 400481 ∈ P := S2 400481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 400481 (by norm_num))
    have g1171 : 1171 ∈ P := S1 1171 (by norm_num) (by norm_num) (hnz (by norm_num)) 400481 g400481 (by norm_num)
    have g293 : 293 ∈ P := S1 293 (by norm_num) (by norm_num) (hnz (by norm_num)) 1171 g1171 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10084) h  -- d = 10084: 5 | 1129409+1, 7986529+1
    rw [show (2:ℕ) ^ 10084 = (2 ^ 200) ^ 50 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 50 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1129409 : 1129409 ∈ P := S2 1129409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1129409 (by norm_num))
    have g7986529 : 7986529 ∈ P := S2 7986529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7986529 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1129409 g1129409 7986529 g7986529 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10172) h  -- d = 10172: 11 | 43+1, 54251+1
    rw [show (2:ℕ) ^ 10172 = (2 ^ 200) ^ 50 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 50 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g691697 : 691697 ∈ P := S2 691697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 691697 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 691697 g691697 (by norm_num)
    have g1302017 : 1302017 ∈ P := S2 1302017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1302017 (by norm_num))
    have g217003 : 217003 ∈ P := S1 217003 (by norm_num) (by norm_num) (hnz (by norm_num)) 1302017 g1302017 (by norm_num)
    have g54251 : 54251 ∈ P := S1 54251 (by norm_num) (by norm_num) (hnz (by norm_num)) 217003 g217003 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 54251 g54251 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10204) h  -- d = 10204: 5^2 | 149+1
    rw [show (2:ℕ) ^ 10204 = (2 ^ 200) ^ 51 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 51 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1224481 : 1224481 ∈ P := S2 1224481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1224481 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 1224481 g1224481 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10228) h  -- d = 10228: 17 | 2^10228+1, 883+1
    rw [show (2:ℕ) ^ 10228 = (2 ^ 200) ^ 51 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 51 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g245473 : 245473 ∈ P := S2 245473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 245473 (by norm_num))
    have g883 : 883 ∈ P := S1 883 (by norm_num) (by norm_num) (hnz (by norm_num)) 245473 g245473 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 883 g883 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10532) h  -- d = 10532: 5 | 719+1, 19+1
    rw [show (2:ℕ) ^ 10532 = (2 ^ 200) ^ 52 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 52 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1137457 : 1137457 ∈ P := S2 1137457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1137457 (by norm_num))
    have g719 : 719 ∈ P := S1 719 (by norm_num) (by norm_num) (hnz (by norm_num)) 1137457 g1137457 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 1137457 g1137457 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 719 g719 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10588) h  -- d = 10588: 5 | 169409+1, 59+1
    rw [show (2:ℕ) ^ 10588 = (2 ^ 200) ^ 52 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 52 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g169409 : 169409 ∈ P := S2 169409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 169409 (by norm_num))
    have g5647 : 5647 ∈ P := S1 5647 (by norm_num) (by norm_num) (hnz (by norm_num)) 169409 g169409 (by norm_num)
    have g353 : 353 ∈ P := S1 353 (by norm_num) (by norm_num) (hnz (by norm_num)) 5647 g5647 (by norm_num)
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 353 g353 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 169409 g169409 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10684) h  -- d = 10684: 3^8 | (2^10684+1) prod (p+1), p in {17, 683777, 113963, 9497, 1583, 11}
    rw [show (2:ℕ) ^ 10684 = (2 ^ 200) ^ 53 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 53 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g683777 : 683777 ∈ P := S2 683777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 683777 (by norm_num))
    have g113963 : 113963 ∈ P := S1 113963 (by norm_num) (by norm_num) (hnz (by norm_num)) 683777 g683777 (by norm_num)
    have g9497 : 9497 ∈ P := S1 9497 (by norm_num) (by norm_num) (hnz (by norm_num)) 113963 g113963 (by norm_num)
    have g1583 : 1583 ∈ P := S1 1583 (by norm_num) (by norm_num) (hnz (by norm_num)) 9497 g9497 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1583 g1583 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g683777 (by simp) (by norm_num : 3 ^ 1 ∣ 683777 + 1)
    have b3 := bud_cons b2 g113963 (by simp) (by norm_num : 3 ^ 1 ∣ 113963 + 1)
    have b4 := bud_cons b3 g9497 (by simp) (by norm_num : 3 ^ 1 ∣ 9497 + 1)
    have b5 := bud_cons b4 g1583 (by simp) (by norm_num : 3 ^ 2 ∣ 1583 + 1)
    have b6 := bud_cons b5 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10732) h  -- d = 10732: 3^8 | (2^10732+1) prod (p+1), p in {17, 42929, 5, 53}
    rw [show (2:ℕ) ^ 10732 = (2 ^ 200) ^ 53 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 53 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g42929 : 42929 ∈ P := S2 42929 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 42929 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 42929 g42929 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 42929 g42929 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g42929 (by simp) (by norm_num : 3 ^ 4 ∣ 42929 + 1)
    have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10796) h  -- d = 10796: 17 | 2^10796+1, 345473+1
    rw [show (2:ℕ) ^ 10796 = (2 ^ 200) ^ 53 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 53 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g345473 : 345473 ∈ P := S2 345473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 345473 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 345473 g345473 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10876) h  -- d = 10876: 7 | 1305121+1, 13+1
    rw [show (2:ℕ) ^ 10876 = (2 ^ 200) ^ 54 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 54 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1305121 : 1305121 ∈ P := S2 1305121 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1305121 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1305121 g1305121 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1305121 g1305121 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10916) h  -- d = 10916: 5 | 742289+1, 109+1
    rw [show (2:ℕ) ^ 10916 = (2 ^ 200) ^ 54 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 54 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g742289 : 742289 ∈ P := S2 742289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 742289 (by norm_num))
    have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 742289 g742289 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 742289 g742289 109 g109 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10924) h  -- d = 10924: 5 | 297469+1, 19+1
    rw [show (2:ℕ) ^ 10924 = (2 ^ 200) ^ 54 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 54 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7734193 : 7734193 ∈ P := S2 7734193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7734193 (by norm_num))
    have g297469 : 297469 ∈ P := S1 297469 (by norm_num) (by norm_num) (hnz (by norm_num)) 7734193 g7734193 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 297469 g297469 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 297469 g297469 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11156) h  -- d = 11156: 17 | 2^11156+1, 271+1
    rw [show (2:ℕ) ^ 11156 = (2 ^ 200) ^ 55 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 55 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g133873 : 133873 ∈ P := S2 133873 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 133873 (by norm_num))
    have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 133873 g133873 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 271 g271 (by norm_num)

theorem w52_v2_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({11164, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228, 13316, 13444, 13484} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11164) h  -- d = 11164: 3^8 | (2^11164+1) prod (p+1), p in {17, 44657, 827, 23}
    rw [show (2:ℕ) ^ 11164 = (2 ^ 200) ^ 55 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 55 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g44657 : 44657 ∈ P := S2 44657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44657 (by norm_num))
    have g827 : 827 ∈ P := S1 827 (by norm_num) (by norm_num) (hnz (by norm_num)) 44657 g44657 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 827 g827 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g44657 (by simp) (by norm_num : 3 ^ 3 ∣ 44657 + 1)
    have b3 := bud_cons b2 g827 (by simp) (by norm_num : 3 ^ 2 ∣ 827 + 1)
    have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11188) h  -- d = 11188: 5 | 7459+1, 67129+1
    rw [show (2:ℕ) ^ 11188 = (2 ^ 200) ^ 55 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 55 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g44753 : 44753 ∈ P := S2 44753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 44753 (by norm_num))
    have g7459 : 7459 ∈ P := S1 7459 (by norm_num) (by norm_num) (hnz (by norm_num)) 44753 g44753 (by norm_num)
    have g134257 : 134257 ∈ P := S2 134257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 134257 (by norm_num))
    have g67129 : 67129 ∈ P := S1 67129 (by norm_num) (by norm_num) (hnz (by norm_num)) 134257 g134257 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7459 g7459 67129 g67129 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11276) h  -- d = 11276: 5^2 | 541249+1
    rw [show (2:ℕ) ^ 11276 = (2 ^ 200) ^ 56 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 56 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g541249 : 541249 ∈ P := S2 541249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 541249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 541249 g541249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11516) h  -- d = 11516: 7^2 | 587+1
    rw [show (2:ℕ) ^ 11516 = (2 ^ 200) ^ 57 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 57 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13082177 : 13082177 ∈ P := S2 13082177 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13082177 (by norm_num))
    have g2347 : 2347 ∈ P := S1 2347 (by norm_num) (by norm_num) (hnz (by norm_num)) 13082177 g13082177 (by norm_num)
    have g587 : 587 ∈ P := S1 587 (by norm_num) (by norm_num) (hnz (by norm_num)) 2347 g2347 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 587 g587 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11548) h  -- d = 11548: 5^2 | 6299+1
    rw [show (2:ℕ) ^ 11548 = (2 ^ 200) ^ 57 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 57 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g138577 : 138577 ∈ P := S2 138577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 138577 (by norm_num))
    have g6299 : 6299 ∈ P := S1 6299 (by norm_num) (by norm_num) (hnz (by norm_num)) 138577 g138577 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6299 g6299 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11612) h  -- d = 11612: 5^2 | 1207649+1
    rw [show (2:ℕ) ^ 11612 = (2 ^ 200) ^ 58 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 58 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1207649 : 1207649 ∈ P := S2 1207649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1207649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1207649 g1207649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11636) h  -- d = 11636: 5 | 93089+1, 29+1
    rw [show (2:ℕ) ^ 11636 = (2 ^ 200) ^ 58 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 58 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g93089 : 93089 ∈ P := S2 93089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 93089 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 93089 g93089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 93089 g93089 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11668) h  -- d = 11668: 5 | 4387169+1, 146239+1
    rw [show (2:ℕ) ^ 11668 = (2 ^ 200) ^ 58 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 58 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4387169 : 4387169 ∈ P := S2 4387169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4387169 (by norm_num))
    have g146239 : 146239 ∈ P := S1 146239 (by norm_num) (by norm_num) (hnz (by norm_num)) 4387169 g4387169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4387169 g4387169 146239 g146239 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11812) h  -- d = 11812: 7^2 | 97+1
    rw [show (2:ℕ) ^ 11812 = (2 ^ 200) ^ 59 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 59 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5433521 : 5433521 ∈ P := S2 5433521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5433521 (by norm_num))
    have g905587 : 905587 ∈ P := S1 905587 (by norm_num) (by norm_num) (hnz (by norm_num)) 5433521 g5433521 (by norm_num)
    have g226397 : 226397 ∈ P := S1 226397 (by norm_num) (by norm_num) (hnz (by norm_num)) 905587 g905587 (by norm_num)
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 226397 g226397 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12004) h  -- d = 12004: 5 | 19+1, 59+1
    rw [show (2:ℕ) ^ 12004 = (2 ^ 200) ^ 60 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 60 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g576193 : 576193 ∈ P := S2 576193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 576193 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 576193 g576193 (by norm_num)
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 576193 g576193 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12044) h  -- d = 12044: 7^2 | 29628241+1
    rw [show (2:ℕ) ^ 12044 = (2 ^ 200) ^ 60 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 60 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29628241 : 29628241 ∈ P := S2 29628241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29628241 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 29628241 g29628241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12076) h  -- d = 12076: 5^2 | 449+1
    rw [show (2:ℕ) ^ 12076 = (2 ^ 200) ^ 60 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 60 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2077073 : 2077073 ∈ P := S2 2077073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2077073 (by norm_num))
    have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 2077073 g2077073 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12148) h  -- d = 12148: 11 | 728881+1, 263+1
    rw [show (2:ℕ) ^ 12148 = (2 ^ 200) ^ 60 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 60 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g728881 : 728881 ∈ P := S2 728881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 728881 (by norm_num))
    have g4733 : 4733 ∈ P := S1 4733 (by norm_num) (by norm_num) (hnz (by norm_num)) 728881 g728881 (by norm_num)
    have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (hnz (by norm_num)) 4733 g4733 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 728881 g728881 263 g263 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12356) h  -- d = 12356: 5^2 | 98849+1
    rw [show (2:ℕ) ^ 12356 = (2 ^ 200) ^ 61 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 61 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g98849 : 98849 ∈ P := S2 98849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 98849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 98849 g98849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12484) h  -- d = 12484: 7 | 49937+1, 41+1
    rw [show (2:ℕ) ^ 12484 = (2 ^ 200) ^ 62 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 62 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g49937 : 49937 ∈ P := S2 49937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 49937 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 49937 g49937 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 49937 g49937 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12668) h  -- d = 12668: 17 | 2^12668+1, 709409+1
    rw [show (2:ℕ) ^ 12668 = (2 ^ 200) ^ 63 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 63 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g709409 : 709409 ∈ P := S2 709409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 709409 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 709409 g709409 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12724) h  -- d = 12724: 5 | 4733329+1, 67619+1
    rw [show (2:ℕ) ^ 12724 = (2 ^ 200) ^ 63 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 63 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g9466657 : 9466657 ∈ P := S2 9466657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9466657 (by norm_num))
    have g4733329 : 4733329 ∈ P := S1 4733329 (by norm_num) (by norm_num) (hnz (by norm_num)) 9466657 g9466657 (by norm_num)
    have g67619 : 67619 ∈ P := S1 67619 (by norm_num) (by norm_num) (hnz (by norm_num)) 4733329 g4733329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4733329 g4733329 67619 g67619 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12748) h  -- d = 12748: 3^8 | (2^12748+1) prod (p+1), p in {17, 1733729, 4487297, 5, 57791, 53}
    rw [show (2:ℕ) ^ 12748 = (2 ^ 200) ^ 63 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 63 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g1733729 : 1733729 ∈ P := S2 1733729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1733729 (by norm_num))
    have g4487297 : 4487297 ∈ P := S2 4487297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4487297 (by norm_num))
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733729 g1733729 (by norm_num)
    have g57791 : 57791 ∈ P := S1 57791 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733729 g1733729 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 4487297 g4487297 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g1733729 (by simp) (by norm_num : 3 ^ 1 ∣ 1733729 + 1)
    have b3 := bud_cons b2 g4487297 (by simp) (by norm_num : 3 ^ 1 ∣ 4487297 + 1)
    have b4 := bud_cons b3 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b5 := bud_cons b4 g57791 (by simp) (by norm_num : 3 ^ 1 ∣ 57791 + 1)
    have b6 := bud_cons b5 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12868) h  -- d = 12868: 17 | 2^12868+1, 373+1
    rw [show (2:ℕ) ^ 12868 = (2 ^ 200) ^ 64 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 64 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g51473 : 51473 ∈ P := S2 51473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 51473 (by norm_num))
    have g373 : 373 ∈ P := S1 373 (by norm_num) (by norm_num) (hnz (by norm_num)) 51473 g51473 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 373 g373 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13004) h  -- d = 13004: 23^2 | 7906433+1
    rw [show (2:ℕ) ^ 13004 = (2 ^ 200) ^ 65 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 65 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7906433 : 7906433 ∈ P := S2 7906433 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7906433 (by norm_num))
    exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 7906433 g7906433 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13204) h  -- d = 13204: 17 | 2^13204+1, 3327409+1
    rw [show (2:ℕ) ^ 13204 = (2 ^ 200) ^ 66 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 66 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3327409 : 3327409 ∈ P := S2 3327409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3327409 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 3327409 g3327409 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13228) h  -- d = 13228: 5 | 7354769+1, 4019+1
    rw [show (2:ℕ) ^ 13228 = (2 ^ 200) ^ 66 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 66 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7354769 : 7354769 ∈ P := S2 7354769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7354769 (by norm_num))
    have g4019 : 4019 ∈ P := S1 4019 (by norm_num) (by norm_num) (hnz (by norm_num)) 7354769 g7354769 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7354769 g7354769 4019 g4019 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13316) h  -- d = 13316: 5^2 | 1704449+1
    rw [show (2:ℕ) ^ 13316 = (2 ^ 200) ^ 66 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 66 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1704449 : 1704449 ∈ P := S2 1704449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1704449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1704449 g1704449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13444) h  -- d = 13444: 11 | 307+1, 263+1
    rw [show (2:ℕ) ^ 13444 = (2 ^ 200) ^ 67 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 67 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g645313 : 645313 ∈ P := S2 645313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 645313 (by norm_num))
    have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 645313 g645313 (by norm_num)
    have g1051 : 1051 ∈ P := S1 1051 (by norm_num) (by norm_num) (hnz (by norm_num)) 645313 g645313 (by norm_num)
    have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (hnz (by norm_num)) 1051 g1051 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 307 g307 263 g263 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13484) h  -- d = 13484: 7 | 13+1, 461+1
    rw [show (2:ℕ) ^ 13484 = (2 ^ 200) ^ 67 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 67 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g107873 : 107873 ∈ P := S2 107873 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 107873 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 107873 g107873 (by norm_num)
    have g461 : 461 ∈ P := S1 461 (by norm_num) (by norm_num) (hnz (by norm_num)) 107873 g107873 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 461 g461 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v2_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14804, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692, 15724, 15772} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13564) h  -- d = 13564: 5 | 139+1, 919+1
    rw [show (2:ℕ) ^ 13564 = (2 ^ 200) ^ 67 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 67 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g325537 : 325537 ∈ P := S2 325537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 325537 (by norm_num))
    have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 325537 g325537 (by norm_num)
    have g11393761 : 11393761 ∈ P := S2 11393761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11393761 (by norm_num))
    have g919 : 919 ∈ P := S1 919 (by norm_num) (by norm_num) (hnz (by norm_num)) 11393761 g11393761 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 139 g139 919 g919 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13796) h  -- d = 13796: 5 | 15329+1, 19+1
    rw [show (2:ℕ) ^ 13796 = (2 ^ 200) ^ 68 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 68 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g275921 : 275921 ∈ P := S2 275921 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 275921 (by norm_num))
    have g15329 : 15329 ∈ P := S1 15329 (by norm_num) (by norm_num) (hnz (by norm_num)) 275921 g275921 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 15329 g15329 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 15329 g15329 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13852) h  -- d = 13852: 17 | 2^13852+1, 509+1
    rw [show (2:ℕ) ^ 13852 = (2 ^ 200) ^ 69 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 69 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g387857 : 387857 ∈ P := S2 387857 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 387857 (by norm_num))
    have g509 : 509 ∈ P := S1 509 (by norm_num) (by norm_num) (hnz (by norm_num)) 387857 g387857 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 509 g509 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13996) h  -- d = 13996: 5 | 14107969+1, 1319+1
    rw [show (2:ℕ) ^ 13996 = (2 ^ 200) ^ 69 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 69 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14107969 : 14107969 ∈ P := S2 14107969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14107969 (by norm_num))
    have g503857 : 503857 ∈ P := S2 503857 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 503857 (by norm_num))
    have g1319 : 1319 ∈ P := S1 1319 (by norm_num) (by norm_num) (hnz (by norm_num)) 503857 g503857 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14107969 g14107969 1319 g1319 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14068) h  -- d = 14068: 5^2 | 506449+1
    rw [show (2:ℕ) ^ 14068 = (2 ^ 200) ^ 70 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 70 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g506449 : 506449 ∈ P := S2 506449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 506449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 506449 g506449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14108) h  -- d = 14108: 5^2 | 149+1
    rw [show (2:ℕ) ^ 14108 = (2 ^ 200) ^ 70 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 70 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3668081 : 3668081 ∈ P := S2 3668081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3668081 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 3668081 g3668081 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14228) h  -- d = 14228: 5 | 89+1, 19+1
    rw [show (2:ℕ) ^ 14228 = (2 ^ 200) ^ 71 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 71 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1195153 : 1195153 ∈ P := S2 1195153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1195153 (by norm_num))
    have g597577 : 597577 ∈ P := S1 597577 (by norm_num) (by norm_num) (hnz (by norm_num)) 1195153 g1195153 (by norm_num)
    have g4093 : 4093 ∈ P := S1 4093 (by norm_num) (by norm_num) (hnz (by norm_num)) 597577 g597577 (by norm_num)
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 4093 g4093 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 597577 g597577 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 89 g89 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14284) h  -- d = 14284: 5 | 4456609+1, 19+1
    rw [show (2:ℕ) ^ 14284 = (2 ^ 200) ^ 71 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 71 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4456609 : 4456609 ∈ P := S2 4456609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4456609 (by norm_num))
    have g3253 : 3253 ∈ P := S1 3253 (by norm_num) (by norm_num) (hnz (by norm_num)) 4456609 g4456609 (by norm_num)
    have g1627 : 1627 ∈ P := S1 1627 (by norm_num) (by norm_num) (hnz (by norm_num)) 3253 g3253 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 1627 g1627 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4456609 g4456609 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14428) h  -- d = 14428: 5 | 9619+1, 19+1
    rw [show (2:ℕ) ^ 14428 = (2 ^ 200) ^ 72 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 72 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g57713 : 57713 ∈ P := S2 57713 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 57713 (by norm_num))
    have g9619 : 9619 ∈ P := S1 9619 (by norm_num) (by norm_num) (hnz (by norm_num)) 57713 g57713 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 9619 g9619 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 9619 g9619 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14452) h  -- d = 14452: 7 | 41+1, 1560817+1
    rw [show (2:ℕ) ^ 14452 = (2 ^ 200) ^ 72 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 72 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g57809 : 57809 ∈ P := S2 57809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 57809 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 57809 g57809 (by norm_num)
    have g3121633 : 3121633 ∈ P := S2 3121633 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3121633 (by norm_num))
    have g1560817 : 1560817 ∈ P := S1 1560817 (by norm_num) (by norm_num) (hnz (by norm_num)) 3121633 g3121633 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 1560817 g1560817 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14524) h  -- d = 14524: 5 | 7726769+1, 1069+1
    rw [show (2:ℕ) ^ 14524 = (2 ^ 200) ^ 72 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 72 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7726769 : 7726769 ∈ P := S2 7726769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7726769 (by norm_num))
    have g3020993 : 3020993 ∈ P := S2 3020993 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3020993 (by norm_num))
    have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 3020993 g3020993 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7726769 g7726769 1069 g1069 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14764) h  -- d = 14764: 5 | 39744689+1, 29+1
    rw [show (2:ℕ) ^ 14764 = (2 ^ 200) ^ 73 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 73 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39744689 : 39744689 ∈ P := S2 39744689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39744689 (by norm_num))
    have g57601 : 57601 ∈ P := S1 57601 (by norm_num) (by norm_num) (hnz (by norm_num)) 39744689 g39744689 (by norm_num)
    have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 57601 g57601 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 39744689 g39744689 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14804) h  -- d = 14804: 3^8 | (2^14804+1) prod (p+1), p in {17, 15751457, 23, 29, 41, 5}
    rw [show (2:ℕ) ^ 14804 = (2 ^ 200) ^ 74 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g15751457 : 15751457 ∈ P := S2 15751457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15751457 (by norm_num))
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 15751457 g15751457 (by norm_num)
    have g38047 : 38047 ∈ P := S1 38047 (by norm_num) (by norm_num) (hnz (by norm_num)) 15751457 g15751457 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 38047 g38047 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 38047 g38047 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g15751457 (by simp) (by norm_num : 3 ^ 2 ∣ 15751457 + 1)
    have b3 := bud_cons b2 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    have b4 := bud_cons b3 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b5 := bud_cons b4 g41 (by simp) (by norm_num : 3 ^ 1 ∣ 41 + 1)
    have b6 := bud_cons b5 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14836) h  -- d = 14836: 7 | 11689+1, 167+1
    rw [show (2:ℕ) ^ 14836 = (2 ^ 200) ^ 74 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g771473 : 771473 ∈ P := S2 771473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 771473 (by norm_num))
    have g11689 : 11689 ∈ P := S1 11689 (by norm_num) (by norm_num) (hnz (by norm_num)) 771473 g771473 (by norm_num)
    have g167 : 167 ∈ P := S1 167 (by norm_num) (by norm_num) (hnz (by norm_num)) 11689 g11689 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 11689 g11689 167 g167 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14876) h  -- d = 14876: 5^2 | 663599+1
    rw [show (2:ℕ) ^ 14876 = (2 ^ 200) ^ 74 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30525553 : 30525553 ∈ P := S2 30525553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30525553 (by norm_num))
    have g663599 : 663599 ∈ P := S1 663599 (by norm_num) (by norm_num) (hnz (by norm_num)) 30525553 g30525553 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 663599 g663599 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14932) h  -- d = 14932: 7 | 181+1, 13+1
    rw [show (2:ℕ) ^ 14932 = (2 ^ 200) ^ 74 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g59729 : 59729 ∈ P := S2 59729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 59729 (by norm_num))
    have g181 : 181 ∈ P := S1 181 (by norm_num) (by norm_num) (hnz (by norm_num)) 59729 g59729 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 181 g181 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15076) h  -- d = 15076: 5 | 422129+1, 19+1
    rw [show (2:ℕ) ^ 15076 = (2 ^ 200) ^ 75 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 75 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g422129 : 422129 ∈ P := S2 422129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 422129 (by norm_num))
    have g2351857 : 2351857 ∈ P := S2 2351857 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2351857 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2351857 g2351857 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 422129 g422129 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15292) h  -- d = 15292: 5 | 61169+1, 2039+1
    rw [show (2:ℕ) ^ 15292 = (2 ^ 200) ^ 76 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 76 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g61169 : 61169 ∈ P := S2 61169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 61169 (by norm_num))
    have g2039 : 2039 ∈ P := S1 2039 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 2039 g2039 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15388) h  -- d = 15388: 5 | 246209+1, 29+1
    rw [show (2:ℕ) ^ 15388 = (2 ^ 200) ^ 76 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 76 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g246209 : 246209 ∈ P := S2 246209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 246209 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 246209 g246209 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 246209 g246209 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15404) h  -- d = 15404: 3^8 | (2^15404+1) prod (p+1), p in {17, 308081, 51347, 41, 71, 11}
    rw [show (2:ℕ) ^ 15404 = (2 ^ 200) ^ 77 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 77 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g308081 : 308081 ∈ P := S2 308081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 308081 (by norm_num))
    have g51347 : 51347 ∈ P := S1 51347 (by norm_num) (by norm_num) (hnz (by norm_num)) 308081 g308081 (by norm_num)
    have g739393 : 739393 ∈ P := S2 739393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 739393 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 739393 g739393 (by norm_num)
    have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 739393 g739393 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 51347 g51347 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g308081 (by simp) (by norm_num : 3 ^ 1 ∣ 308081 + 1)
    have b3 := bud_cons b2 g51347 (by simp) (by norm_num : 3 ^ 1 ∣ 51347 + 1)
    have b4 := bud_cons b3 g41 (by simp) (by norm_num : 3 ^ 1 ∣ 41 + 1)
    have b5 := bud_cons b4 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
    have b6 := bud_cons b5 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15452) h  -- d = 15452: 17 | 2^15452+1, 67+1
    rw [show (2:ℕ) ^ 15452 = (2 ^ 200) ^ 77 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 77 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1483393 : 1483393 ∈ P := S2 1483393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1483393 (by norm_num))
    have g67427 : 67427 ∈ P := S1 67427 (by norm_num) (by norm_num) (hnz (by norm_num)) 1483393 g1483393 (by norm_num)
    have g1873 : 1873 ∈ P := S1 1873 (by norm_num) (by norm_num) (hnz (by norm_num)) 67427 g67427 (by norm_num)
    have g937 : 937 ∈ P := S1 937 (by norm_num) (by norm_num) (hnz (by norm_num)) 1873 g1873 (by norm_num)
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 937 g937 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15628) h  -- d = 15628: 7 | 13+1, 12823+1
    rw [show (2:ℕ) ^ 15628 = (2 ^ 200) ^ 78 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1000193 : 1000193 ∈ P := S2 1000193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1000193 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1000193 g1000193 (by norm_num)
    have g12823 : 12823 ∈ P := S1 12823 (by norm_num) (by norm_num) (hnz (by norm_num)) 1000193 g1000193 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 12823 g12823 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15692) h  -- d = 15692: 7 | 13+1, 2897+1
    rw [show (2:ℕ) ^ 15692 = (2 ^ 200) ^ 78 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g376609 : 376609 ∈ P := S2 376609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 376609 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 376609 g376609 (by norm_num)
    have g2897 : 2897 ∈ P := S1 2897 (by norm_num) (by norm_num) (hnz (by norm_num)) 376609 g376609 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 2897 g2897 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15724) h  -- d = 15724: 3^8 | (2^15724+1) prod (p+1), p in {17, 62897, 11, 953, 53}
    rw [show (2:ℕ) ^ 15724 = (2 ^ 200) ^ 78 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num))
    have g62897 : 62897 ∈ P := S2 62897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 62897 (by norm_num))
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 62897 g62897 (by norm_num)
    have g953 : 953 ∈ P := S1 953 (by norm_num) (by norm_num) (hnz (by norm_num)) 62897 g62897 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 953 g953 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b2 := bud_cons b1 g62897 (by simp) (by norm_num : 3 ^ 1 ∣ 62897 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b4 := bud_cons b3 g953 (by simp) (by norm_num : 3 ^ 2 ∣ 953 + 1)
    have b5 := bud_cons b4 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15772) h  -- d = 15772: 5 | 3889+1, 389+1
    rw [show (2:ℕ) ^ 15772 = (2 ^ 200) ^ 78 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g567793 : 567793 ∈ P := S2 567793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 567793 (by norm_num))
    have g3889 : 3889 ∈ P := S1 3889 (by norm_num) (by norm_num) (hnz (by norm_num)) 567793 g567793 (by norm_num)
    have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 3889 g3889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3889 g3889 389 g389 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v3_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3064, 3176, 3272, 3352, 3544, 3592, 3704, 3832, 3896, 4024, 4184, 4376, 4568, 4856, 4904, 5128, 5384, 5608, 5752, 6008, 6056, 6152, 6296, 6568, 6616} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3064) h  -- d = 3064: 11 | 122561+1, 43+1
    rw [show (2:ℕ) ^ 3064 = (2 ^ 200) ^ 15 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g122561 : 122561 ∈ P := S2 122561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 122561 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 122561 g122561 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3176) h  -- d = 3176: 5 | 19+1, 59+1
    rw [show (2:ℕ) ^ 3176 = (2 ^ 200) ^ 15 * 2 ^ 176 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 15 * 2 ^ 176 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38113 : 38113 ∈ P := S2 38113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38113 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 38113 g38113 (by norm_num)
    have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 38113 g38113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 59 g59 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3272) h  -- d = 3272: 7 | 13+1, 839+1
    rw [show (2:ℕ) ^ 3272 = (2 ^ 200) ^ 16 * 2 ^ 72 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 72 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g261761 : 261761 ∈ P := S2 261761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 261761 (by norm_num))
    have g43627 : 43627 ∈ P := S1 43627 (by norm_num) (by norm_num) (hnz (by norm_num)) 261761 g261761 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 43627 g43627 (by norm_num)
    have g839 : 839 ∈ P := S1 839 (by norm_num) (by norm_num) (hnz (by norm_num)) 43627 g43627 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 839 g839 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3352) h  -- d = 3352: 5^2 | 80449+1
    rw [show (2:ℕ) ^ 3352 = (2 ^ 200) ^ 16 * 2 ^ 152 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 16 * 2 ^ 152 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g80449 : 80449 ∈ P := S2 80449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 80449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 80449 g80449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3544) h  -- d = 3544: 5^2 | 149+1
    rw [show (2:ℕ) ^ 3544 = (2 ^ 200) ^ 17 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g99233 : 99233 ∈ P := S2 99233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 99233 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 99233 g99233 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3592) h  -- d = 3592: 7 | 41+1, 83+1
    rw [show (2:ℕ) ^ 3592 = (2 ^ 200) ^ 17 * 2 ^ 192 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 17 * 2 ^ 192 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g129313 : 129313 ∈ P := S2 129313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 129313 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 129313 g129313 (by norm_num)
    have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 129313 g129313 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 83 g83 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3704) h  -- d = 3704: 5 | 118529+1, 439+1
    rw [show (2:ℕ) ^ 3704 = (2 ^ 200) ^ 18 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 18 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g118529 : 118529 ∈ P := S2 118529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 118529 (by norm_num))
    have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 118529 g118529 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 118529 g118529 439 g439 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3832) h  -- d = 3832: 7 | 15329+1, 22225601+1
    rw [show (2:ℕ) ^ 3832 = (2 ^ 200) ^ 19 * 2 ^ 32 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 32 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15329 : 15329 ∈ P := S2 15329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15329 (by norm_num))
    have g22225601 : 22225601 ∈ P := S2 22225601 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22225601 (by norm_num))
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 15329 g15329 22225601 g22225601 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 3896) h  -- d = 3896: 43 | 257+1, 6277+1
    rw [show (2:ℕ) ^ 3896 = (2 ^ 200) ^ 19 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 19 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g451937 : 451937 ∈ P := S2 451937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 451937 (by norm_num))
    have g75323 : 75323 ∈ P := S1 75323 (by norm_num) (by norm_num) (hnz (by norm_num)) 451937 g451937 (by norm_num)
    have g6277 : 6277 ∈ P := S1 6277 (by norm_num) (by norm_num) (hnz (by norm_num)) 75323 g75323 (by norm_num)
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 6277 g6277 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4024) h  -- d = 4024: 11 | 43+1, 2683+1
    rw [show (2:ℕ) ^ 4024 = (2 ^ 200) ^ 20 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g16097 : 16097 ∈ P := S2 16097 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16097 (by norm_num))
    have g2683 : 2683 ∈ P := S1 2683 (by norm_num) (by norm_num) (hnz (by norm_num)) 16097 g16097 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 2683 g2683 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4184) h  -- d = 4184: 11 | 16451489+1, 43+1
    rw [show (2:ℕ) ^ 4184 = (2 ^ 200) ^ 20 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 20 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16451489 : 16451489 ∈ P := S2 16451489 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16451489 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 16451489 g16451489 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4376) h  -- d = 4376: 11 | 43+1, 1187+1
    rw [show (2:ℕ) ^ 4376 = (2 ^ 200) ^ 21 * 2 ^ 176 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 176 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g1452833 : 1452833 ∈ P := S2 1452833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1452833 (by norm_num))
    have g80713 : 80713 ∈ P := S1 80713 (by norm_num) (by norm_num) (hnz (by norm_num)) 1452833 g1452833 (by norm_num)
    have g40357 : 40357 ∈ P := S1 40357 (by norm_num) (by norm_num) (hnz (by norm_num)) 80713 g80713 (by norm_num)
    have g1187 : 1187 ∈ P := S1 1187 (by norm_num) (by norm_num) (hnz (by norm_num)) 40357 g40357 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 1187 g1187 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4568) h  -- d = 4568: 5^2 | 164449+1
    rw [show (2:ℕ) ^ 4568 = (2 ^ 200) ^ 22 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 22 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g164449 : 164449 ∈ P := S2 164449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 164449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 164449 g164449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4856) h  -- d = 4856: 5^2 | 2696699+1
    rw [show (2:ℕ) ^ 4856 = (2 ^ 200) ^ 24 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 24 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16180193 : 16180193 ∈ P := S2 16180193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16180193 (by norm_num))
    have g2696699 : 2696699 ∈ P := S1 2696699 (by norm_num) (by norm_num) (hnz (by norm_num)) 16180193 g16180193 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2696699 g2696699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4904) h  -- d = 4904: 7 | 13+1, 503+1
    rw [show (2:ℕ) ^ 4904 = (2 ^ 200) ^ 24 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 24 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39233 : 39233 ∈ P := S2 39233 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39233 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 39233 g39233 (by norm_num)
    have g503 : 503 ∈ P := S1 503 (by norm_num) (by norm_num) (hnz (by norm_num)) 39233 g39233 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 503 g503 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5128) h  -- d = 5128: 5^2 | 1249+1
    rw [show (2:ℕ) ^ 5128 = (2 ^ 200) ^ 25 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2522977 : 2522977 ∈ P := S2 2522977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2522977 (by norm_num))
    have g1261489 : 1261489 ∈ P := S1 1261489 (by norm_num) (by norm_num) (hnz (by norm_num)) 2522977 g2522977 (by norm_num)
    have g1249 : 1249 ∈ P := S1 1249 (by norm_num) (by norm_num) (hnz (by norm_num)) 1261489 g1261489 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1249 g1249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5384) h  -- d = 5384: 7 | 64609+1, 13+1
    rw [show (2:ℕ) ^ 5384 = (2 ^ 200) ^ 26 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 26 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g64609 : 64609 ∈ P := S2 64609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 64609 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 64609 g64609 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 64609 g64609 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5608) h  -- d = 5608: 11 | 43+1, 3739+1
    rw [show (2:ℕ) ^ 5608 = (2 ^ 200) ^ 28 * 2 ^ 8 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 28 * 2 ^ 8 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g22433 : 22433 ∈ P := S2 22433 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22433 (by norm_num))
    have g3739 : 3739 ∈ P := S1 3739 (by norm_num) (by norm_num) (hnz (by norm_num)) 22433 g22433 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 3739 g3739 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5752) h  -- d = 5752: 11 | 43+1, 6577+1
    rw [show (2:ℕ) ^ 5752 = (2 ^ 200) ^ 28 * 2 ^ 152 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 28 * 2 ^ 152 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g26321153 : 26321153 ∈ P := S2 26321153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 26321153 (by norm_num))
    have g6577 : 6577 ∈ P := S1 6577 (by norm_num) (by norm_num) (hnz (by norm_num)) 26321153 g26321153 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 6577 g6577 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6008) h  -- d = 6008: 11 | 720961+1, 43+1
    rw [show (2:ℕ) ^ 6008 = (2 ^ 200) ^ 30 * 2 ^ 8 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 30 * 2 ^ 8 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g720961 : 720961 ∈ P := S2 720961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 720961 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 720961 g720961 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6056) h  -- d = 6056: 5 | 29+1, 179+1
    rw [show (2:ℕ) ^ 6056 = (2 ^ 200) ^ 30 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 30 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g72673 : 72673 ∈ P := S2 72673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 72673 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 72673 g72673 (by norm_num)
    have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 72673 g72673 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 179 g179 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6152) h  -- d = 6152: 5 | 19+1, 29+1
    rw [show (2:ℕ) ^ 6152 = (2 ^ 200) ^ 30 * 2 ^ 152 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 30 * 2 ^ 152 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g590593 : 590593 ∈ P := S2 590593 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 590593 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 590593 g590593 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 590593 g590593 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6296) h  -- d = 6296: 5 | 1109+1, 1709+1
    rw [show (2:ℕ) ^ 6296 = (2 ^ 200) ^ 31 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 31 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g22741153 : 22741153 ∈ P := S2 22741153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22741153 (by norm_num))
    have g1109 : 1109 ∈ P := S1 1109 (by norm_num) (by norm_num) (hnz (by norm_num)) 22741153 g22741153 (by norm_num)
    have g10253 : 10253 ∈ P := S1 10253 (by norm_num) (by norm_num) (hnz (by norm_num)) 22741153 g22741153 (by norm_num)
    have g1709 : 1709 ∈ P := S1 1709 (by norm_num) (by norm_num) (hnz (by norm_num)) 10253 g10253 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1109 g1109 1709 g1709 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6568) h  -- d = 6568: 11 | 1287329+1, 43+1
    rw [show (2:ℕ) ^ 6568 = (2 ^ 200) ^ 32 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 32 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1287329 : 1287329 ∈ P := S2 1287329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1287329 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 1287329 g1287329 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6616) h  -- d = 6616: 3^8 | (2^6616+1) prod (p+1), p in {257, 53, 107, 11}
    rw [show (2:ℕ) ^ 6616 = (2 ^ 200) ^ 33 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 33 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g79393 : 79393 ∈ P := S2 79393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 79393 (by norm_num))
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 79393 g79393 (by norm_num)
    have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 79393 g79393 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    have b3 := bud_cons b2 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)

theorem w52_v3_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({6856, 7016, 7048, 7096, 7256, 7528, 7768, 8104, 8728, 9208, 9304, 9544, 9704, 9784, 9832, 9896, 10264, 10312, 10424, 10552, 10568, 11416, 11624, 11768, 11864} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 6856) h  -- d = 6856: 7^2 | 97+1
    rw [show (2:ℕ) ^ 6856 = (2 ^ 200) ^ 34 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 34 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3647393 : 3647393 ∈ P := S2 3647393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3647393 (by norm_num))
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 3647393 g3647393 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7016) h  -- d = 7016: 43 | 257+1, 14565217+1
    rw [show (2:ℕ) ^ 7016 = (2 ^ 200) ^ 35 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 35 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g14565217 : 14565217 ∈ P := S2 14565217 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14565217 (by norm_num))
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 14565217 g14565217 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7048) h  -- d = 7048: 11 | 43+1, 211441+1
    rw [show (2:ℕ) ^ 7048 = (2 ^ 200) ^ 35 * 2 ^ 48 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 35 * 2 ^ 48 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g422881 : 422881 ∈ P := S2 422881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 422881 (by norm_num))
    have g211441 : 211441 ∈ P := S1 211441 (by norm_num) (by norm_num) (hnz (by norm_num)) 422881 g422881 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 211441 g211441 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7096) h  -- d = 7096: 5 | 20635169+1, 687839+1
    rw [show (2:ℕ) ^ 7096 = (2 ^ 200) ^ 35 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 35 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20635169 : 20635169 ∈ P := S2 20635169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20635169 (by norm_num))
    have g687839 : 687839 ∈ P := S1 687839 (by norm_num) (by norm_num) (hnz (by norm_num)) 20635169 g20635169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 20635169 g20635169 687839 g687839 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7256) h  -- d = 7256: 5^2 | 58049+1
    rw [show (2:ℕ) ^ 7256 = (2 ^ 200) ^ 36 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 36 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g58049 : 58049 ∈ P := S2 58049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 58049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 58049 g58049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7528) h  -- d = 7528: 3^8 | (2^7528+1) prod (p+1), p in {257, 30113, 6714977, 35080481, 239, 5846747, 11}
    rw [show (2:ℕ) ^ 7528 = (2 ^ 200) ^ 37 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 37 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g30113 : 30113 ∈ P := S2 30113 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30113 (by norm_num))
    have g6714977 : 6714977 ∈ P := S2 6714977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6714977 (by norm_num))
    have g35080481 : 35080481 ∈ P := S2 35080481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 35080481 (by norm_num))
    have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 30113 g30113 (by norm_num)
    have g5846747 : 5846747 ∈ P := S1 5846747 (by norm_num) (by norm_num) (hnz (by norm_num)) 35080481 g35080481 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g30113 (by simp) (by norm_num : 3 ^ 2 ∣ 30113 + 1)
    have b3 := bud_cons b2 g6714977 (by simp) (by norm_num : 3 ^ 1 ∣ 6714977 + 1)
    have b4 := bud_cons b3 g35080481 (by simp) (by norm_num : 3 ^ 1 ∣ 35080481 + 1)
    have b5 := bud_cons b4 g239 (by simp) (by norm_num : 3 ^ 1 ∣ 239 + 1)
    have b6 := bud_cons b5 g5846747 (by simp) (by norm_num : 3 ^ 1 ∣ 5846747 + 1)
    have b7 := bud_cons b6 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b7.1 ((pow_dvd_pow 3 (by norm_num)).trans b7.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 7768) h  -- d = 7768: 5^2 | 499+1
    rw [show (2:ℕ) ^ 7768 = (2 ^ 200) ^ 38 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 38 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g13329889 : 13329889 ∈ P := S2 13329889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13329889 (by norm_num))
    have g997 : 997 ∈ P := S1 997 (by norm_num) (by norm_num) (hnz (by norm_num)) 13329889 g13329889 (by norm_num)
    have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 997 g997 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8104) h  -- d = 8104: 13^2 | 10477+1
    rw [show (2:ℕ) ^ 8104 = (2 ^ 200) ^ 40 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 40 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3792673 : 3792673 ∈ P := S2 3792673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3792673 (by norm_num))
    have g10477 : 10477 ∈ P := S1 10477 (by norm_num) (by norm_num) (hnz (by norm_num)) 3792673 g3792673 (by norm_num)
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 10477 g10477 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8728) h  -- d = 8728: 23^2 | 34913+1
    rw [show (2:ℕ) ^ 8728 = (2 ^ 200) ^ 43 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 43 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g34913 : 34913 ∈ P := S2 34913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 34913 (by norm_num))
    exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 34913 g34913 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9208) h  -- d = 9208: 5^2 | 12486049+1
    rw [show (2:ℕ) ^ 9208 = (2 ^ 200) ^ 46 * 2 ^ 8 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 46 * 2 ^ 8 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12486049 : 12486049 ∈ P := S2 12486049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12486049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12486049 g12486049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9304) h  -- d = 9304: 3^8 | (2^9304+1) prod (p+1), p in {257, 11, 17, 521, 29, 5}
    rw [show (2:ℕ) ^ 9304 = (2 ^ 200) ^ 46 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 46 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g558241 : 558241 ∈ P := S2 558241 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 558241 (by norm_num))
    have g279121 : 279121 ∈ P := S1 279121 (by norm_num) (by norm_num) (hnz (by norm_num)) 558241 g558241 (by norm_num)
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 279121 g279121 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 (by norm_num)
    have g2083 : 2083 ∈ P := S1 2083 (by norm_num) (by norm_num) (hnz (by norm_num)) 279121 g279121 (by norm_num)
    have g521 : 521 ∈ P := S1 521 (by norm_num) (by norm_num) (hnz (by norm_num)) 2083 g2083 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 521 g521 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g521 (by simp) (by norm_num : 3 ^ 2 ∣ 521 + 1)
    have b5 := bud_cons b4 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b6 := bud_cons b5 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9544) h  -- d = 9544: 3^8 | (2^9544+1) prod (p+1), p in {257, 38177, 496289, 101, 5, 71}
    rw [show (2:ℕ) ^ 9544 = (2 ^ 200) ^ 47 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 47 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g38177 : 38177 ∈ P := S2 38177 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38177 (by norm_num))
    have g496289 : 496289 ∈ P := S2 496289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 496289 (by norm_num))
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 38177 g38177 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 496289 g496289 (by norm_num)
    have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 496289 g496289 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g38177 (by simp) (by norm_num : 3 ^ 3 ∣ 38177 + 1)
    have b3 := bud_cons b2 g496289 (by simp) (by norm_num : 3 ^ 1 ∣ 496289 + 1)
    have b4 := bud_cons b3 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b5 := bud_cons b4 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b6 := bud_cons b5 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9704) h  -- d = 9704: 11 | 43+1, 197+1
    rw [show (2:ℕ) ^ 9704 = (2 ^ 200) ^ 48 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 48 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g28374497 : 28374497 ∈ P := S2 28374497 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28374497 (by norm_num))
    have g787 : 787 ∈ P := S1 787 (by norm_num) (by norm_num) (hnz (by norm_num)) 28374497 g28374497 (by norm_num)
    have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 787 g787 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 197 g197 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9784) h  -- d = 9784: 5 | 29+1, 659+1
    rw [show (2:ℕ) ^ 9784 = (2 ^ 200) ^ 48 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 48 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g18002561 : 18002561 ∈ P := S2 18002561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 18002561 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 18002561 g18002561 (by norm_num)
    have g659 : 659 ∈ P := S1 659 (by norm_num) (by norm_num) (hnz (by norm_num)) 18002561 g18002561 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 659 g659 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9832) h  -- d = 9832: 11 | 43+1, 252823+1
    rw [show (2:ℕ) ^ 9832 = (2 ^ 200) ^ 49 * 2 ^ 32 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 49 * 2 ^ 32 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g3539521 : 3539521 ∈ P := S2 3539521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3539521 (by norm_num))
    have g252823 : 252823 ∈ P := S1 252823 (by norm_num) (by norm_num) (hnz (by norm_num)) 3539521 g3539521 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 252823 g252823 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 9896) h  -- d = 9896: 17 | 1339259+1, 101+1
    rw [show (2:ℕ) ^ 9896 = (2 ^ 200) ^ 49 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 49 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8035553 : 8035553 ∈ P := S2 8035553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8035553 (by norm_num))
    have g1339259 : 1339259 ∈ P := S1 1339259 (by norm_num) (by norm_num) (hnz (by norm_num)) 8035553 g8035553 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 1339259 g1339259 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1339259 g1339259 101 g101 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10264) h  -- d = 10264: 7 | 2281+1, 41+1
    rw [show (2:ℕ) ^ 10264 = (2 ^ 200) ^ 51 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 51 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g41057 : 41057 ∈ P := S2 41057 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 41057 (by norm_num))
    have g2281 : 2281 ∈ P := S1 2281 (by norm_num) (by norm_num) (hnz (by norm_num)) 41057 g41057 (by norm_num)
    have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 2281 g2281 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2281 g2281 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10312) h  -- d = 10312: 11 | 15014273+1, 43+1
    rw [show (2:ℕ) ^ 10312 = (2 ^ 200) ^ 51 * 2 ^ 112 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 51 * 2 ^ 112 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15014273 : 15014273 ∈ P := S2 15014273 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15014273 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 15014273 g15014273 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10424) h  -- d = 10424: 5 | 437809+1, 89+1
    rw [show (2:ℕ) ^ 10424 = (2 ^ 200) ^ 52 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 52 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g875617 : 875617 ∈ P := S2 875617 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 875617 (by norm_num))
    have g437809 : 437809 ∈ P := S1 437809 (by norm_num) (by norm_num) (hnz (by norm_num)) 875617 g875617 (by norm_num)
    have g43781 : 43781 ∈ P := S1 43781 (by norm_num) (by norm_num) (hnz (by norm_num)) 437809 g437809 (by norm_num)
    have g7297 : 7297 ∈ P := S1 7297 (by norm_num) (by norm_num) (hnz (by norm_num)) 43781 g43781 (by norm_num)
    have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (hnz (by norm_num)) 7297 g7297 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 437809 g437809 89 g89 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10552) h  -- d = 10552: 3^8 | (2^10552+1) prod (p+1), p in {257, 7892897, 47, 2153, 11, 359, 5}
    rw [show (2:ℕ) ^ 10552 = (2 ^ 200) ^ 52 * 2 ^ 152 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 52 * 2 ^ 152 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g7892897 : 7892897 ∈ P := S2 7892897 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7892897 (by norm_num))
    have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 7892897 g7892897 (by norm_num)
    have g2153 : 2153 ∈ P := S1 2153 (by norm_num) (by norm_num) (hnz (by norm_num)) 7892897 g7892897 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g359 : 359 ∈ P := S1 359 (by norm_num) (by norm_num) (hnz (by norm_num)) 2153 g2153 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 359 g359 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g7892897 (by simp) (by norm_num : 3 ^ 1 ∣ 7892897 + 1)
    have b3 := bud_cons b2 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
    have b4 := bud_cons b3 g2153 (by simp) (by norm_num : 3 ^ 1 ∣ 2153 + 1)
    have b5 := bud_cons b4 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b6 := bud_cons b5 g359 (by simp) (by norm_num : 3 ^ 2 ∣ 359 + 1)
    have b7 := bud_cons b6 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b7.1 ((pow_dvd_pow 3 (by norm_num)).trans b7.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10568) h  -- d = 10568: 3^8 | (2^10568+1) prod (p+1), p in {257, 29, 4373}
    rw [show (2:ℕ) ^ 10568 = (2 ^ 200) ^ 52 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 52 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g253633 : 253633 ∈ P := S2 253633 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 253633 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 253633 g253633 (by norm_num)
    have g4373 : 4373 ∈ P := S1 4373 (by norm_num) (by norm_num) (hnz (by norm_num)) 253633 g253633 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b3 := bud_cons b2 g4373 (by simp) (by norm_num : 3 ^ 7 ∣ 4373 + 1)
    exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11416) h  -- d = 11416: 3^8 | (2^11416+1) prod (p+1), p in {257, 593633, 867617, 98939, 16067, 11}
    rw [show (2:ℕ) ^ 11416 = (2 ^ 200) ^ 57 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 57 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g593633 : 593633 ∈ P := S2 593633 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 593633 (by norm_num))
    have g867617 : 867617 ∈ P := S2 867617 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 867617 (by norm_num))
    have g98939 : 98939 ∈ P := S1 98939 (by norm_num) (by norm_num) (hnz (by norm_num)) 593633 g593633 (by norm_num)
    have g16067 : 16067 ∈ P := S1 16067 (by norm_num) (by norm_num) (hnz (by norm_num)) 867617 g867617 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g593633 (by simp) (by norm_num : 3 ^ 1 ∣ 593633 + 1)
    have b3 := bud_cons b2 g867617 (by simp) (by norm_num : 3 ^ 3 ∣ 867617 + 1)
    have b4 := bud_cons b3 g98939 (by simp) (by norm_num : 3 ^ 1 ∣ 98939 + 1)
    have b5 := bud_cons b4 g16067 (by simp) (by norm_num : 3 ^ 1 ∣ 16067 + 1)
    have b6 := bud_cons b5 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11624) h  -- d = 11624: 3^8 | (2^11624+1) prod (p+1), p in {257, 511457, 11, 101, 17, 53}
    rw [show (2:ℕ) ^ 11624 = (2 ^ 200) ^ 58 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 58 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g511457 : 511457 ∈ P := S2 511457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 511457 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g85243 : 85243 ∈ P := S1 85243 (by norm_num) (by norm_num) (hnz (by norm_num)) 511457 g511457 (by norm_num)
    have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 85243 g85243 (by norm_num)
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 (by norm_num)
    have g211 : 211 ∈ P := S1 211 (by norm_num) (by norm_num) (hnz (by norm_num)) 85243 g85243 (by norm_num)
    have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 211 g211 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g511457 (by simp) (by norm_num : 3 ^ 1 ∣ 511457 + 1)
    have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b4 := bud_cons b3 g101 (by simp) (by norm_num : 3 ^ 1 ∣ 101 + 1)
    have b5 := bud_cons b4 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b6 := bud_cons b5 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
    exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11768) h  -- d = 11768: 5 | 479+1, 19+1
    rw [show (2:ℕ) ^ 11768 = (2 ^ 200) ^ 58 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 58 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6590081 : 6590081 ∈ P := S2 6590081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6590081 (by norm_num))
    have g479 : 479 ∈ P := S1 479 (by norm_num) (by norm_num) (hnz (by norm_num)) 6590081 g6590081 (by norm_num)
    have g2293 : 2293 ∈ P := S1 2293 (by norm_num) (by norm_num) (hnz (by norm_num)) 6590081 g6590081 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 2293 g2293 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 479 g479 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11864) h  -- d = 11864: 5^2 | 379649+1
    rw [show (2:ℕ) ^ 11864 = (2 ^ 200) ^ 59 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 59 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g379649 : 379649 ∈ P := S2 379649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 379649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 379649 g379649 (by norm_num)

theorem w52_v3_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({11992, 12088, 12424, 12472, 12536, 12568, 12664, 12968, 13016, 13256, 13336, 13544, 13768, 13864, 13928, 14072, 14216, 14296, 14312, 14648, 14968, 14984, 15032, 15256, 15304} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 11992) h  -- d = 11992: 7 | 13+1, 41+1
    rw [show (2:ℕ) ^ 11992 = (2 ^ 200) ^ 59 * 2 ^ 192 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 59 * 2 ^ 192 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g47969 : 47969 ∈ P := S2 47969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 47969 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 47969 g47969 (by norm_num)
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 47969 g47969 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12088) h  -- d = 12088: 5 | 6237409+1, 8059+1
    rw [show (2:ℕ) ^ 12088 = (2 ^ 200) ^ 60 * 2 ^ 88 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 60 * 2 ^ 88 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6237409 : 6237409 ∈ P := S2 6237409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6237409 (by norm_num))
    have g48353 : 48353 ∈ P := S2 48353 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 48353 (by norm_num))
    have g8059 : 8059 ∈ P := S1 8059 (by norm_num) (by norm_num) (hnz (by norm_num)) 48353 g48353 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6237409 g6237409 8059 g8059 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12424) h  -- d = 12424: 11 | 49697+1, 43+1
    rw [show (2:ℕ) ^ 12424 = (2 ^ 200) ^ 62 * 2 ^ 24 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 62 * 2 ^ 24 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g49697 : 49697 ∈ P := S2 49697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 49697 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 49697 g49697 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12472) h  -- d = 12472: 5^2 | 39710849+1
    rw [show (2:ℕ) ^ 12472 = (2 ^ 200) ^ 62 * 2 ^ 72 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 62 * 2 ^ 72 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g39710849 : 39710849 ∈ P := S2 39710849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 39710849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 39710849 g39710849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12536) h  -- d = 12536: 43 | 257+1, 702017+1
    rw [show (2:ℕ) ^ 12536 = (2 ^ 200) ^ 62 * 2 ^ 136 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 62 * 2 ^ 136 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g702017 : 702017 ∈ P := S2 702017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 702017 (by norm_num))
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 702017 g702017 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12568) h  -- d = 12568: 7^2 | 50273+1
    rw [show (2:ℕ) ^ 12568 = (2 ^ 200) ^ 62 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 62 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g50273 : 50273 ∈ P := S2 50273 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 50273 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 50273 g50273 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12664) h  -- d = 12664: 151969 | 2^12664+1, 303937+1
    rw [show (2:ℕ) ^ 12664 = (2 ^ 200) ^ 63 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 63 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g303937 : 303937 ∈ P := S2 303937 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 303937 (by norm_num))
    exact S4 151969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 151969 (by norm_num)) 303937 g303937 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12968) h  -- d = 12968: 11 | 43+1, 17291+1
    rw [show (2:ℕ) ^ 12968 = (2 ^ 200) ^ 64 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 64 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g414977 : 414977 ∈ P := S2 414977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 414977 (by norm_num))
    have g69163 : 69163 ∈ P := S1 69163 (by norm_num) (by norm_num) (hnz (by norm_num)) 414977 g414977 (by norm_num)
    have g17291 : 17291 ∈ P := S1 17291 (by norm_num) (by norm_num) (hnz (by norm_num)) 69163 g69163 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 17291 g17291 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13016) h  -- d = 13016: 7 | 11714401+1, 419+1
    rw [show (2:ℕ) ^ 13016 = (2 ^ 200) ^ 65 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 65 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g11714401 : 11714401 ∈ P := S2 11714401 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 11714401 (by norm_num))
    have g419 : 419 ∈ P := S1 419 (by norm_num) (by norm_num) (hnz (by norm_num)) 11714401 g11714401 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 11714401 g11714401 419 g419 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13256) h  -- d = 13256: 7^2 | 97+1
    rw [show (2:ℕ) ^ 13256 = (2 ^ 200) ^ 66 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 66 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g159073 : 159073 ∈ P := S2 159073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 159073 (by norm_num))
    have g79537 : 79537 ∈ P := S1 79537 (by norm_num) (by norm_num) (hnz (by norm_num)) 159073 g159073 (by norm_num)
    have g39769 : 39769 ∈ P := S1 39769 (by norm_num) (by norm_num) (hnz (by norm_num)) 79537 g79537 (by norm_num)
    have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 39769 g39769 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13336) h  -- d = 13336: 7^2 | 160033+1
    rw [show (2:ℕ) ^ 13336 = (2 ^ 200) ^ 66 * 2 ^ 136 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 66 * 2 ^ 136 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g160033 : 160033 ∈ P := S2 160033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 160033 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 160033 g160033 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13544) h  -- d = 13544: 43 | 257+1, 16253+1
    rw [show (2:ℕ) ^ 13544 = (2 ^ 200) ^ 67 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 67 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g162529 : 162529 ∈ P := S2 162529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 162529 (by norm_num))
    have g16253 : 16253 ∈ P := S1 16253 (by norm_num) (by norm_num) (hnz (by norm_num)) 162529 g162529 (by norm_num)
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 16253 g16253 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13768) h  -- d = 13768: 5^2 | 6002849+1
    rw [show (2:ℕ) ^ 13768 = (2 ^ 200) ^ 68 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 68 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6002849 : 6002849 ∈ P := S2 6002849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6002849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6002849 g6002849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13864) h  -- d = 13864: 5 | 2384609+1, 79+1
    rw [show (2:ℕ) ^ 13864 = (2 ^ 200) ^ 69 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 69 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2384609 : 2384609 ∈ P := S2 2384609 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2384609 (by norm_num))
    have g55457 : 55457 ∈ P := S2 55457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 55457 (by norm_num))
    have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 55457 g55457 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2384609 g2384609 79 g79 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 13928) h  -- d = 13928: 11 | 43+1, 1297+1
    rw [show (2:ℕ) ^ 13928 = (2 ^ 200) ^ 69 * 2 ^ 128 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 69 * 2 ^ 128 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g14707969 : 14707969 ∈ P := S2 14707969 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14707969 (by norm_num))
    have g1470797 : 1470797 ∈ P := S1 1470797 (by norm_num) (by norm_num) (hnz (by norm_num)) 14707969 g14707969 (by norm_num)
    have g1297 : 1297 ∈ P := S1 1297 (by norm_num) (by norm_num) (hnz (by norm_num)) 1470797 g1470797 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 1297 g1297 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14072) h  -- d = 14072: 3^8 | (2^14072+1) prod (p+1), p in {257, 112577, 29, 647, 11}
    rw [show (2:ℕ) ^ 14072 = (2 ^ 200) ^ 70 * 2 ^ 72 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 70 * 2 ^ 72 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g112577 : 112577 ∈ P := S2 112577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 112577 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 112577 g112577 (by norm_num)
    have g647 : 647 ∈ P := S1 647 (by norm_num) (by norm_num) (hnz (by norm_num)) 112577 g112577 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g112577 (by simp) (by norm_num : 3 ^ 1 ∣ 112577 + 1)
    have b3 := bud_cons b2 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b4 := bud_cons b3 g647 (by simp) (by norm_num : 3 ^ 4 ∣ 647 + 1)
    have b5 := bud_cons b4 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14216) h  -- d = 14216: 13^2 | 2160833+1
    rw [show (2:ℕ) ^ 14216 = (2 ^ 200) ^ 71 * 2 ^ 16 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 71 * 2 ^ 16 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2160833 : 2160833 ∈ P := S2 2160833 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2160833 (by norm_num))
    exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2160833 g2160833 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14296) h  -- d = 14296: 5^2 | 29850049+1
    rw [show (2:ℕ) ^ 14296 = (2 ^ 200) ^ 71 * 2 ^ 96 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 71 * 2 ^ 96 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g29850049 : 29850049 ∈ P := S2 29850049 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 29850049 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29850049 g29850049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14312) h  -- d = 14312: 3^8 | (2^14312+1) prod (p+1), p in {257, 2690657, 17, 977}
    rw [show (2:ℕ) ^ 14312 = (2 ^ 200) ^ 71 * 2 ^ 112 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 71 * 2 ^ 112 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g2690657 : 2690657 ∈ P := S2 2690657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2690657 (by norm_num))
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2690657 g2690657 (by norm_num)
    have g977 : 977 ∈ P := S1 977 (by norm_num) (by norm_num) (hnz (by norm_num)) 2690657 g2690657 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g2690657 (by simp) (by norm_num : 3 ^ 4 ∣ 2690657 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g977 (by simp) (by norm_num : 3 ^ 1 ∣ 977 + 1)
    exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14648) h  -- d = 14648: 11 | 43+1, 1033+1
    rw [show (2:ℕ) ^ 14648 = (2 ^ 200) ^ 73 * 2 ^ 48 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 73 * 2 ^ 48 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g644513 : 644513 ∈ P := S2 644513 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 644513 (by norm_num))
    have g8263 : 8263 ∈ P := S1 8263 (by norm_num) (by norm_num) (hnz (by norm_num)) 644513 g644513 (by norm_num)
    have g1033 : 1033 ∈ P := S1 1033 (by norm_num) (by norm_num) (hnz (by norm_num)) 8263 g8263 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 1033 g1033 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14968) h  -- d = 14968: 3^8 | (2^14968+1) prod (p+1), p in {257, 17, 29, 11, 5, 137, 23}
    rw [show (2:ℕ) ^ 14968 = (2 ^ 200) ^ 74 * 2 ^ 168 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 168 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g1077697 : 1077697 ∈ P := S2 1077697 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1077697 (by norm_num))
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1077697 g1077697 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1077697 g1077697 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 (by norm_num)
    have g1093 : 1093 ∈ P := S1 1093 (by norm_num) (by norm_num) (hnz (by norm_num)) 1077697 g1077697 (by norm_num)
    have g547 : 547 ∈ P := S1 547 (by norm_num) (by norm_num) (hnz (by norm_num)) 1093 g1093 (by norm_num)
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
    have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b3 := bud_cons b2 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    have b6 := bud_cons b5 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
    have b7 := bud_cons b6 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
    exact budget_kernel3 hP h3P E b7.1 ((pow_dvd_pow 3 (by norm_num)).trans b7.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 14984) h  -- d = 14984: 5^2 | 1078849+1
    rw [show (2:ℕ) ^ 14984 = (2 ^ 200) ^ 74 * 2 ^ 184 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 74 * 2 ^ 184 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1078849 : 1078849 ∈ P := S2 1078849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1078849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1078849 g1078849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15032) h  -- d = 15032: 17 | 591259+1, 67+1
    rw [show (2:ℕ) ^ 15032 = (2 ^ 200) ^ 75 * 2 ^ 32 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 75 * 2 ^ 32 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3547553 : 3547553 ∈ P := S2 3547553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3547553 (by norm_num))
    have g591259 : 591259 ∈ P := S1 591259 (by norm_num) (by norm_num) (hnz (by norm_num)) 3547553 g3547553 (by norm_num)
    have g27779137 : 27779137 ∈ P := S2 27779137 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 27779137 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 27779137 g27779137 (by norm_num)
    exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 591259 g591259 67 g67 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15256) h  -- d = 15256: 3^8 | (2^15256+1) prod (p+1), p in {257, 2440961, 17, 11, 5}
    rw [show (2:ℕ) ^ 15256 = (2 ^ 200) ^ 76 * 2 ^ 56 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 76 * 2 ^ 56 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g2440961 : 2440961 ∈ P := S2 2440961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2440961 (by norm_num))
    have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 2440961 g2440961 (by norm_num)
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have g2659 : 2659 ∈ P := S1 2659 (by norm_num) (by norm_num) (hnz (by norm_num)) 2440961 g2440961 (by norm_num)
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2659 g2659 (by norm_num)
    have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
      ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (R (3 ^ 0) (by norm_num))⟩
    have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
    have b2 := bud_cons b1 g2440961 (by simp) (by norm_num : 3 ^ 3 ∣ 2440961 + 1)
    have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
    have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
    have b5 := bud_cons b4 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
    exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15304) h  -- d = 15304: 97 | 193+1, 1163+1
    rw [show (2:ℕ) ^ 15304 = (2 ^ 200) ^ 76 * 2 ^ 104 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 76 * 2 ^ 104 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1346753 : 1346753 ∈ P := S2 1346753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1346753 (by norm_num))
    have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 1346753 g1346753 (by norm_num)
    have g1163 : 1163 ∈ P := S1 1163 (by norm_num) (by norm_num) (hnz (by norm_num)) 1346753 g1346753 (by norm_num)
    exact absurd (S3 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 1163 g1163 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_v3_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({15464, 15608, 15944} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc] at hd
  rcases hd with rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15464) h  -- d = 15464: 11 | 185569+1, 43+1
    rw [show (2:ℕ) ^ 15464 = (2 ^ 200) ^ 77 * 2 ^ 64 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 77 * 2 ^ 64 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g185569 : 185569 ∈ P := S2 185569 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 185569 (by norm_num))
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 185569 g185569 43 g43 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15608) h  -- d = 15608: 5 | 8990209+1, 229+1
    rw [show (2:ℕ) ^ 15608 = (2 ^ 200) ^ 78 * 2 ^ 8 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 8 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8990209 : 8990209 ∈ P := S2 8990209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8990209 (by norm_num))
    have g1831 : 1831 ∈ P := S1 1831 (by norm_num) (by norm_num) (hnz (by norm_num)) 8990209 g8990209 (by norm_num)
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 1831 g1831 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8990209 g8990209 229 g229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15944) h  -- d = 15944: 43 | 257+1, 765313+1
    rw [show (2:ℕ) ^ 15944 = (2 ^ 200) ^ 79 * 2 ^ 144 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 79 * 2 ^ 144 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 257 (by norm_num))
    have g765313 : 765313 ∈ P := S2 765313 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 765313 (by norm_num))
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 765313 g765313 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_sieve1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2986, 3022, 3086, 3134, 3142, 3158, 3166, 3194, 3202, 3214, 3218, 3238, 3242, 3254, 3274, 3282, 3326, 3334, 3386, 3394, 3398, 3418, 3466, 3494, 3506} : Finset ℕ) ∪
      ({3554, 3558, 3566, 3574, 3578, 3622, 3642, 3646, 3662, 3694, 3722, 3734, 3742, 3746, 3758, 3778, 3814, 3858, 3862, 3866, 3898, 3902, 3918, 3946, 3966} : Finset ℕ) ∪
      ({3974, 3986, 4034, 4054, 4058, 4062, 4078, 4098, 4138, 4162, 4166, 4178, 4198, 4206, 4222, 4262, 4274, 4282, 4286, 4306, 4406, 4414, 4426, 4442, 4474} : Finset ℕ),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with (h | h) | h
  · exact w52_v1_0 hP h3P E d h
  · exact w52_v1_1 hP h3P E d h
  · exact w52_v1_2 hP h3P E d h

theorem w52_sieve2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3028, 3076, 3092, 3244, 3284, 3292, 3316, 3412, 3428, 3628, 3644, 3748, 4084, 4132, 4204, 4348, 4364, 4372, 4412, 4436, 4492, 4516, 4684, 4868, 4924} : Finset ℕ) ∪
      ({4996, 5036, 5108, 5116, 5188, 5204, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996, 6124, 6268, 6388, 6404, 6428, 6652, 6676} : Finset ℕ) ∪
      ({6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324, 8332, 8396, 8452, 8524, 8612, 8644, 8812} : Finset ℕ) ∪
      ({8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10684, 10732, 10796, 10876, 10916, 10924, 11156} : Finset ℕ) ∪
      ({11164, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228, 13316, 13444, 13484} : Finset ℕ) ∪
      ({13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14804, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692, 15724, 15772} : Finset ℕ),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with ((((h | h) | h) | h) | h) | h
  · exact w52_v2_0 hP h3P E d h
  · exact w52_v2_1 hP h3P E d h
  · exact w52_v2_2 hP h3P E d h
  · exact w52_v2_3 hP h3P E d h
  · exact w52_v2_4 hP h3P E d h
  · exact w52_v2_5 hP h3P E d h

theorem w52_sieve3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({3064, 3176, 3272, 3352, 3544, 3592, 3704, 3832, 3896, 4024, 4184, 4376, 4568, 4856, 4904, 5128, 5384, 5608, 5752, 6008, 6056, 6152, 6296, 6568, 6616} : Finset ℕ) ∪
      ({6856, 7016, 7048, 7096, 7256, 7528, 7768, 8104, 8728, 9208, 9304, 9544, 9704, 9784, 9832, 9896, 10264, 10312, 10424, 10552, 10568, 11416, 11624, 11768, 11864} : Finset ℕ) ∪
      ({11992, 12088, 12424, 12472, 12536, 12568, 12664, 12968, 13016, 13256, 13336, 13544, 13768, 13864, 13928, 14072, 14216, 14296, 14312, 14648, 14968, 14984, 15032, 15256, 15304} : Finset ℕ) ∪
      ({15464, 15608, 15944} : Finset ℕ),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with ((h | h) | h) | h
  · exact w52_v3_0 hP h3P E d h
  · exact w52_v3_1 hP h3P E d h
  · exact w52_v3_2 hP h3P E d h
  · exact w52_v3_3 hP h3P E d h

-- Old classes with the matching power of 2, from the parent hypothesis.
-- Membership helpers (short names keep the explicit subset proofs below the size cap).
theorem w52i {a b : ℕ} {s : Finset ℕ} (h : a ∈ s) : a ∈ insert b s := Finset.mem_insert_of_mem h
theorem w52s {a : ℕ} {s : Finset ℕ} : a ∈ insert a s := Finset.mem_insert_self a s
theorem w52e {a : ℕ} : a ∈ ({a} : Finset ℕ) := Finset.mem_singleton_self a
theorem w52l {a : ℕ} {s t : Finset ℕ} (h : a ∈ s) : a ∈ s ∪ t := Finset.mem_union_left t h
theorem w52r {a : ℕ} {s t : Finset ℕ} (h : a ∈ t) : a ∈ s ∪ t := Finset.mem_union_right s h
theorem w52c {a : ℕ} {s t : Finset ℕ} (h : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t := Finset.insert_subset h hs
theorem w52o {a : ℕ} {t : Finset ℕ} (h : a ∈ t) : {a} ⊆ t := Finset.singleton_subset_iff.mpr h
theorem w52u {s s2 t : Finset ℕ} (h : s ⊆ t) (h2 : s2 ⊆ t) : s ∪ s2 ⊆ t := Finset.union_subset h h2

set_option maxHeartbeats 4000000 in
theorem w52_old1 {a : ℕ}
    (hf : ∀ d ∈ (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 818,
      824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974, 982,
      998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1126, 1138, 1142, 1154} : Finset ℕ) ∪
      ({1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382, 1384, 1388,
      1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544, 1546, 1574,
      1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754, 1756, 1762,
      1766, 1784, 1796, 1816} : Finset ℕ) ∪
      ({1822, 1832, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994, 2018,
      2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186, 2188,
      2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348, 2362,
      2372, 2374, 2396, 2402} : Finset ℕ) ∪
      ({2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572, 2578,
      2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734, 2762, 2764,
      2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942, 2962, 2966,
      2972, 2974, 2978} : Finset ℕ)),
      a % (2 * d) ≠ d) :
    ∀ d ∈ ({262, 274, 278, 298, 302, 314, 326, 334, 346, 358, 362, 382, 386, 394, 398, 422, 446, 454, 458, 466, 478, 482, 502, 514, 526} : Finset ℕ) ∪
      ({538, 542, 554, 562, 586, 614, 622, 626, 634, 662, 674, 694, 698, 718, 758, 766, 778, 794, 802, 818, 838, 842, 862, 866, 878} : Finset ℕ) ∪
      ({898, 914, 922, 934, 958, 974, 982, 998, 1006, 1018, 1042, 1046, 1082, 1126, 1138, 1142, 1154, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294} : Finset ℕ) ∪
      ({1318, 1346, 1382, 1418, 1438, 1454, 1466, 1478, 1502, 1522, 1546, 1574, 1618, 1622, 1646, 1654, 1678, 1698, 1706, 1718, 1726, 1754, 1762, 1766, 1822} : Finset ℕ) ∪
      ({1838, 1858, 1874, 1882, 1894, 1934, 1942, 1982, 1994, 2018, 2026, 2038, 2062, 2066, 2098, 2102, 2126, 2138, 2174, 2182, 2186, 2194, 2206, 2218, 2234} : Finset ℕ) ∪
      ({2238, 2246, 2302, 2306, 2326, 2342, 2362, 2374, 2402, 2434, 2446, 2458, 2462, 2474, 2498, 2518, 2554, 2566, 2578, 2594, 2602, 2606, 2614, 2638, 2654} : Finset ℕ) ∪
      ({2722, 2734, 2762, 2778, 2798, 2818, 2846, 2854, 2858, 2878, 2902, 2906, 2942, 2962, 2966, 2974, 2978} : Finset ℕ),
      a % (2 * d) ≠ d :=
  fun d hd => hf d ((w52u (w52u (w52u (w52u (w52u (w52u (w52c (w52l (w52l (w52l (w52l w52s))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i w52s))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i w52s)))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))
        (w52o (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52e)))))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i w52s))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i w52s))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i w52s)))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))
        (w52o (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52e)))))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i w52s))))
        (w52c (w52l (w52l (w52r (w52i (w52i w52s)))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i w52s))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i w52s)))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i w52s))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))
        (w52o (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))
        (w52o (w52l (w52r w52s))))))))))))))))))))))))))))
      (w52c (w52l (w52r (w52i (w52i w52s))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i w52s))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))
        (w52o (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52e)))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i w52s))
        (w52c (w52r (w52i (w52i w52s)))
        (w52c (w52r (w52i (w52i (w52i w52s))))
        (w52c (w52r (w52i (w52i (w52i (w52i w52s)))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))
        (w52o (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))
        (w52o (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52e))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hd)

set_option maxHeartbeats 4000000 in
theorem w52_old2 {a : ℕ}
    (hf : ∀ d ∈ (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 818,
      824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974, 982,
      998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1126, 1138, 1142, 1154} : Finset ℕ) ∪
      ({1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382, 1384, 1388,
      1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544, 1546, 1574,
      1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754, 1756, 1762,
      1766, 1784, 1796, 1816} : Finset ℕ) ∪
      ({1822, 1832, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994, 2018,
      2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186, 2188,
      2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348, 2362,
      2372, 2374, 2396, 2402} : Finset ℕ) ∪
      ({2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572, 2578,
      2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734, 2762, 2764,
      2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942, 2962, 2966,
      2972, 2974, 2978} : Finset ℕ)),
      a % (2 * d) ≠ d) :
    ∀ d ∈ ({268, 284, 316, 388, 412, 428, 436, 452, 508, 548, 604, 628, 652, 724, 788, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468} : Finset ℕ) ∪
      ({1492, 1604, 1636, 1756, 1796, 1844, 1868, 2188, 2284, 2308, 2348, 2372, 2396, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2644, 2692, 2764, 2908, 2932} : Finset ℕ) ∪
      ({2972} : Finset ℕ),
      a % (2 * d) ≠ d :=
  fun d hd => hf d ((w52u (w52u (w52c (w52l (w52l (w52l (w52l (w52i w52s)))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i w52s))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r w52s))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i w52s)))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r w52s)))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))
        (w52o (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i w52s)))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52r w52s)
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i w52s))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))
        (w52o (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (w52o (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))) hd)

set_option maxHeartbeats 4000000 in
theorem w52_old3 {a : ℕ}
    (hf : ∀ d ∈ (({262, 268, 274, 278, 284, 296, 298, 302, 314, 316, 326, 328, 334, 344, 346, 358, 362, 376, 382,
      386, 388, 394, 398, 412, 422, 428, 436, 446, 452, 454, 458, 466, 478, 482, 502, 508, 514,
      526, 536, 538, 542, 548, 554, 562, 568, 586, 604, 614, 622, 626} : Finset ℕ) ∪
      ({628, 632, 634, 652, 662, 674, 694, 698, 712, 718, 724, 758, 766, 776, 778, 788, 794, 802, 818,
      824, 838, 842, 856, 862, 866, 878, 892, 898, 904, 908, 914, 922, 932, 934, 958, 974, 982,
      998, 1006, 1018, 1042, 1046, 1048, 1076, 1082, 1084, 1126, 1138, 1142, 1154} : Finset ℕ) ∪
      ({1172, 1174, 1198, 1202, 1226, 1234, 1238, 1262, 1294, 1304, 1318, 1324, 1346, 1382, 1384, 1388,
      1396, 1418, 1432, 1438, 1454, 1466, 1468, 1478, 1492, 1502, 1522, 1528, 1544, 1546, 1574,
      1604, 1618, 1622, 1636, 1646, 1654, 1678, 1688, 1698, 1706, 1718, 1726, 1754, 1756, 1762,
      1766, 1784, 1796, 1816} : Finset ℕ) ∪
      ({1822, 1832, 1838, 1844, 1858, 1864, 1868, 1874, 1882, 1894, 1912, 1934, 1942, 1982, 1994, 2018,
      2026, 2038, 2056, 2062, 2066, 2098, 2102, 2104, 2126, 2138, 2168, 2174, 2182, 2186, 2188,
      2194, 2206, 2216, 2218, 2234, 2238, 2246, 2284, 2302, 2306, 2308, 2326, 2342, 2348, 2362,
      2372, 2374, 2396, 2402} : Finset ℕ) ∪
      ({2428, 2434, 2446, 2458, 2462, 2468, 2474, 2498, 2518, 2524, 2536, 2554, 2564, 2566, 2572, 2578,
      2594, 2602, 2606, 2612, 2614, 2636, 2638, 2644, 2648, 2654, 2692, 2722, 2734, 2762, 2764,
      2778, 2798, 2818, 2824, 2846, 2854, 2858, 2878, 2902, 2906, 2908, 2932, 2942, 2962, 2966,
      2972, 2974, 2978} : Finset ℕ)),
      a % (2 * d) ≠ d) :
    ∀ d ∈ ({296, 328, 344, 376, 536, 568, 632, 712, 776, 824, 856, 904, 1048, 1304, 1384, 1432, 1528, 1544, 1688, 1784, 1816, 1832, 1864, 1912, 2056} : Finset ℕ) ∪
      ({2104, 2168, 2216, 2536, 2648, 2824} : Finset ℕ),
      a % (2 * d) ≠ d :=
  fun d hd => hf d ((w52u (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i w52s)))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52l (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i w52s)))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52e))))))))))))))))))))))))))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i w52s)))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i w52s)))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))
        (w52o (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))))))
      (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s))))))))))))))))))))))))))))
        (w52c (w52l (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))
        (w52c (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))
        (w52o (w52r (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i (w52i w52s)))))))))))))))))))))))))))))))))))))))))) hd)

-- Section 2. The step.
set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he hlo h0 h16 hs hf => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hsimple : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hsimple
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rw [he] at E
  have t1 := w52_sieve1 hP h3P E
  have t2 := w52_sieve2 hP h3P E
  have t3 := w52_sieve3 hP h3P E
  rw [ha] at t1 t2 t3
  have o1 := w52_old1 hf
  have o2 := w52_old2 hf
  have o3 := w52_old3 hf
  have hk : padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 8 = 4 ∨ padicValNat 2 n % 16 = 8 := by omega
  rcases hk with k | k | k
  · refine (h1 n h hiff he hlo k hs (fun d hd => ?_)).trans (le_max_left _ _)
    rcases Finset.mem_union.mp hd with hd | hd
    · exact o1 d hd
    · exact t1 d hd
  · refine (h2 n h hiff he hlo k hs (fun d hd => ?_)).trans ((le_max_left _ _).trans (le_max_right _ _))
    rcases Finset.mem_union.mp hd with hd | hd
    · exact o2 d hd
    · exact t2 d hd
  · refine (h3 n h hiff he hlo k hs (fun d hd => ?_)).trans ((le_max_right _ _).trans (le_max_right _ _))
    rcases Finset.mem_union.mp hd with hd | hd
    · exact o3 d hd
    · exact t3 d hd

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1
