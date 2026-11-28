import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H3.R1.H2.R1
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H3.R1 (3 is the only repeated odd prime of the unitary perfect number n, its exponent is 19, a = 4 mod 8, a >= 262, and a is no odd multiple of any d <= 400 outside {1, 3, 4, 269, 292, 347, 353, 383}))
-- by whether a = padicValNat 2 n is an odd multiple of 292, with new excluded classes proved below.
-- Proving H1 and H2 proves the step.
--
-- Notation as in the parent files: a is an ODD MULTIPLE of d when a mod 2d = d; then 2^d + 1 divides 2^a + 1.
-- Balance equation: (2^a + 1)(3^19 + 1) prod (p + 1) = 2^(a+1) 3^19 prod p over the simple primes p.
--
-- PROVED BELOW (no hypothesis needed), by the forced-root method of the parent files (shared lemmas reused):
--   w52_sieve: a is no odd multiple of any of 215 new values d with v2(d) = 2, 412 <= d <= 21292
--   (only this class can matter, since a and d then have the same power of 2). None of them is an odd multiple of
--   a class excluded by the parent (every d <= 400 outside the parent's exception list) or of an earlier new one.
--   Each case: primes q of 2^d + 1 are simple primes of n, odd primes other than 3 of q + 1 are simple again,
--   and the chain ends in a prime with two sources (118), a prime dividing both 2^d+1 and some p+1 (25), a square dividing some p+1 (72).
--   All primes used are below 4.3 * 10^7 (norm_num checks them). The comment on each case names the contradiction.
--   main: the parent's case splits by a mod 584 = 292 (a is an odd multiple of 292, the parent's open class) or not.
--
-- H1 (OPEN): a mod 584 = 292.   H2 (OPEN): a mod 584 <> 292.  Both keep all parent conditions and add the new classes.
-- No known unitary perfect number satisfies the hypotheses of the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H3_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H3_R1 hiding H1 H2 H3 main

-- H1: a is bounded when a mod 584 = 292.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 19 →
    padicValNat 2 n % 8 = 4 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 4, 269, 292, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n % 584 = 292 →
    (∀ d ∈ (({412, 428, 436, 508, 548, 604, 628, 652, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796, 1868, 2188} : Finset ℕ) ∪
      ({2284, 2348, 2372, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2908, 2972, 3028, 3076, 3092, 3244, 3284, 3292, 3412, 3428, 3628, 3644, 3748, 4084, 4132} : Finset ℕ) ∪
      ({4348, 4364, 4412, 4436, 4492, 4516, 4684, 4868, 4924, 4996, 5036, 5108, 5188, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996} : Finset ℕ) ∪
      ({6124, 6268, 6388, 6404, 6428, 6652, 6676, 6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324} : Finset ℕ) ∪
      ({8332, 8396, 8452, 8524, 8644, 8812, 8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10796} : Finset ℕ) ∪
      ({10876, 10916, 10924, 11156, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228} : Finset ℕ) ∪
      ({13316, 13444, 13484, 13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692} : Finset ℕ) ∪
      ({15772, 16028, 16052, 16108, 16196, 16292, 16372, 16444, 16612, 16628, 16804, 16844, 16916, 16972, 17084, 17428, 17452, 17492, 17564, 17764, 17788, 17804, 18092, 18188, 18572} : Finset ℕ) ∪
      ({18916, 19036, 19268, 19444, 19556, 19724, 19804, 19868, 19876, 20092, 20452, 20476, 20836, 21092, 21292} : Finset ℕ)),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when a mod 584 <> 292.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 19 →
    padicValNat 2 n % 8 = 4 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 → d ∉ ({1, 3, 4, 269, 292, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n % 584 ≠ 292 →
    (∀ d ∈ (({412, 428, 436, 508, 548, 604, 628, 652, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796, 1868, 2188} : Finset ℕ) ∪
      ({2284, 2348, 2372, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2908, 2972, 3028, 3076, 3092, 3244, 3284, 3292, 3412, 3428, 3628, 3644, 3748, 4084, 4132} : Finset ℕ) ∪
      ({4348, 4364, 4412, 4436, 4492, 4516, 4684, 4868, 4924, 4996, 5036, 5108, 5188, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996} : Finset ℕ) ∪
      ({6124, 6268, 6388, 6404, 6428, 6652, 6676, 6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324} : Finset ℕ) ∪
      ({8332, 8396, 8452, 8524, 8644, 8812, 8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10796} : Finset ℕ) ∪
      ({10876, 10916, 10924, 11156, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228} : Finset ℕ) ∪
      ({13316, 13444, 13484, 13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692} : Finset ℕ) ∪
      ({15772, 16028, 16052, 16108, 16196, 16292, 16372, 16444, 16612, 16628, 16804, 16844, 16916, 16972, 17084, 17428, 17452, 17492, 17564, 17764, 17788, 17804, 18092, 18188, 18572} : Finset ℕ) ∪
      ({18916, 19036, 19268, 19444, 19556, 19724, 19804, 19868, 19876, 20092, 20452, 20476, 20836, 21092, 21292} : Finset ℕ)),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1. The new sieve.

theorem w52_c0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({412, 428, 436, 508, 548, 604, 628, 652, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796, 1868, 2188} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 412) h  -- d = 412: 5^2 | 454849+1
    rw [show (2:ℕ) ^ 412 = (2 ^ 200) ^ 2 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g454849 : 454849 ∈ P := S2 454849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 454849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 454849 g454849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 428) h  -- d = 428: 5 | 4209809+1, 2168819+1
    rw [show (2:ℕ) ^ 428 = (2 ^ 200) ^ 2 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4209809 : 4209809 ∈ P := S2 4209809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4209809 (by norm_num))
    have g13012913 : 13012913 ∈ P := S2 13012913 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 13012913 (by norm_num))
    have g2168819 : 2168819 ∈ P := S1 2168819 (by norm_num) (by norm_num) (hnz (by norm_num)) 13012913 g13012913 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4209809 g4209809 2168819 g2168819 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 436) h  -- d = 436: 5^2 | 199+1
    rw [show (2:ℕ) ^ 436 = (2 ^ 200) ^ 2 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g598193 : 598193 ∈ P := S2 598193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 598193 (by norm_num))
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 598193 g598193 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 508) h  -- d = 508: 19 | 37+1, 3001+1
    rw [show (2:ℕ) ^ 508 = (2 ^ 200) ^ 2 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3108961 : 3108961 ∈ P := S2 3108961 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3108961 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 3108961 g3108961 (by norm_num)
    have g42013 : 42013 ∈ P := S1 42013 (by norm_num) (by norm_num) (hnz (by norm_num)) 3108961 g3108961 (by norm_num)
    have g3001 : 3001 ∈ P := S1 3001 (by norm_num) (by norm_num) (hnz (by norm_num)) 42013 g42013 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 3001 g3001 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 548) h  -- d = 548: 19^2 | 38226289+1
    rw [show (2:ℕ) ^ 548 = (2 ^ 200) ^ 2 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 2 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38226289 : 38226289 ∈ P := S2 38226289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38226289 (by norm_num))
    exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 38226289 g38226289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 604) h  -- d = 604: 5^2 | 2181649+1
    rw [show (2:ℕ) ^ 604 = (2 ^ 200) ^ 3 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4363297 : 4363297 ∈ P := S2 4363297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4363297 (by norm_num))
    have g2181649 : 2181649 ∈ P := S1 2181649 (by norm_num) (by norm_num) (hnz (by norm_num)) 4363297 g4363297 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2181649 g2181649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 628) h  -- d = 628: 5 | 3769+1, 29+1
    rw [show (2:ℕ) ^ 628 = (2 ^ 200) ^ 3 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7537 : 7537 ∈ P := S2 7537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7537 (by norm_num))
    have g3769 : 3769 ∈ P := S1 3769 (by norm_num) (by norm_num) (hnz (by norm_num)) 7537 g7537 (by norm_num)
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 652) h  -- d = 652: 7^2 | 28322881+1
    rw [show (2:ℕ) ^ 652 = (2 ^ 200) ^ 3 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 3 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28322881 : 28322881 ∈ P := S2 28322881 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28322881 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 28322881 g28322881 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 892) h  -- d = 892: 5 | 19+1, 3329+1
    rw [show (2:ℕ) ^ 892 = (2 ^ 200) ^ 4 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1391521 : 1391521 ∈ P := S2 1391521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1391521 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1391521 g1391521 (by norm_num)
    have g3329 : 3329 ∈ P := S1 3329 (by norm_num) (by norm_num) (hnz (by norm_num)) 1391521 g1391521 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 3329 g3329 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 908) h  -- d = 908: 17 | 2^908+1, 83537+1
    rw [show (2:ℕ) ^ 908 = (2 ^ 200) ^ 4 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g83537 : 83537 ∈ P := S2 83537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 83537 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 83537 g83537 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 932) h  -- d = 932: 17^2 | 74561+1
    rw [show (2:ℕ) ^ 932 = (2 ^ 200) ^ 4 * 2 ^ 132 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 4 * 2 ^ 132 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g74561 : 74561 ∈ P := S2 74561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 74561 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 74561 g74561 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1076) h  -- d = 1076: 5 | 61169+1, 2039+1
    rw [show (2:ℕ) ^ 1076 = (2 ^ 200) ^ 5 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4037153 : 4037153 ∈ P := S2 4037153 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4037153 (by norm_num))
    have g61169 : 61169 ∈ P := S1 61169 (by norm_num) (by norm_num) (hnz (by norm_num)) 4037153 g4037153 (by norm_num)
    have g2039 : 2039 ∈ P := S1 2039 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 61169 g61169 2039 g2039 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1084) h  -- d = 1084: 11^2 | 241+1
    rw [show (2:ℕ) ^ 1084 = (2 ^ 200) ^ 5 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4337 : 4337 ∈ P := S2 4337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4337 (by norm_num))
    have g241 : 241 ∈ P := S1 241 (by norm_num) (by norm_num) (hnz (by norm_num)) 4337 g4337 (by norm_num)
    exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 241 g241 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1172) h  -- d = 1172: 23^2 | 4231+1
    rw [show (2:ℕ) ^ 1172 = (2 ^ 200) ^ 5 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 5 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1345457 : 1345457 ∈ P := S2 1345457 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1345457 (by norm_num))
    have g4231 : 4231 ∈ P := S1 4231 (by norm_num) (by norm_num) (hnz (by norm_num)) 1345457 g1345457 (by norm_num)
    exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 4231 g4231 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1324) h  -- d = 1324: 7 | 15889+1, 13+1
    rw [show (2:ℕ) ^ 1324 = (2 ^ 200) ^ 6 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g15889 : 15889 ∈ P := S2 15889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 15889 (by norm_num))
    have g1085681 : 1085681 ∈ P := S2 1085681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1085681 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1085681 g1085681 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 15889 g15889 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1388) h  -- d = 1388: 7^2 | 8329+1
    rw [show (2:ℕ) ^ 1388 = (2 ^ 200) ^ 6 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g16657 : 16657 ∈ P := S2 16657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 16657 (by norm_num))
    have g8329 : 8329 ∈ P := S1 8329 (by norm_num) (by norm_num) (hnz (by norm_num)) 16657 g16657 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 8329 g8329 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1396) h  -- d = 1396: 5 | 150769+1, 359+1
    rw [show (2:ℕ) ^ 1396 = (2 ^ 200) ^ 6 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 6 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g150769 : 150769 ∈ P := S2 150769 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 150769 (by norm_num))
    have g15077 : 15077 ∈ P := S1 15077 (by norm_num) (by norm_num) (hnz (by norm_num)) 150769 g150769 (by norm_num)
    have g359 : 359 ∈ P := S1 359 (by norm_num) (by norm_num) (hnz (by norm_num)) 15077 g15077 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 150769 g150769 359 g359 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1468) h  -- d = 1468: 17 | 2^1468+1, 340577+1
    rw [show (2:ℕ) ^ 1468 = (2 ^ 200) ^ 7 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g340577 : 340577 ∈ P := S2 340577 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 340577 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 340577 g340577 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1492) h  -- d = 1492: 5^2 | 199+1
    rw [show (2:ℕ) ^ 1492 = (2 ^ 200) ^ 7 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 7 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g35809 : 35809 ∈ P := S2 35809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 35809 (by norm_num))
    have g3581 : 3581 ∈ P := S1 3581 (by norm_num) (by norm_num) (hnz (by norm_num)) 35809 g35809 (by norm_num)
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 3581 g3581 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1604) h  -- d = 1604: 7^2 | 109073+1
    rw [show (2:ℕ) ^ 1604 = (2 ^ 200) ^ 8 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g109073 : 109073 ∈ P := S2 109073 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 109073 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 109073 g109073 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1636) h  -- d = 1636: 11 | 516977+1, 373+1
    rw [show (2:ℕ) ^ 1636 = (2 ^ 200) ^ 8 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g516977 : 516977 ∈ P := S2 516977 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 516977 (by norm_num))
    have g373 : 373 ∈ P := S1 373 (by norm_num) (by norm_num) (hnz (by norm_num)) 516977 g516977 (by norm_num)
    exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 516977 g516977 373 g373 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1756) h  -- d = 1756: 5^2 | 149+1
    rw [show (2:ℕ) ^ 1756 = (2 ^ 200) ^ 8 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g49169 : 49169 ∈ P := S2 49169 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 49169 (by norm_num))
    have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 49169 g49169 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1796) h  -- d = 1796: 5 | 14369+1, 2780209+1
    rw [show (2:ℕ) ^ 1796 = (2 ^ 200) ^ 8 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 8 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g14369 : 14369 ∈ P := S2 14369 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 14369 (by norm_num))
    have g2780209 : 2780209 ∈ P := S2 2780209 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2780209 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14369 g14369 2780209 g2780209 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 1868) h  -- d = 1868: 5 | 3019+1, 19+1
    rw [show (2:ℕ) ^ 1868 = (2 ^ 200) ^ 9 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 9 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g597761 : 597761 ∈ P := S2 597761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 597761 (by norm_num))
    have g3019 : 3019 ∈ P := S1 3019 (by norm_num) (by norm_num) (hnz (by norm_num)) 597761 g597761 (by norm_num)
    have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3019 g3019 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2188) h  -- d = 2188: 5 | 1459+1, 19+1
    rw [show (2:ℕ) ^ 2188 = (2 ^ 200) ^ 10 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 10 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8753 : 8753 ∈ P := S2 8753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8753 (by norm_num))
    have g1459 : 1459 ∈ P := S1 1459 (by norm_num) (by norm_num) (hnz (by norm_num)) 8753 g8753 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 19 g19 (by norm_num) (by norm_num)) (by norm_num)

theorem w52_c1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({2284, 2348, 2372, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2908, 2972, 3028, 3076, 3092, 3244, 3284, 3292, 3412, 3428, 3628, 3644, 3748, 4084, 4132} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2284) h  -- d = 2284: 5 | 30678689+1, 139+1
    rw [show (2:ℕ) ^ 2284 = (2 ^ 200) ^ 11 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g30678689 : 30678689 ∈ P := S2 30678689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 30678689 (by norm_num))
    have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 30678689 g30678689 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 30678689 g30678689 139 g139 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2348) h  -- d = 2348: 5 | 1493329+1, 24889+1
    rw [show (2:ℕ) ^ 2348 = (2 ^ 200) ^ 11 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2986657 : 2986657 ∈ P := S2 2986657 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2986657 (by norm_num))
    have g1493329 : 1493329 ∈ P := S1 1493329 (by norm_num) (by norm_num) (hnz (by norm_num)) 2986657 g2986657 (by norm_num)
    have g149333 : 149333 ∈ P := S1 149333 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493329 g1493329 (by norm_num)
    have g24889 : 24889 ∈ P := S1 24889 (by norm_num) (by norm_num) (hnz (by norm_num)) 149333 g149333 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1493329 g1493329 24889 g24889 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2372) h  -- d = 2372: 7 | 370033+1, 26431+1
    rw [show (2:ℕ) ^ 2372 = (2 ^ 200) ^ 11 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 11 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g370033 : 370033 ∈ P := S2 370033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 370033 (by norm_num))
    have g26431 : 26431 ∈ P := S1 26431 (by norm_num) (by norm_num) (hnz (by norm_num)) 370033 g370033 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 370033 g370033 26431 g26431 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2428) h  -- d = 2428: 5 | 475889+1, 29+1
    rw [show (2:ℕ) ^ 2428 = (2 ^ 200) ^ 12 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g475889 : 475889 ∈ P := S2 475889 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 475889 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 475889 g475889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 475889 g475889 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2468) h  -- d = 2468: 5^2 | 124699+1
    rw [show (2:ℕ) ^ 2468 = (2 ^ 200) ^ 12 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4738561 : 4738561 ∈ P := S2 4738561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4738561 (by norm_num))
    have g124699 : 124699 ∈ P := S1 124699 (by norm_num) (by norm_num) (hnz (by norm_num)) 4738561 g4738561 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 124699 g124699 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2524) h  -- d = 2524: 17 | 2^2524+1, 4644161+1
    rw [show (2:ℕ) ^ 2524 = (2 ^ 200) ^ 12 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4644161 : 4644161 ∈ P := S2 4644161 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4644161 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 4644161 g4644161 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2564) h  -- d = 2564: 97 | 153841+1, 3138337+1
    rw [show (2:ℕ) ^ 2564 = (2 ^ 200) ^ 12 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g153841 : 153841 ∈ P := S2 153841 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 153841 (by norm_num))
    have g3138337 : 3138337 ∈ P := S2 3138337 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3138337 (by norm_num))
    exact absurd (S3 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 153841 g153841 3138337 g3138337 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2572) h  -- d = 2572: 7^2 | 10289+1
    rw [show (2:ℕ) ^ 2572 = (2 ^ 200) ^ 12 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 12 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g10289 : 10289 ∈ P := S2 10289 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 10289 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 10289 g10289 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2612) h  -- d = 2612: 5 | 23509+1, 19+1
    rw [show (2:ℕ) ^ 2612 = (2 ^ 200) ^ 13 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g94033 : 94033 ∈ P := S2 94033 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 94033 (by norm_num))
    have g47017 : 47017 ∈ P := S1 47017 (by norm_num) (by norm_num) (hnz (by norm_num)) 94033 g94033 (by norm_num)
    have g23509 : 23509 ∈ P := S1 23509 (by norm_num) (by norm_num) (hnz (by norm_num)) 47017 g47017 (by norm_num)
    have g9424097 : 9424097 ∈ P := S2 9424097 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 9424097 (by norm_num))
    have g1367 : 1367 ∈ P := S1 1367 (by norm_num) (by norm_num) (hnz (by norm_num)) 9424097 g9424097 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1367 g1367 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 23509 g23509 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2636) h  -- d = 2636: 5 | 21089+1, 19+1
    rw [show (2:ℕ) ^ 2636 = (2 ^ 200) ^ 13 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 13 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g21089 : 21089 ∈ P := S2 21089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21089 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 21089 g21089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 21089 g21089 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2908) h  -- d = 2908: 5 | 1093409+1, 21914689+1
    rw [show (2:ℕ) ^ 2908 = (2 ^ 200) ^ 14 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1093409 : 1093409 ∈ P := S2 1093409 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1093409 (by norm_num))
    have g21914689 : 21914689 ∈ P := S2 21914689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 21914689 (by norm_num))
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1093409 g1093409 21914689 g21914689 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 2972) h  -- d = 2972: 5 | 71329+1, 1019+1
    rw [show (2:ℕ) ^ 2972 = (2 ^ 200) ^ 14 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 14 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g71329 : 71329 ∈ P := S2 71329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 71329 (by norm_num))
    have g1019 : 1019 ∈ P := S1 1019 (by norm_num) (by norm_num) (hnz (by norm_num)) 71329 g71329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 71329 g71329 1019 g1019 (by norm_num) (by norm_num)) (by norm_num)
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

theorem w52_c2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({4348, 4364, 4412, 4436, 4492, 4516, 4684, 4868, 4924, 4996, 5036, 5108, 5188, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4348) h  -- d = 4348: 7 | 13+1, 223+1
    rw [show (2:ℕ) ^ 4348 = (2 ^ 200) ^ 21 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17393 : 17393 ∈ P := S2 17393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17393 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 17393 g17393 (by norm_num)
    have g223 : 223 ∈ P := S1 223 (by norm_num) (by norm_num) (hnz (by norm_num)) 17393 g17393 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 223 g223 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 4364) h  -- d = 4364: 5 | 23967089+1, 1409+1
    rw [show (2:ℕ) ^ 4364 = (2 ^ 200) ^ 21 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 21 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g23967089 : 23967089 ∈ P := S2 23967089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 23967089 (by norm_num))
    have g1409 : 1409 ∈ P := S1 1409 (by norm_num) (by norm_num) (hnz (by norm_num)) 23967089 g23967089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 23967089 g23967089 1409 g1409 (by norm_num) (by norm_num)) (by norm_num)
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
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 5188) h  -- d = 5188: 17^2 | 577+1
    rw [show (2:ℕ) ^ 5188 = (2 ^ 200) ^ 25 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 25 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g20753 : 20753 ∈ P := S2 20753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 20753 (by norm_num))
    have g1153 : 1153 ∈ P := S1 1153 (by norm_num) (by norm_num) (hnz (by norm_num)) 20753 g20753 (by norm_num)
    have g577 : 577 ∈ P := S1 577 (by norm_num) (by norm_num) (hnz (by norm_num)) 1153 g1153 (by norm_num)
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)
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

theorem w52_c3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({6124, 6268, 6388, 6404, 6428, 6652, 6676, 6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem w52_c4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({8332, 8396, 8452, 8524, 8644, 8812, 8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10796} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8644) h  -- d = 8644: 5 | 19+1, 269+1
    rw [show (2:ℕ) ^ 8644 = (2 ^ 200) ^ 43 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 43 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g28559777 : 28559777 ∈ P := S2 28559777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 28559777 (by norm_num))
    have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (hnz (by norm_num)) 28559777 g28559777 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 227 g227 (by norm_num)
    have g1613 : 1613 ∈ P := S1 1613 (by norm_num) (by norm_num) (hnz (by norm_num)) 28559777 g28559777 (by norm_num)
    have g269 : 269 ∈ P := S1 269 (by norm_num) (by norm_num) (hnz (by norm_num)) 1613 g1613 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 269 g269 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 8812) h  -- d = 8812: 5 | 4519+1, 19+1
    rw [show (2:ℕ) ^ 8812 = (2 ^ 200) ^ 44 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 44 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g352481 : 352481 ∈ P := S2 352481 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 352481 (by norm_num))
    have g4519 : 4519 ∈ P := S1 4519 (by norm_num) (by norm_num) (hnz (by norm_num)) 352481 g352481 (by norm_num)
    have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 4519 g4519 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4519 g4519 19 g19 (by norm_num) (by norm_num)) (by norm_num)
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
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 10796) h  -- d = 10796: 17 | 2^10796+1, 345473+1
    rw [show (2:ℕ) ^ 10796 = (2 ^ 200) ^ 53 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 53 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g345473 : 345473 ∈ P := S2 345473 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 345473 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 345473 g345473 (by norm_num)

theorem w52_c5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({10876, 10916, 10924, 11156, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 12748) h  -- d = 12748: 23 | 22181521+1, 137+1
    rw [show (2:ℕ) ^ 12748 = (2 ^ 200) ^ 63 * 2 ^ 148 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 63 * 2 ^ 148 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g22181521 : 22181521 ∈ P := S2 22181521 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 22181521 (by norm_num))
    have g4487297 : 4487297 ∈ P := S2 4487297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4487297 (by norm_num))
    have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 4487297 g4487297 (by norm_num)
    exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 22181521 g22181521 137 g137 (by norm_num) (by norm_num)) (by norm_num)
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

theorem w52_c6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({13316, 13444, 13484, 13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15404) h  -- d = 15404: 7 | 41+1, 13+1
    rw [show (2:ℕ) ^ 15404 = (2 ^ 200) ^ 77 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 77 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g739393 : 739393 ∈ P := S2 739393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 739393 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 739393 g739393 (by norm_num)
    have g308081 : 308081 ∈ P := S2 308081 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 308081 (by norm_num))
    have g51347 : 51347 ∈ P := S1 51347 (by norm_num) (by norm_num) (hnz (by norm_num)) 308081 g308081 (by norm_num)
    have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 51347 g51347 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 389 g389 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)) (by norm_num)
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

theorem w52_c7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({15772, 16028, 16052, 16108, 16196, 16292, 16372, 16444, 16612, 16628, 16804, 16844, 16916, 16972, 17084, 17428, 17452, 17492, 17564, 17764, 17788, 17804, 18092, 18188, 18572} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 15772) h  -- d = 15772: 5 | 3889+1, 389+1
    rw [show (2:ℕ) ^ 15772 = (2 ^ 200) ^ 78 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 78 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g567793 : 567793 ∈ P := S2 567793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 567793 (by norm_num))
    have g3889 : 3889 ∈ P := S1 3889 (by norm_num) (by norm_num) (hnz (by norm_num)) 567793 g567793 (by norm_num)
    have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 3889 g3889 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3889 g3889 389 g389 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16028) h  -- d = 16028: 5 | 577009+1, 229+1
    rw [show (2:ℕ) ^ 16028 = (2 ^ 200) ^ 80 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 80 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1154017 : 1154017 ∈ P := S2 1154017 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1154017 (by norm_num))
    have g577009 : 577009 ∈ P := S1 577009 (by norm_num) (by norm_num) (hnz (by norm_num)) 1154017 g1154017 (by norm_num)
    have g8243 : 8243 ∈ P := S1 8243 (by norm_num) (by norm_num) (hnz (by norm_num)) 577009 g577009 (by norm_num)
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 8243 g8243 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 577009 g577009 229 g229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16052) h  -- d = 16052: 5^2 | 1499+1
    rw [show (2:ℕ) ^ 16052 = (2 ^ 200) ^ 80 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 80 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g37882721 : 37882721 ∈ P := S2 37882721 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 37882721 (by norm_num))
    have g6313787 : 6313787 ∈ P := S1 6313787 (by norm_num) (by norm_num) (hnz (by norm_num)) 37882721 g37882721 (by norm_num)
    have g1499 : 1499 ∈ P := S1 1499 (by norm_num) (by norm_num) (hnz (by norm_num)) 6313787 g6313787 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1499 g1499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16108) h  -- d = 16108: 5^2 | 7345249+1
    rw [show (2:ℕ) ^ 16108 = (2 ^ 200) ^ 80 * 2 ^ 108 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 80 * 2 ^ 108 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g7345249 : 7345249 ∈ P := S2 7345249 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 7345249 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 7345249 g7345249 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16196) h  -- d = 16196: 23 | 1295681+1, 229+1
    rw [show (2:ℕ) ^ 16196 = (2 ^ 200) ^ 80 * 2 ^ 196 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 80 * 2 ^ 196 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1295681 : 1295681 ∈ P := S2 1295681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1295681 (by norm_num))
    have g229 : 229 ∈ P := S1 229 (by norm_num) (by norm_num) (hnz (by norm_num)) 1295681 g1295681 (by norm_num)
    exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 1295681 g1295681 229 g229 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16292) h  -- d = 16292: 5 | 1368529+1, 1279+1
    rw [show (2:ℕ) ^ 16292 = (2 ^ 200) ^ 81 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 81 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1368529 : 1368529 ∈ P := S2 1368529 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1368529 (by norm_num))
    have g1279 : 1279 ∈ P := S1 1279 (by norm_num) (by norm_num) (hnz (by norm_num)) 1368529 g1368529 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1368529 g1368529 1279 g1279 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16372) h  -- d = 16372: 5^2 | 1496149+1
    rw [show (2:ℕ) ^ 16372 = (2 ^ 200) ^ 81 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 81 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g38899873 : 38899873 ∈ P := S2 38899873 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 38899873 (by norm_num))
    have g1496149 : 1496149 ∈ P := S1 1496149 (by norm_num) (by norm_num) (hnz (by norm_num)) 38899873 g38899873 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1496149 g1496149 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16444) h  -- d = 16444: 5 | 855089+1, 19+1
    rw [show (2:ℕ) ^ 16444 = (2 ^ 200) ^ 82 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 82 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g855089 : 855089 ∈ P := S2 855089 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 855089 (by norm_num))
    have g65777 : 65777 ∈ P := S2 65777 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 65777 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 65777 g65777 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 855089 g855089 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16612) h  -- d = 16612: 5^2 | 66449+1
    rw [show (2:ℕ) ^ 16612 = (2 ^ 200) ^ 83 * 2 ^ 12 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 83 * 2 ^ 12 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g66449 : 66449 ∈ P := S2 66449 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 66449 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 66449 g66449 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16628) h  -- d = 16628: 43 | 332561+1, 1289+1
    rw [show (2:ℕ) ^ 16628 = (2 ^ 200) ^ 83 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 83 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g332561 : 332561 ∈ P := S2 332561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 332561 (by norm_num))
    have g1289 : 1289 ∈ P := S1 1289 (by norm_num) (by norm_num) (hnz (by norm_num)) 332561 g332561 (by norm_num)
    exact absurd (S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 332561 g332561 1289 g1289 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16804) h  -- d = 16804: 5^2 | 5242849+1
    rw [show (2:ℕ) ^ 16804 = (2 ^ 200) ^ 84 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 84 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5242849 : 5242849 ∈ P := S2 5242849 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5242849 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5242849 g5242849 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16844) h  -- d = 16844: 19 | 37+1, 607+1
    rw [show (2:ℕ) ^ 16844 = (2 ^ 200) ^ 84 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 84 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g134753 : 134753 ∈ P := S2 134753 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 134753 (by norm_num))
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 134753 g134753 (by norm_num)
    have g607 : 607 ∈ P := S1 607 (by norm_num) (by norm_num) (hnz (by norm_num)) 134753 g134753 (by norm_num)
    exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 607 g607 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16916) h  -- d = 16916: 5 | 135329+1, 19+1
    rw [show (2:ℕ) ^ 16916 = (2 ^ 200) ^ 84 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 84 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g135329 : 135329 ∈ P := S2 135329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 135329 (by norm_num))
    have g2029921 : 2029921 ∈ P := S2 2029921 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2029921 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2029921 g2029921 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 135329 g135329 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 16972) h  -- d = 16972: 5 | 45259+1, 19+1
    rw [show (2:ℕ) ^ 16972 = (2 ^ 200) ^ 84 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 84 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g271553 : 271553 ∈ P := S2 271553 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 271553 (by norm_num))
    have g45259 : 45259 ∈ P := S1 45259 (by norm_num) (by norm_num) (hnz (by norm_num)) 271553 g271553 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 45259 g45259 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 45259 g45259 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17084) h  -- d = 17084: 31 | 2460097+1, 39679+1
    rw [show (2:ℕ) ^ 17084 = (2 ^ 200) ^ 85 * 2 ^ 84 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 85 * 2 ^ 84 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2460097 : 2460097 ∈ P := S2 2460097 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2460097 (by norm_num))
    have g39679 : 39679 ∈ P := S1 39679 (by norm_num) (by norm_num) (hnz (by norm_num)) 2460097 g2460097 (by norm_num)
    exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 2460097 g2460097 39679 g39679 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17428) h  -- d = 17428: 5 | 739+1, 19+1
    rw [show (2:ℕ) ^ 17428 = (2 ^ 200) ^ 87 * 2 ^ 28 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 87 * 2 ^ 28 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g418273 : 418273 ∈ P := S2 418273 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 418273 (by norm_num))
    have g739 : 739 ∈ P := S1 739 (by norm_num) (by norm_num) (hnz (by norm_num)) 418273 g418273 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 739 g739 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 739 g739 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17452) h  -- d = 17452: 5 | 69809+1, 179+1
    rw [show (2:ℕ) ^ 17452 = (2 ^ 200) ^ 87 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 87 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g69809 : 69809 ∈ P := S2 69809 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 69809 (by norm_num))
    have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 69809 g69809 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 69809 g69809 179 g179 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17492) h  -- d = 17492: 7 | 1091+1, 13+1
    rw [show (2:ℕ) ^ 17492 = (2 ^ 200) ^ 87 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 87 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8326193 : 8326193 ∈ P := S2 8326193 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8326193 (by norm_num))
    have g26183 : 26183 ∈ P := S1 26183 (by norm_num) (by norm_num) (hnz (by norm_num)) 8326193 g8326193 (by norm_num)
    have g1091 : 1091 ∈ P := S1 1091 (by norm_num) (by norm_num) (hnz (by norm_num)) 26183 g26183 (by norm_num)
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1091 g1091 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1091 g1091 13 g13 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17564) h  -- d = 17564: 5^2 | 499+1
    rw [show (2:ℕ) ^ 17564 = (2 ^ 200) ^ 87 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 87 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4426129 : 4426129 ∈ P := S2 4426129 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4426129 (by norm_num))
    have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 4426129 g4426129 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17764) h  -- d = 17764: 17 | 2^17764+1, 271+1
    rw [show (2:ℕ) ^ 17764 = (2 ^ 200) ^ 88 * 2 ^ 164 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 88 * 2 ^ 164 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g710561 : 710561 ∈ P := S2 710561 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 710561 (by norm_num))
    have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 710561 g710561 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 271 g271 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17788) h  -- d = 17788: 5 | 1459+1, 19+1
    rw [show (2:ℕ) ^ 17788 = (2 ^ 200) ^ 88 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 88 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2205713 : 2205713 ∈ P := S2 2205713 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2205713 (by norm_num))
    have g52517 : 52517 ∈ P := S1 52517 (by norm_num) (by norm_num) (hnz (by norm_num)) 2205713 g2205713 (by norm_num)
    have g8753 : 8753 ∈ P := S1 8753 (by norm_num) (by norm_num) (hnz (by norm_num)) 52517 g52517 (by norm_num)
    have g1459 : 1459 ∈ P := S1 1459 (by norm_num) (by norm_num) (hnz (by norm_num)) 8753 g8753 (by norm_num)
    have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 (by norm_num)
    have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1459 g1459 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 17804) h  -- d = 17804: 7 | 569729+1, 41+1
    rw [show (2:ℕ) ^ 17804 = (2 ^ 200) ^ 89 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 89 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g569729 : 569729 ∈ P := S2 569729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 569729 (by norm_num))
    have g142433 : 142433 ∈ P := S2 142433 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 142433 (by norm_num))
    have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 142433 g142433 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 569729 g569729 41 g41 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 18092) h  -- d = 18092: 17 | 2^18092+1, 144737+1
    rw [show (2:ℕ) ^ 18092 = (2 ^ 200) ^ 90 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 90 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g144737 : 144737 ∈ P := S2 144737 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 144737 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 144737 g144737 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 18188) h  -- d = 18188: 5^2 | 5383649+1
    rw [show (2:ℕ) ^ 18188 = (2 ^ 200) ^ 90 * 2 ^ 188 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 90 * 2 ^ 188 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g5383649 : 5383649 ∈ P := S2 5383649 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 5383649 (by norm_num))
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5383649 g5383649 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 18572) h  -- d = 18572: 7^2 | 13033+1
    rw [show (2:ℕ) ^ 18572 = (2 ^ 200) ^ 92 * 2 ^ 172 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 92 * 2 ^ 172 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1485761 : 1485761 ∈ P := S2 1485761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1485761 (by norm_num))
    have g13033 : 13033 ∈ P := S1 13033 (by norm_num) (by norm_num) (hnz (by norm_num)) 1485761 g1485761 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13033 g13033 (by norm_num)

theorem w52_c8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ ({18916, 19036, 19268, 19444, 19556, 19724, 19804, 19868, 19876, 20092, 20452, 20476, 20836, 21092, 21292} : Finset ℕ),
      m % (2 * d) ≠ d := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 18916) h  -- d = 18916: 5^2 | 162749+1
    rw [show (2:ℕ) ^ 18916 = (2 ^ 200) ^ 94 * 2 ^ 116 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 94 * 2 ^ 116 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17251393 : 17251393 ∈ P := S2 17251393 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17251393 (by norm_num))
    have g162749 : 162749 ∈ P := S1 162749 (by norm_num) (by norm_num) (hnz (by norm_num)) 17251393 g17251393 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 162749 g162749 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19036) h  -- d = 19036: 5 | 2089+1, 19+1
    rw [show (2:ℕ) ^ 19036 = (2 ^ 200) ^ 95 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 95 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g3045761 : 3045761 ∈ P := S2 3045761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 3045761 (by norm_num))
    have g2089 : 2089 ∈ P := S1 2089 (by norm_num) (by norm_num) (hnz (by norm_num)) 3045761 g3045761 (by norm_num)
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2089 g2089 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2089 g2089 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19268) h  -- d = 19268: 17 | 2^19268+1, 2427769+1
    rw [show (2:ℕ) ^ 19268 = (2 ^ 200) ^ 96 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 96 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g4855537 : 4855537 ∈ P := S2 4855537 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 4855537 (by norm_num))
    have g2427769 : 2427769 ∈ P := S1 2427769 (by norm_num) (by norm_num) (hnz (by norm_num)) 4855537 g4855537 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 2427769 g2427769 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19444) h  -- d = 19444: 7^2 | 4801+1
    rw [show (2:ℕ) ^ 19444 = (2 ^ 200) ^ 97 * 2 ^ 44 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 97 * 2 ^ 44 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g777761 : 777761 ∈ P := S2 777761 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 777761 (by norm_num))
    have g4801 : 4801 ∈ P := S1 4801 (by norm_num) (by norm_num) (hnz (by norm_num)) 777761 g777761 (by norm_num)
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 4801 g4801 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19556) h  -- d = 19556: 5^2 | 199+1
    rw [show (2:ℕ) ^ 19556 = (2 ^ 200) ^ 97 * 2 ^ 156 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 97 * 2 ^ 156 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g2737841 : 2737841 ∈ P := S2 2737841 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 2737841 (by norm_num))
    have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 2737841 g2737841 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19724) h  -- d = 19724: 17^2 | 157793+1
    rw [show (2:ℕ) ^ 19724 = (2 ^ 200) ^ 98 * 2 ^ 124 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 98 * 2 ^ 124 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g157793 : 157793 ∈ P := S2 157793 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 157793 (by norm_num))
    exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 157793 g157793 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19804) h  -- d = 19804: 17 | 2^19804+1, 67+1
    rw [show (2:ℕ) ^ 19804 = (2 ^ 200) ^ 99 * 2 ^ 4 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 99 * 2 ^ 4 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g475297 : 475297 ∈ P := S2 475297 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 475297 (by norm_num))
    have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 475297 g475297 (by norm_num)
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 67 g67 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19868) h  -- d = 19868: 5 | 1337779+1, 66889+1
    rw [show (2:ℕ) ^ 19868 = (2 ^ 200) ^ 99 * 2 ^ 68 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 99 * 2 ^ 68 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g8026673 : 8026673 ∈ P := S2 8026673 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 8026673 (by norm_num))
    have g1337779 : 1337779 ∈ P := S1 1337779 (by norm_num) (by norm_num) (hnz (by norm_num)) 8026673 g8026673 (by norm_num)
    have g66889 : 66889 ∈ P := S1 66889 (by norm_num) (by norm_num) (hnz (by norm_num)) 1337779 g1337779 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1337779 g1337779 66889 g66889 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 19876) h  -- d = 19876: 17 | 2^19876+1, 6519329+1
    rw [show (2:ℕ) ^ 19876 = (2 ^ 200) ^ 99 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 99 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g6519329 : 6519329 ∈ P := S2 6519329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 6519329 (by norm_num))
    exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17 (by norm_num)) 6519329 g6519329 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 20092) h  -- d = 20092: 5 | 80369+1, 19+1
    rw [show (2:ℕ) ^ 20092 = (2 ^ 200) ^ 100 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 100 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g80369 : 80369 ∈ P := S2 80369 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 80369 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 80369 g80369 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 80369 g80369 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 20452) h  -- d = 20452: 7 | 13+1, 660757+1
    rw [show (2:ℕ) ^ 20452 = (2 ^ 200) ^ 102 * 2 ^ 52 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 102 * 2 ^ 52 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g17179681 : 17179681 ∈ P := S2 17179681 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 17179681 (by norm_num))
    have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 17179681 g17179681 (by norm_num)
    have g660757 : 660757 ∈ P := S1 660757 (by norm_num) (by norm_num) (hnz (by norm_num)) 17179681 g17179681 (by norm_num)
    exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 660757 g660757 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 20476) h  -- d = 20476: 5 | 573329+1, 29+1
    rw [show (2:ℕ) ^ 20476 = (2 ^ 200) ^ 102 * 2 ^ 76 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 102 * 2 ^ 76 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g573329 : 573329 ∈ P := S2 573329 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 573329 (by norm_num))
    have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 573329 g573329 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 573329 g573329 29 g29 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 20836) h  -- d = 20836: 5^2 | 375049+1
    rw [show (2:ℕ) ^ 20836 = (2 ^ 200) ^ 104 * 2 ^ 36 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 104 * 2 ^ 36 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g750097 : 750097 ∈ P := S2 750097 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 750097 (by norm_num))
    have g375049 : 375049 ∈ P := S1 375049 (by norm_num) (by norm_num) (hnz (by norm_num)) 750097 g750097 (by norm_num)
    exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 375049 g375049 (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 21092) h  -- d = 21092: 5 | 12317729+1, 19+1
    rw [show (2:ℕ) ^ 21092 = (2 ^ 200) ^ 105 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 105 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g12317729 : 12317729 ∈ P := S2 12317729 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 12317729 (by norm_num))
    have g31638001 : 31638001 ∈ P := S2 31638001 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 31638001 (by norm_num))
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 31638001 g31638001 (by norm_num)
    exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12317729 g12317729 19 g19 (by norm_num) (by norm_num)) (by norm_num)
  · have hd := two_pow_add_one_dvd_of_odd_mul (d := 21292) h  -- d = 21292: 7^2 | 1362689+1
    rw [show (2:ℕ) ^ 21292 = (2 ^ 200) ^ 106 * 2 ^ 92 by rw [← pow_mul, ← pow_add]] at hd
    have R : ∀ x : ℕ, x ∣ (2 ^ 200) ^ 106 * 2 ^ 92 + 1 → x ∣ 2 ^ m + 1 := fun x hx => hx.trans hd
    have g1362689 : 1362689 ∈ P := S2 1362689 (by norm_num) (by norm_num) (hnz (by norm_num)) (R 1362689 (by norm_num))
    exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1362689 g1362689 (by norm_num)

theorem w52_sieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    ∀ d ∈ (({412, 428, 436, 508, 548, 604, 628, 652, 892, 908, 932, 1076, 1084, 1172, 1324, 1388, 1396, 1468, 1492, 1604, 1636, 1756, 1796, 1868, 2188} : Finset ℕ) ∪
      ({2284, 2348, 2372, 2428, 2468, 2524, 2564, 2572, 2612, 2636, 2908, 2972, 3028, 3076, 3092, 3244, 3284, 3292, 3412, 3428, 3628, 3644, 3748, 4084, 4132} : Finset ℕ) ∪
      ({4348, 4364, 4412, 4436, 4492, 4516, 4684, 4868, 4924, 4996, 5036, 5108, 5188, 5212, 5276, 5308, 5492, 5524, 5716, 5732, 5804, 5836, 5932, 5948, 5996} : Finset ℕ) ∪
      ({6124, 6268, 6388, 6404, 6428, 6652, 6676, 6884, 6932, 7108, 7132, 7324, 7444, 7516, 7556, 7796, 7804, 7892, 7916, 7948, 7988, 7996, 8212, 8276, 8324} : Finset ℕ) ∪
      ({8332, 8396, 8452, 8524, 8644, 8812, 8852, 9068, 9124, 9172, 9388, 9572, 9692, 9748, 9788, 9892, 9908, 10012, 10084, 10172, 10204, 10228, 10532, 10588, 10796} : Finset ℕ) ∪
      ({10876, 10916, 10924, 11156, 11188, 11276, 11516, 11548, 11612, 11636, 11668, 11812, 12004, 12044, 12076, 12148, 12356, 12484, 12668, 12724, 12748, 12868, 13004, 13204, 13228} : Finset ℕ) ∪
      ({13316, 13444, 13484, 13564, 13796, 13852, 13996, 14068, 14108, 14228, 14284, 14428, 14452, 14524, 14764, 14836, 14876, 14932, 15076, 15292, 15388, 15404, 15452, 15628, 15692} : Finset ℕ) ∪
      ({15772, 16028, 16052, 16108, 16196, 16292, 16372, 16444, 16612, 16628, 16804, 16844, 16916, 16972, 17084, 17428, 17452, 17492, 17564, 17764, 17788, 17804, 18092, 18188, 18572} : Finset ℕ) ∪
      ({18916, 19036, 19268, 19444, 19556, 19724, 19804, 19868, 19876, 20092, 20452, 20476, 20836, 21092, 21292} : Finset ℕ)),
      m % (2 * d) ≠ d := by
  intro d hd
  simp only [Finset.mem_union] at hd
  rcases hd with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
  · exact w52_c0 hP E d h
  · exact w52_c1 hP E d h
  · exact w52_c2 hP E d h
  · exact w52_c3 hP E d h
  · exact w52_c4 hP E d h
  · exact w52_c5 hP E d h
  · exact w52_c6 hP E d h
  · exact w52_c7 hP E d h
  · exact w52_c8 hP E d h

-- Section 2. The step.
set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H3_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff he hmod hlo hs0 => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  rw [he] at E
  have t := w52_sieve hP E
  rw [ha] at t
  by_cases hc : padicValNat 2 n % 584 = 292
  · exact (h1 n h hiff he hmod hlo hs0 hc t).trans (le_max_left _ _)
  · exact (h2 n h hiff he hmod hlo hs0 hc t).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H3_R1_H2_R1
