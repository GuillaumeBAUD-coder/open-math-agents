import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H2.R1
-- Credit: @heavydawson
-- Splits e > 800, e % 4 != 2 into four branches:
--   H1: e % 6 = 3 (7 | 1 + 3^3 | 1 + 3^e), with infinite quadratic-reciprocity exclusions
--       for primes r = 6 mod 7 on both a and e, plus explicit kills d = 6, 16, 2048.
--   H2: e % 8 = 4 (41 | 1 + 3^4 | 1 + 3^e -> 41 in P, 7 | 41 + 1), with infinite quadratic-
--       reciprocity exclusions for primes r = 6 mod 7 (r != 41) on both a and e, plus d = 6, 16, 2048.
--   H3: e % 2 = 1 and e % 6 != 3, with d = 2048 excluded.
--   H4: e % 8 = 0, with d = 2048 excluded.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1 hiding H1 H2 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 6 = 3 →
    padicValNat 2 n % 12 ≠ 6 →
    padicValNat 2 n % 32 ≠ 16 →
    padicValNat 2 n % 4096 ≠ 2048 →
    (∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    (∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 12 = 5 ∨ r % 12 = 7) →
      n.factorization 3 % (r - 1) ≠ (r - 1) / 2) →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 8 = 4 →
    padicValNat 2 n % 12 ≠ 6 →
    padicValNat 2 n % 32 ≠ 16 →
    padicValNat 2 n % 4096 ≠ 2048 →
    (∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    (∀ r : ℕ, r.Prime → r ≠ 41 → r % 7 = 6 → (r % 12 = 5 ∨ r % 12 = 7) →
      n.factorization 3 % (r - 1) ≠ (r - 1) / 2) →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 2 = 1 →
    n.factorization 3 % 6 ≠ 3 →
    padicValNat 2 n % 4096 ≠ 2048 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 8 = 0 →
    padicValNat 2 n % 4096 ≠ 2048 →
    (∀ d ∈ ({502, 503, 508, 509, 512, 514, 521, 523, 524, 526, 538, 541, 542, 547, 548, 554, 556, 557,
        562, 563, 566, 569, 571, 586, 587, 593, 596, 599, 601, 604, 607, 613, 614, 617, 619,
        622, 626, 628, 631, 634, 641, 643, 647, 652, 653, 659, 661, 662, 668, 673, 674, 677,
        683, 691, 692, 694, 698, 701, 706, 709, 716, 718, 719, 724, 727, 733, 734, 739, 743,
        746, 751, 757, 758, 761, 766, 769, 772, 773, 778, 787, 788, 794, 796, 797} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({31, 40, 41, 43, 44, 47, 49, 53, 58, 61, 71, 73, 79, 88, 89, 92, 93, 101, 103, 104, 107, 109,
        113, 127, 128, 129, 136, 137, 139, 148, 151, 159, 161, 163, 164, 166, 167, 172, 173,
        174, 176, 178, 179, 181, 183, 184, 187, 188, 191, 193, 194, 197, 199, 200} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1: Balance equation and Legendre symbol divisibility helpers.

theorem balance_of_only_three {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (2 ^ padicValNat 2 n + 1) * (1 + 3 ^ n.factorization 3) * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * 3 ^ n.factorization 3 * ∏ p ∈ P, p := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have h3n : 3 ∣ n := (dvd_pow_self 3 (by norm_num)).trans h3sq.2.2
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  exact ⟨_, hP, E⟩

theorem dvd_pow_add_one_of_legendre_neg_one {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hleg : @legendreSym r ⟨hr⟩ (a : ℤ) = -1) :
    r ∣ a ^ ((r - 1) / 2) + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
  have hdiv : r / 2 = (r - 1) / 2 := by omega
  have hpow : ((a : ZMod r) ^ (r / 2)) = (-1 : ZMod r) := by
    have h1 := legendreSym.eq_pow r (a : ℤ)
    rw [hleg] at h1
    simpa only [Int.cast_neg, Int.cast_one, Int.cast_natCast] using h1.symm
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [← hdiv, hpow]
  ring

theorem dvd_two_pow_half_add_one {r : ℕ} (hr : r.Prime) (h8 : r % 8 = 3 ∨ r % 8 = 5) :
    r ∣ 2 ^ ((r - 1) / 2) + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  apply dvd_pow_add_one_of_legendre_neg_one hr hr2
  change legendreSym r 2 = -1
  rw [legendreSym.at_two hr2]
  have hmod : (r : ZMod 8) = 3 ∨ (r : ZMod 8) = 5 := by
    rcases h8 with h | h
    · left; rw [← ZMod.natCast_mod, h]; rfl
    · right; rw [← ZMod.natCast_mod, h]; rfl
  rcases hmod with h | h <;> rw [h] <;> decide

theorem dvd_three_pow_half_add_one {r : ℕ} (hr : r.Prime) (h12 : r % 12 = 5 ∨ r % 12 = 7) :
    r ∣ 3 ^ ((r - 1) / 2) + 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  apply dvd_pow_add_one_of_legendre_neg_one hr hr2
  have hqr := legendreSym.quadratic_reciprocity (p := 3) (q := r) (by norm_num) hr2 hr3.symm
  have h3r : legendreSym 3 (r : ℤ) = legendreSym 3 ((r % 3 : ℕ) : ℤ) := by
    rw [legendreSym.mod 3 (r : ℤ), ← Int.natCast_emod]
  rcases h12 with h | h
  · have hmod3 : r % 3 = 2 := by omega
    have hleg3 : legendreSym 3 (r : ℤ) = -1 := by
      rw [h3r, hmod3]
      change legendreSym 3 2 = -1
      rw [legendreSym.at_two (by norm_num)]
      decide
    have heven : Even (r / 2) := ⟨r / 4, by omega⟩
    rw [hleg3, show (3 : ℕ) / 2 = 1 from rfl, one_mul, heven.neg_one_pow] at hqr
    linarith
  · have hmod3 : r % 3 = 1 := by omega
    have hleg3 : legendreSym 3 (r : ℤ) = 1 := by
      rw [h3r, hmod3]
      change legendreSym 3 1 = 1
      exact legendreSym.at_one 3
    have hodd : Odd (r / 2) := ⟨r / 4, by omega⟩
    rw [hleg3, show (3 : ℕ) / 2 = 1 from rfl, one_mul, hodd.neg_one_pow] at hqr
    linarith

theorem dvd_two_pow_add_one {p d : ℕ}
    (h : ((2 : ZMod p) ^ d + 1) = 0) : p ∣ 2 ^ d + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

theorem dvd_seven_three_pow {e : ℕ} (he6 : e % 6 = 3) : 7 ∣ 1 + 3 ^ e := by
  have h1 : 7 ∣ 1 + 3 ^ 3 := by norm_num
  have h2 : 1 + 3 ^ 3 ∣ 1 + 3 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 3) = 3)
  exact h1.trans h2

theorem dvd_41_three_pow {e : ℕ} (he8 : e % 8 = 4) : 41 ∣ 1 + 3 ^ e := by
  have h1 : 41 ∣ 1 + 3 ^ 4 := by norm_num
  have h2 : 1 + 3 ^ 4 ∣ 1 + 3 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 4) = 4)
  exact h1.trans h2

-- Section 2: Unconditional Fermat kill d = 2048.

theorem kill_d2048 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hmod : m % 4096 = 2048) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have hd : 2 ^ 2048 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 2048) (by omega : m % (2 * 2048) = 2048)
    rwa [add_comm 1 (2 ^ 2048), add_comm 1 (2 ^ m)] at h
  have g1 : 974849 ∈ P := S2 974849 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 974849 g1 (by norm_num)

-- Section 3: Exclusions for e % 6 = 3 (7 | 1 + 3^e).

theorem excl_mod6_a_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he6 : e % 6 = 3) {r : ℕ} (hr : r.Prime) (hr7 : r % 7 = 6) (h8 : r % 8 = 3 ∨ r % 8 = 5)
    (hmod : m % (r - 1) = (r - 1) / 2) : False := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP hK E
  have hd_eq : 2 * ((r - 1) / 2) = r - 1 := by
    have := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hdiv : 2 ^ ((r - 1) / 2) + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := (r - 1) / 2) (by rw [hd_eq]; exact hmod)
    rwa [add_comm 1 (2 ^ ((r - 1) / 2)), add_comm 1 (2 ^ m)] at h
  have hrP : r ∈ P := S2 r hr hr2 (hnz hr3) ((dvd_two_pow_half_add_one hr h8).trans hdiv)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_seven_three_pow he6) r hrP (by omega)

theorem excl_mod6_e_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he6 : e % 6 = 3) {r : ℕ} (hr : r.Prime) (hr7 : r % 7 = 6) (h12 : r % 12 = 5 ∨ r % 12 = 7)
    (hmod : e % (r - 1) = (r - 1) / 2) : False := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, -, -, -, -, S7, S8⟩ := facts hP hK E
  have hd_eq : 2 * ((r - 1) / 2) = r - 1 := by
    have := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hdiv : 1 + 3 ^ ((r - 1) / 2) ∣ 1 + 3 ^ e :=
    one_add_pow_dvd_of_odd_mul (z := 3) (e0 := (r - 1) / 2) (by rw [hd_eq]; exact hmod)
  have hr3d : r ∣ 1 + 3 ^ ((r - 1) / 2) := by
    rw [add_comm]
    exact dvd_three_pow_half_add_one hr h12
  have hrP : r ∈ P := S7 r hr hr2 (hnz hr3) (hr3d.trans hdiv)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_seven_three_pow he6) r hrP (by omega)

theorem kill_mod6_d6 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he6 : e % 6 = 3) (hmod : m % 12 = 6) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP hK E
  have hd : 2 ^ 6 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 6) (by omega : m % (2 * 6) = 6)
    rwa [add_comm 1 (2 ^ 6), add_comm 1 (2 ^ m)] at h
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 6 + 1).trans hd)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_seven_three_pow he6) 13 g13 (by norm_num)

theorem kill_mod6_d16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he6 : e % 6 = 3) (hmod : m % 32 = 16) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP hK E
  have hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 16) (by omega : m % (2 * 16) = 16)
    rwa [add_comm 1 (2 ^ 16), add_comm 1 (2 ^ m)] at h
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_seven_three_pow he6) 83 g83 (by norm_num)

-- Section 4: Exclusions for e % 8 = 4 (41 | 1 + 3^e -> 41 in P, 7 | 41 + 1).

theorem excl_mod8_a_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he8 : e % 8 = 4) {r : ℕ} (hr : r.Prime) (hr7 : r % 7 = 6) (h8 : r % 8 = 3 ∨ r % 8 = 5)
    (hmod : m % (r - 1) = (r - 1) / 2) : False := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hr41 : r ≠ 41 := by omega
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_41_three_pow he8)
  have hd_eq : 2 * ((r - 1) / 2) = r - 1 := by
    have := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hdiv : 2 ^ ((r - 1) / 2) + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := (r - 1) / 2) (by rw [hd_eq]; exact hmod)
    rwa [add_comm 1 (2 ^ ((r - 1) / 2)), add_comm 1 (2 ^ m)] at h
  have hrP : r ∈ P := S2 r hr hr2 (hnz hr3) ((dvd_two_pow_half_add_one hr h8).trans hdiv)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 r hrP (by norm_num) (by omega)
  omega

theorem excl_mod8_e_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he8 : e % 8 = 4) {r : ℕ} (hr : r.Prime) (hr41 : r ≠ 41) (hr7 : r % 7 = 6)
    (h12 : r % 12 = 5 ∨ r % 12 = 7) (hmod : e % (r - 1) = (r - 1) / 2) : False := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, -, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_41_three_pow he8)
  have hd_eq : 2 * ((r - 1) / 2) = r - 1 := by
    have := hr.eq_two_or_odd.resolve_left hr2
    omega
  have hdiv : 1 + 3 ^ ((r - 1) / 2) ∣ 1 + 3 ^ e :=
    one_add_pow_dvd_of_odd_mul (z := 3) (e0 := (r - 1) / 2) (by rw [hd_eq]; exact hmod)
  have hr3d : r ∣ 1 + 3 ^ ((r - 1) / 2) := by
    rw [add_comm]
    exact dvd_three_pow_half_add_one hr h12
  have hrP : r ∈ P := S7 r hr hr2 (hnz hr3) (hr3d.trans hdiv)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 r hrP (by norm_num) (by omega)
  omega

theorem kill_mod8_d6 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he8 : e % 8 = 4) (hmod : m % 12 = 6) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_41_three_pow he8)
  have hd : 2 ^ 6 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 6) (by omega : m % (2 * 6) = 6)
    rwa [add_comm 1 (2 ^ 6), add_comm 1 (2 ^ m)] at h
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 6 + 1).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill_mod8_d16 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he8 : e % 8 = 4) (hmod : m % 32 = 16) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_41_three_pow he8)
  have hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 16) (by omega : m % (2 * 16) = 16)
    rwa [add_comm 1 (2 ^ 16), add_comm 1 (2 ^ m)] at h
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 83 g83 (by norm_num) (by norm_num)
  omega

-- Section 5: Main reduction.

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h hiff he800 he4 hE hA1 hA2 => ?_⟩
  obtain ⟨P, hP, E⟩ := balance_of_only_three h hiff
  have h2048 : padicValNat 2 n % 4096 ≠ 2048 := fun hm => kill_d2048 hP E hm
  by_cases hodd : n.factorization 3 % 2 = 1
  · by_cases he6 : n.factorization 3 % 6 = 3
    · have hd6 : padicValNat 2 n % 12 ≠ 6 := fun hm => kill_mod6_d6 hP E he6 hm
      have hd16 : padicValNat 2 n % 32 ≠ 16 := fun hm => kill_mod6_d16 hP E he6 hm
      have ha_inf : ∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 8 = 3 ∨ r % 8 = 5) →
          padicValNat 2 n % (r - 1) ≠ (r - 1) / 2 :=
        fun r hr hr7 h8 hm => excl_mod6_a_family hP E he6 hr hr7 h8 hm
      have he_inf : ∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 12 = 5 ∨ r % 12 = 7) →
          n.factorization 3 % (r - 1) ≠ (r - 1) / 2 :=
        fun r hr hr7 h12 hm => excl_mod6_e_family hP E he6 hr hr7 h12 hm
      exact (h1 n h hiff he800 he6 hd6 hd16 h2048 ha_inf he_inf hE hA1 hA2).trans
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact (h3 n h hiff he800 hodd he6 h2048 hE hA1 hA2).trans
        (le_trans (le_max_left _ _) (le_max_right _ _))
  · by_cases he8 : n.factorization 3 % 8 = 4
    · have hd6 : padicValNat 2 n % 12 ≠ 6 := fun hm => kill_mod8_d6 hP E he8 hm
      have hd16 : padicValNat 2 n % 32 ≠ 16 := fun hm => kill_mod8_d16 hP E he8 hm
      have ha_inf : ∀ r : ℕ, r.Prime → r % 7 = 6 → (r % 8 = 3 ∨ r % 8 = 5) →
          padicValNat 2 n % (r - 1) ≠ (r - 1) / 2 :=
        fun r hr hr7 h8 hm => excl_mod8_a_family hP E he8 hr hr7 h8 hm
      have he_inf : ∀ r : ℕ, r.Prime → r ≠ 41 → r % 7 = 6 → (r % 12 = 5 ∨ r % 12 = 7) →
          n.factorization 3 % (r - 1) ≠ (r - 1) / 2 :=
        fun r hr hr41 hr7 h12 hm => excl_mod8_e_family hP E he8 hr hr41 hr7 h12 hm
      exact (h2 n h hiff he800 he8 hd6 hd16 h2048 ha_inf he_inf hE hA1 hA2).trans
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · have he8z : n.factorization 3 % 8 = 0 := by omega
      exact (h4 n h hiff he800 he8z h2048 hE hA1 hA2).trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H2_R1
