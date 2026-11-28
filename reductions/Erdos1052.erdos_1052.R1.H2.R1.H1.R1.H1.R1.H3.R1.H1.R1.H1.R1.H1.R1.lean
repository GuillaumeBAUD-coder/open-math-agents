import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H1.R1.H1.R1
-- Credit: @heavydawson (quadratic reciprocity infinite-family idea credited to @AlfredMelson, note #194073)
-- When e = n.factorization 3 satisfies e % 4 = 2, 5 | 1 + 3^2 | 1 + 3^e, so S8 forbids any simple
-- prime r in P with r % 5 = 4. Using quadratic reciprocity (legendreSym.at_two and legendreSym.at_three):
--   1. Every prime r with r % 5 = 4 and (r % 8 = 3 or r % 8 = 5) satisfies a % (r - 1) != (r - 1) / 2.
--   2. Every prime r with r % 5 = 4 and (r % 12 = 5 or r % 12 = 7) satisfies e % (r - 1) != (r - 1) / 2.
-- In addition, we eliminate d = 2048 (974849 | 2^2048 + 1, 5^2 | 974849 + 1) and d = 4096
-- (114689 | 2^4096 + 1, 5 | 114689 + 1 colliding with 5 | 1 + 3^e), and split the residual branch
-- into three 2-adic valuation classes (a odd, a % 8 = 4, and 8 | a; a % 4 = 2 is already excluded).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1 hiding H1 H2 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 = 2 →
    padicValNat 2 n % 2 = 1 →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 12 = 5 ∨ r % 12 = 7) →
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
    (∀ d ∈ ({2, 6, 9, 11, 13, 21, 23, 158, 169, 219, 272, 302, 332, 356, 373} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 = 2 →
    padicValNat 2 n % 8 = 4 →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 12 = 5 ∨ r % 12 = 7) →
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
    (∀ d ∈ ({2, 6, 9, 11, 13, 21, 23, 158, 169, 219, 272, 302, 332, 356, 373} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    800 < n.factorization 3 →
    n.factorization 3 % 4 = 2 →
    padicValNat 2 n % 8 = 0 →
    padicValNat 2 n % 4096 ≠ 2048 →
    padicValNat 2 n % 8192 ≠ 4096 →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2) →
    (∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 12 = 5 ∨ r % 12 = 7) →
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
    (∀ d ∈ ({2, 6, 9, 11, 13, 21, 23, 158, 169, 219, 272, 302, 332, 356, 373} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1: Balance equation setup and Legendre symbol divisibility lemmas.

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
  haveI : Fact r.Prime := ⟨hr⟩
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

theorem dvd_five_three_pow {e : ℕ} (he4 : e % 4 = 2) : 5 ∣ 1 + 3 ^ e := by
  have h1 : 5 ∣ 1 + 3 ^ 2 := by norm_num
  have h2 : 1 + 3 ^ 2 ∣ 1 + 3 ^ e := one_add_pow_dvd_of_odd_mul (by omega : e % (2 * 2) = 2)
  exact h1.trans h2

-- Section 2: Infinite exclusion families from S8 with 5 | 1 + 3^e.

theorem excl_a_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he4 : e % 4 = 2) {r : ℕ} (hr : r.Prime) (hr5 : r % 5 = 4) (h8 : r % 8 = 3 ∨ r % 8 = 5)
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
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_five_three_pow he4) r hrP (by omega)

theorem excl_e_family {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he4 : e % 4 = 2) {r : ℕ} (hr : r.Prime) (hr5 : r % 5 = 4) (h12 : r % 12 = 5 ∨ r % 12 = 7)
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
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_five_three_pow he4) r hrP (by omega)

-- Section 3: Fermat kills d = 2048 and d = 4096.

theorem dvd_two_pow_add_one {p d : ℕ}
    (h : ((2 : ZMod p) ^ d + 1) = 0) : p ∣ 2 ^ d + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

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

theorem kill_d4096 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he4 : e % 4 = 2) (hmod : m % 8192 = 4096) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP hK E
  have hd : 2 ^ 4096 + 1 ∣ 2 ^ m + 1 := by
    have h := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 4096) (by omega : m % (2 * 4096) = 4096)
    rwa [add_comm 1 (2 ^ 4096), add_comm 1 (2 ^ m)] at h
  have g1 : 114689 ∈ P := S2 114689 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) (dvd_five_three_pow he4) 114689 g1 (by norm_num)

-- Section 4: Main reduction.

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he800 he4 hE hA1 hA2 hA3 => ?_⟩
  obtain ⟨P, hP, E⟩ := balance_of_only_three h hiff
  have ha_inf : ∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 8 = 3 ∨ r % 8 = 5) →
      padicValNat 2 n % (r - 1) ≠ (r - 1) / 2 :=
    fun r hr hr5 h8 hm => excl_a_family hP E he4 hr hr5 h8 hm
  have he_inf : ∀ r : ℕ, r.Prime → r % 5 = 4 → (r % 12 = 5 ∨ r % 12 = 7) →
      n.factorization 3 % (r - 1) ≠ (r - 1) / 2 :=
    fun r hr hr5 h12 hm => excl_e_family hP E he4 hr hr5 h12 hm
  by_cases hodd : padicValNat 2 n % 2 = 1
  · exact (h1 n h hiff he800 he4 hodd ha_inf he_inf hE hA1 hA2 hA3).trans (le_max_left _ _)
  · have h4ne : padicValNat 2 n % 4 ≠ 2 := hA3 2 (by simp)
    by_cases h8m : padicValNat 2 n % 8 = 4
    · exact (h2 n h hiff he800 he4 h8m ha_inf he_inf hE hA1 hA2 hA3).trans
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · have h8 : padicValNat 2 n % 8 = 0 := by omega
      have h2048 : padicValNat 2 n % 4096 ≠ 2048 := fun hm => kill_d2048 hP E hm
      have h4096 : padicValNat 2 n % 8192 ≠ 4096 := fun hm => kill_d4096 hP E he4 hm
      exact (h3 n h hiff he800 he4 h8 h2048 h4096 ha_inf he_inf hE hA1 hA2 hA3).trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H1_R1_H1_R1
