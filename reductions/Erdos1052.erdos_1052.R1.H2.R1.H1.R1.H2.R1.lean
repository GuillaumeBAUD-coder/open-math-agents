import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1
-- Credit: @adammcarter
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1 (exactly one repeated odd prime z,
-- 5 <= z < 2100, with the proved exponent restrictions) by z and by the exponent e of z, with
-- the results of rounds 8, 10 and 13 built in.  Proving the four H proves the step.
--
-- Notation: n unitary perfect, z the only odd prime with z^2 | n (every other odd prime divides n
-- exactly once), e = n.factorization z, a = padicValNat 2 n.  The parent gives, for z = 5,
-- e = 2, e = 4 or e >= 41.  A number x is an ODD MULTIPLE of d when x mod 2d = d.  The 2-adic
-- valuation of a is r exactly when a mod 2^(r+1) = 2^r; then the Fermat number 2^(2^r) + 1
-- divides 2^a + 1.
--
-- PROVED BELOW (no hypothesis needed; the lemmas of this file, the rest is imported from the
-- parent reduction):
--   Every z: v2(a) is not r for r = 4..10, 12..19, 21, 22, 23, 25..32, and not 2 (unless z = 17),
--     not 3 (unless z = 11, 43 or 257), not 11 (unless z = 743).  For a odd: a mod 6 is not 3;
--     a mod 10 is not 5 unless z = 11; a mod 14 is not 7 unless z = 11 or 43; a mod 6 is not 5
--     when z = 5 or z = 1 mod 3.  a mod 20 is not 10 unless z = 5; a mod 28 is not 14 unless
--     z = 5 or 29.  Method: a prime factor of the Fermat number (or of 2^d + 1) is a simple prime
--     of n and starts a forced chain of simple primes in the balance equation
--     (2^a + 1)(1 + z^e) prod (p + 1) = 2^(a+1) z^e prod p, ending at a prime with two sources or
--     a square in some p + 1.  Large primes are certified by the Lucas test.
--     (H2_two_adic_classes, H2_two_adic_r14, H2_two_adic_high)
--   z = 5, e = 2: a odd => every prime factor of a is >= 43; a = 2 mod 4 => every odd prime
--     factor of a is >= 101 (five_two_odd_prime_factor, five_two_two_mod_four_prime_factor).
--   z = 5, e = 4: a is even (five_four_two_adic_even, a weight search tree for odd a).
--   The lower bounds 43 <= a (H1) and 128 <= a (H2) cost nothing: main bounds every a < 128
--     directly.  (Round 13 also proved them: e = 2 forces a >= 43, and e = 4 with a even and
--     a < 128 forces a = 18 and n = Wall's number; those proofs are not needed here.)
--
-- H1 (OPEN): z = 5, e = 2, a >= 43, with the restrictions above.
-- H2 (OPEN): z = 5, e = 4, a even, a >= 128, with the restrictions above.
-- H3 (OPEN): z = 5, e >= 41 (with the parent's restrictions on e), with the restrictions above.
-- H4 (OPEN): 7 <= z < 2100 (with the parent's restrictions on e), with the restrictions above.
-- No known unitary perfect number satisfies the hypotheses of any H: Wall's number
-- 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313 has z = 5, e = 4, a = 18 < 128.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- H1: a = v2(n) is bounded over the unitary perfect numbers whose only repeated odd prime is 5,
-- with 5^2 exactly dividing n, a >= 43, every prime factor of a at least 43 when a is odd, every
-- odd prime factor of a at least 101 when a = 2 mod 4, a mod 6 not 5, and v2(a) not in R5.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n →
    (padicValNat 2 n % 2 = 1 → ∀ d : ℕ, d.Prime → d ∣ padicValNat 2 n → 43 ≤ d) →
    (padicValNat 2 n % 4 = 2 → ∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 101 ≤ d) →
    padicValNat 2 n % 6 ≠ 5 →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a = v2(n) is bounded over the unitary perfect numbers whose only repeated odd prime is 5,
-- with 5^4 exactly dividing n, a even, a >= 128, and v2(a) not in R5.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 4 →
    Even (padicValNat 2 n) → 128 ≤ padicValNat 2 n →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H3: a = v2(n) is bounded over the unitary perfect numbers whose only repeated odd prime is 5,
-- with exponent e >= 41, e = 1 mod 6 when e is odd, e no odd multiple of any d in D5 (the set
-- listed), a mod 6 not 3 or 5, a mod 10 not 5, a mod 14 not 7, and v2(a) not in R5.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → 41 ≤ n.factorization 5 →
    (Odd (n.factorization 5) → n.factorization 5 % 6 = 1) →
    (∀ d ∈ ({5, 6, 7, 8, 10, 12, 13, 14, 16, 19, 20, 22, 26, 28, 29, 31, 32, 34, 37, 38} : Finset ℕ),
      n.factorization 5 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → padicValNat 2 n % 6 ≠ 5 → padicValNat 2 n % 10 ≠ 5 →
    padicValNat 2 n % 14 ≠ 7 →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H4: a = v2(n) is bounded over the unitary perfect numbers with exactly one repeated odd prime
-- z, 7 <= z < 2100, with the parent's restrictions on its exponent (e = 1 mod 6 when z = 2 mod 3
-- and e is odd; for z = 7, e >= 41 and e no odd multiple of any d in D7), and the 2-adic classes
-- of a listed in the header (with their exceptions for z = 11, 17, 29, 43, 257, 743).
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    (z % 3 = 2 → Odd (n.factorization z) → n.factorization z % 6 = 1) →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) → (z % 3 = 1 → padicValNat 2 n % 6 ≠ 5) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Lemmas from rounds 8, 10 and 13 (Erdos1052OpenCore8/10/13.lean), restricted to what main uses;
-- lemmas identical to the parent's are taken from the parent.

theorem prime_611065913 : Nat.Prime 611065913 := by
  refine lucas_primality 611065913 (3 : ZMod 611065913) ?_ (fun q hq hd => ?_)
  · rw [show 611065913 - 1 = 611065912 from by norm_num]
    reduce_mod_char
  · have e : 611065913 - 1 = [2 ^ 3, 1013 ^ 1, 75403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 2 = 305532956 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 305532956 = ((611065912 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 1013 = 603224 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 603224 = ((340408484 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 75403 = 8104 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 8104 = ((306963438 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_825753601 : Nat.Prime 825753601 := by
  refine lucas_primality 825753601 (23 : ZMod 825753601) ?_ (fun q hq hd => ?_)
  · rw [show 825753601 - 1 = 825753600 from by norm_num]
    reduce_mod_char
  · have e : 825753601 - 1 = [2 ^ 19, 3 ^ 2, 5 ^ 2, 7 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 2 = 412876800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 412876800 = ((825753600 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 3 = 275251200 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 275251200 = ((769286199 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 5 = 165150720 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 165150720 = ((50952529 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 7 = 117964800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 117964800 = ((709772069 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1389171559 : Nat.Prime 1389171559 := by
  refine lucas_primality 1389171559 (3 : ZMod 1389171559) ?_ (fun q hq hd => ?_)
  · rw [show 1389171559 - 1 = 1389171558 from by norm_num]
    reduce_mod_char
  · have e : 1389171559 - 1 = [2 ^ 1, 3 ^ 1, 17 ^ 2, 801137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1389171559 - 1) / 2 = 694585779 from by norm_num]
      have h2 : (3 : ZMod 1389171559) ^ 694585779 = ((1389171558 : ℕ) : ZMod 1389171559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1389171559 - 1) / 3 = 463057186 from by norm_num]
      have h2 : (3 : ZMod 1389171559) ^ 463057186 = ((667583411 : ℕ) : ZMod 1389171559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1389171559 - 1) / 17 = 81715974 from by norm_num]
      have h2 : (3 : ZMod 1389171559) ^ 81715974 = ((745221501 : ℕ) : ZMod 1389171559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1389171559 - 1) / 801137 = 1734 from by norm_num]
      have h2 : (3 : ZMod 1389171559) ^ 1734 = ((893295967 : ℕ) : ZMod 1389171559) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3853149761 : Nat.Prime 3853149761 := by
  refine lucas_primality 3853149761 (6 : ZMod 3853149761) ?_ (fun q hq hd => ?_)
  · rw [show 3853149761 - 1 = 3853149760 from by norm_num]
    reduce_mod_char
  · have e : 3853149761 - 1 = [2 ^ 6, 5 ^ 1, 719 ^ 1, 16747 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 2 = 1926574880 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 1926574880 = ((3853149760 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 5 = 770629952 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 770629952 = ((2694843562 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 719 = 5359040 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 5359040 = ((803003822 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 16747 = 230080 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 230080 = ((3140195378 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18533742247 : Nat.Prime 18533742247 := by
  refine lucas_primality 18533742247 (6 : ZMod 18533742247) ?_ (fun q hq hd => ?_)
  · rw [show 18533742247 - 1 = 18533742246 from by norm_num]
    reduce_mod_char
  · have e : 18533742247 - 1 = [2 ^ 1, 3 ^ 3, 181 ^ 1, 1896229 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 2 = 9266871123 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 9266871123 = ((18533742246 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 3 = 6177914082 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 6177914082 = ((17436423204 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 181 = 102396366 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 102396366 = ((4318986892 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 1896229 = 9774 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 9774 = ((16378712013 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70525124609 : Nat.Prime 70525124609 := by
  refine lucas_primality 70525124609 (3 : ZMod 70525124609) ?_ (fun q hq hd => ?_)
  · rw [show 70525124609 - 1 = 70525124608 from by norm_num]
    reduce_mod_char
  · have e : 70525124609 - 1 = [2 ^ 21, 33629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 2 = 35262562304 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 35262562304 = ((70525124608 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 33629 = 2097152 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 2097152 = ((41758406289 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_161682554881 : Nat.Prime 161682554881 := by
  refine lucas_primality 161682554881 (31 : ZMod 161682554881) ?_ (fun q hq hd => ?_)
  · rw [show 161682554881 - 1 = 161682554880 from by norm_num]
    reduce_mod_char
  · have e : 161682554881 - 1 = [2 ^ 19, 3 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 1, 89 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 2 = 80841277440 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 80841277440 = ((161682554880 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 3 = 53894184960 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 53894184960 = ((51317120649 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 5 = 32336510976 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 32336510976 = ((90856096301 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 7 = 23097507840 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 23097507840 = ((5645139987 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 11 = 14698414080 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 14698414080 = ((87496196605 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161682554881 - 1) / 89 = 1816657920 from by norm_num]
      have h2 : (31 : ZMod 161682554881) ^ 1816657920 = ((114833206851 : ℕ) : ZMod 161682554881) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_231828638827 : Nat.Prime 231828638827 := by
  refine lucas_primality 231828638827 (3 : ZMod 231828638827) ?_ (fun q hq hd => ?_)
  · rw [show 231828638827 - 1 = 231828638826 from by norm_num]
    reduce_mod_char
  · have e : 231828638827 - 1 = [2 ^ 1, 3 ^ 1, 29 ^ 1, 139 ^ 1, 2273 ^ 1, 4217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 2 = 115914319413 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 115914319413 = ((231828638826 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 3 = 77276212942 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 77276212942 = ((220596364139 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 29 = 7994090994 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 7994090994 = ((105702497580 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 139 = 1667831934 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 1667831934 = ((89981218114 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 2273 = 101992362 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 101992362 = ((158396879870 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 4217 = 54974778 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 54974778 = ((67309039783 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_323365109761 : Nat.Prime 323365109761 := by
  refine lucas_primality 323365109761 (23 : ZMod 323365109761) ?_ (fun q hq hd => ?_)
  · rw [show 323365109761 - 1 = 323365109760 from by norm_num]
    reduce_mod_char
  · have e : 323365109761 - 1 = [2 ^ 20, 3 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 1, 89 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 2 = 161682554880 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 161682554880 = ((323365109760 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 3 = 107788369920 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 107788369920 = ((243824470911 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 5 = 64673021952 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 64673021952 = ((223403792769 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 7 = 46195015680 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 46195015680 = ((302201451784 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 11 = 29396828160 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 29396828160 = ((276363038569 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (323365109761 - 1) / 89 = 3633315840 from by norm_num]
      have h2 : (23 : ZMod 323365109761) ^ 3633315840 = ((166025110832 : ℕ) : ZMod 323365109761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_646730219521 : Nat.Prime 646730219521 := by
  refine lucas_primality 646730219521 (93 : ZMod 646730219521) ?_ (fun q hq hd => ?_)
  · rw [show 646730219521 - 1 = 646730219520 from by norm_num]
    reduce_mod_char
  · have e : 646730219521 - 1 = [2 ^ 21, 3 ^ 2, 5 ^ 1, 7 ^ 1, 11 ^ 1, 89 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 2 = 323365109760 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 323365109760 = ((646730219520 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 3 = 215576739840 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 215576739840 = ((238470838201 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 5 = 129346043904 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 129346043904 = ((221372628197 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 7 = 92390031360 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 92390031360 = ((254375314516 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 11 = 58793656320 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 58793656320 = ((211618615694 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (646730219521 - 1) / 89 = 7266631680 from by norm_num]
      have h2 : (93 : ZMod 646730219521) ^ 7266631680 = ((178119698545 : ℕ) : ZMod 646730219521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_860444447189 : Nat.Prime 860444447189 := by
  refine lucas_primality 860444447189 (2 : ZMod 860444447189) ?_ (fun q hq hd => ?_)
  · rw [show 860444447189 - 1 = 860444447188 from by norm_num]
    reduce_mod_char
  · have e : 860444447189 - 1 = [2 ^ 2, 19 ^ 1, 27271 ^ 1, 415153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (860444447189 - 1) / 2 = 430222223594 from by norm_num]
      have h2 : (2 : ZMod 860444447189) ^ 430222223594 = ((860444447188 : ℕ) : ZMod 860444447189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (860444447189 - 1) / 19 = 45286549852 from by norm_num]
      have h2 : (2 : ZMod 860444447189) ^ 45286549852 = ((633552435264 : ℕ) : ZMod 860444447189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (860444447189 - 1) / 27271 = 31551628 from by norm_num]
      have h2 : (2 : ZMod 860444447189) ^ 31551628 = ((453655953797 : ℕ) : ZMod 860444447189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (860444447189 - 1) / 415153 = 2072596 from by norm_num]
      have h2 : (2 : ZMod 860444447189) ^ 2072596 = ((290531188411 : ℕ) : ZMod 860444447189) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1069660739759 : Nat.Prime 1069660739759 := by
  refine lucas_primality 1069660739759 (17 : ZMod 1069660739759) ?_ (fun q hq hd => ?_)
  · rw [show 1069660739759 - 1 = 1069660739758 from by norm_num]
    reduce_mod_char
  · have e : 1069660739759 - 1 = [2 ^ 1, 13 ^ 1, 73 ^ 1, 563 ^ 1, 1001017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 2 = 534830369879 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 534830369879 = ((1069660739758 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 13 = 82281595366 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 82281595366 = ((1144950070 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 73 = 14652886846 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 14652886846 = ((1061627935906 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 563 = 1899930266 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1899930266 = ((368040485674 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 1001017 = 1068574 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1068574 = ((50491089679 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1277254085461 : Nat.Prime 1277254085461 := by
  refine lucas_primality 1277254085461 (2 : ZMod 1277254085461) ?_ (fun q hq hd => ?_)
  · rw [show 1277254085461 - 1 = 1277254085460 from by norm_num]
    reduce_mod_char
  · have e : 1277254085461 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 227 ^ 1, 2741 ^ 1, 34213 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 2 = 638627042730 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 638627042730 = ((1277254085460 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 3 = 425751361820 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 425751361820 = ((1047812401647 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 5 = 255450817092 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 255450817092 = ((397687640499 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 227 = 5626669980 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 5626669980 = ((1222527768111 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 2741 = 465981060 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 465981060 = ((537741237084 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1277254085461 - 1) / 34213 = 37332420 from by norm_num]
      have h2 : (2 : ZMod 1277254085461) ^ 37332420 = ((137931633827 : ℕ) : ZMod 1277254085461) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4485296422913 : Nat.Prime 4485296422913 := by
  refine lucas_primality 4485296422913 (3 : ZMod 4485296422913) ?_ (fun q hq hd => ?_)
  · rw [show 4485296422913 - 1 = 4485296422912 from by norm_num]
    reduce_mod_char
  · have e : 4485296422913 - 1 = [2 ^ 23, 503 ^ 1, 1063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4485296422913 - 1) / 2 = 2242648211456 from by norm_num]
      have h2 : (3 : ZMod 4485296422913) ^ 2242648211456 = ((4485296422912 : ℕ) : ZMod 4485296422913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4485296422913 - 1) / 503 = 8917090304 from by norm_num]
      have h2 : (3 : ZMod 4485296422913) ^ 8917090304 = ((632022860276 : ℕ) : ZMod 4485296422913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4485296422913 - 1) / 1063 = 4219469824 from by norm_num]
      have h2 : (3 : ZMod 4485296422913) ^ 4219469824 = ((668862236023 : ℕ) : ZMod 4485296422913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13562889751591 : Nat.Prime 13562889751591 := by
  refine lucas_primality 13562889751591 (6 : ZMod 13562889751591) ?_ (fun q hq hd => ?_)
  · rw [show 13562889751591 - 1 = 13562889751590 from by norm_num]
    reduce_mod_char
  · have e : 13562889751591 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 503 ^ 1, 15643 ^ 1, 57457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 2 = 6781444875795 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 6781444875795 = ((13562889751590 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 3 = 4520963250530 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 4520963250530 = ((4765861943083 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 5 = 2712577950318 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 2712577950318 = ((601171651600 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 503 = 26963995530 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 26963995530 = ((1996861145169 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 15643 = 867026130 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 867026130 = ((1205480546483 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 57457 = 236052870 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 236052870 = ((2259943784594 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31065037602817 : Nat.Prime 31065037602817 := by
  refine lucas_primality 31065037602817 (5 : ZMod 31065037602817) ?_ (fun q hq hd => ?_)
  · rw [show 31065037602817 - 1 = 31065037602816 from by norm_num]
    reduce_mod_char
  · have e : 31065037602817 - 1 = [2 ^ 19, 3 ^ 1, 7 ^ 1, 2821517 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2 = 15532518801408 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 15532518801408 = ((31065037602816 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 3 = 10355012534272 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 10355012534272 = ((8563864821674 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 7 = 4437862514688 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 4437862514688 = ((8857347445025 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2821517 = 11010048 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 11010048 = ((23804604093954 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine lucas_primality 67280421310721 (3 : ZMod 67280421310721) ?_ (fun q hq hd => ?_)
  · rw [show 67280421310721 - 1 = 67280421310720 from by norm_num]
    reduce_mod_char
  · have e : 67280421310721 - 1 = [2 ^ 8, 5 ^ 1, 47 ^ 1, 373 ^ 1, 2998279 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2 = 33640210655360 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 33640210655360 = ((67280421310720 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 5 = 13456084262144 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 13456084262144 = ((8348471219631 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 47 = 1431498325760 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 1431498325760 = ((29801263682154 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 373 = 180376464640 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 180376464640 = ((65541179653181 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67280421310721 - 1) / 2998279 = 22439680 from by norm_num]
      have h2 : (3 : ZMod 67280421310721) ^ 22439680 = ((61150258807256 : ℕ) : ZMod 67280421310721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116503103764643 : Nat.Prime 116503103764643 := by
  refine lucas_primality 116503103764643 (2 : ZMod 116503103764643) ?_ (fun q hq hd => ?_)
  · rw [show 116503103764643 - 1 = 116503103764642 from by norm_num]
    reduce_mod_char
  · have e : 116503103764643 - 1 = [2 ^ 1, 7 ^ 1, 449 ^ 1, 18533742247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 2 = 58251551882321 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 58251551882321 = ((116503103764642 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 7 = 16643300537806 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 16643300537806 = ((10593569056013 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 449 = 259472391458 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 259472391458 = ((12829831376547 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_18533742247).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 18533742247 = 6286 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 6286 = ((65489195555553 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_151977745250209 : Nat.Prime 151977745250209 := by
  refine lucas_primality 151977745250209 (17 : ZMod 151977745250209) ?_ (fun q hq hd => ?_)
  · rw [show 151977745250209 - 1 = 151977745250208 from by norm_num]
    reduce_mod_char
  · have e : 151977745250209 - 1 = [2 ^ 5, 3 ^ 2, 37 ^ 1, 163 ^ 1, 577 ^ 1, 151643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 2 = 75988872625104 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 75988872625104 = ((151977745250208 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 3 = 50659248416736 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 50659248416736 = ((77359160108590 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 37 = 4107506628384 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 4107506628384 = ((128038624677732 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 163 = 932378805216 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 932378805216 = ((79127591120372 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 577 = 263392972704 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 263392972704 = ((21696979250474 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151977745250209 - 1) / 151643 = 1002207456 from by norm_num]
      have h2 : (17 : ZMod 151977745250209) ^ 1002207456 = ((81764543091079 : ℕ) : ZMod 151977745250209) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_206487726925483 : Nat.Prime 206487726925483 := by
  refine lucas_primality 206487726925483 (2 : ZMod 206487726925483) ?_ (fun q hq hd => ?_)
  · rw [show 206487726925483 - 1 = 206487726925482 from by norm_num]
    reduce_mod_char
  · have e : 206487726925483 - 1 = [2 ^ 1, 3 ^ 2, 18773 ^ 1, 611065913 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 2 = 103243863462741 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 103243863462741 = ((206487726925482 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 3 = 68829242308494 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 68829242308494 = ((2152959480421 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 18773 = 10999186434 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 10999186434 = ((204828111120102 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_611065913).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 611065913 = 337914 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 337914 = ((51630314293860 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1238926361552897 : Nat.Prime 1238926361552897 := by
  refine lucas_primality 1238926361552897 (3 : ZMod 1238926361552897) ?_ (fun q hq hd => ?_)
  · rw [show 1238926361552897 - 1 = 1238926361552896 from by norm_num]
    reduce_mod_char
  · have e : 1238926361552897 - 1 = [2 ^ 11, 157 ^ 1, 3853149761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 2 = 619463180776448 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 619463180776448 = ((1238926361552896 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 157 = 7891250710528 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 7891250710528 = ((196133765836405 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3853149761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 3853149761 = 321536 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 321536 = ((437771075092802 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2327042503868417 : Nat.Prime 2327042503868417 := by
  refine lucas_primality 2327042503868417 (3 : ZMod 2327042503868417) ?_ (fun q hq hd => ?_)
  · rw [show 2327042503868417 - 1 = 2327042503868416 from by norm_num]
    reduce_mod_char
  · have e : 2327042503868417 - 1 = [2 ^ 17, 14431 ^ 1, 1230263 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2327042503868417 - 1) / 2 = 1163521251934208 from by norm_num]
      have h2 : (3 : ZMod 2327042503868417) ^ 1163521251934208 = ((2327042503868416 : ℕ) : ZMod 2327042503868417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2327042503868417 - 1) / 14431 = 161253031936 from by norm_num]
      have h2 : (3 : ZMod 2327042503868417) ^ 161253031936 = ((1981247777303027 : ℕ) : ZMod 2327042503868417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2327042503868417 - 1) / 1230263 = 1891500032 from by norm_num]
      have h2 : (3 : ZMod 2327042503868417) ^ 1891500032 = ((132441633644978 : ℕ) : ZMod 2327042503868417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  refine lucas_primality 59649589127497217 (3 : ZMod 59649589127497217) ?_ (fun q hq hd => ?_)
  · rw [show 59649589127497217 - 1 = 59649589127497216 from by norm_num]
    reduce_mod_char
  · have e : 59649589127497217 - 1 = [2 ^ 9, 116503103764643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59649589127497217 - 1) / 2 = 29824794563748608 from by norm_num]
      have h2 : (3 : ZMod 59649589127497217) ^ 29824794563748608 = ((59649589127497216 : ℕ) : ZMod 59649589127497217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_116503103764643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59649589127497217 - 1) / 116503103764643 = 512 from by norm_num]
      have h2 : (3 : ZMod 59649589127497217) ^ 512 = ((20416608684428934 : ℕ) : ZMod 59649589127497217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2663848877152141313 : Nat.Prime 2663848877152141313 := by
  refine lucas_primality 2663848877152141313 (3 : ZMod 2663848877152141313) ?_ (fun q hq hd => ?_)
  · rw [show 2663848877152141313 - 1 = 2663848877152141312 from by norm_num]
    reduce_mod_char
  · have e : 2663848877152141313 - 1 = [2 ^ 17, 19 ^ 1, 1069660739759 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 2 = 1331924438576070656 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 1331924438576070656 = ((2663848877152141312 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 19 = 140202572481691648 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 140202572481691648 = ((1712054958658763820 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1069660739759).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 1069660739759 = 2490368 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 2490368 = ((2177351900160986599 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_188981757975021318420037633 : Nat.Prime 188981757975021318420037633 := by
  refine lucas_primality 188981757975021318420037633 (5 : ZMod 188981757975021318420037633) ?_ (fun q hq hd => ?_)
  · rw [show 188981757975021318420037633 - 1 = 188981757975021318420037632 from by norm_num]
    reduce_mod_char
  · have e : 188981757975021318420037633 - 1 = [2 ^ 20, 3 ^ 2, 31 ^ 1, 37 ^ 1, 13669 ^ 1, 1277254085461 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 2 = 94490878987510659210018816 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 94490878987510659210018816 = ((188981757975021318420037632 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 3 = 62993919325007106140012544 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 62993919325007106140012544 = ((119124213611872968847939642 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 31 = 6096185741129719949033472 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 6096185741129719949033472 = ((99846352614131517007009889 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 37 = 5107615080405981578919936 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 5107615080405981578919936 = ((57163852481855136931501980 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 13669 = 13825573046676517552128 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 13825573046676517552128 = ((81747507176766292372077976 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1277254085461).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (188981757975021318420037633 - 1) / 1277254085461 = 147959407706112 from by norm_num]
      have h2 : (5 : ZMod 188981757975021318420037633) ^ 147959407706112 = ((161232707101981062275200354 : ℕ) : ZMod 188981757975021318420037633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7751061099802522589358967058392886922693580423169 : Nat.Prime 7751061099802522589358967058392886922693580423169 := by
  refine lucas_primality 7751061099802522589358967058392886922693580423169 (3 : ZMod 7751061099802522589358967058392886922693580423169) ?_ (fun q hq hd => ?_)
  · rw [show 7751061099802522589358967058392886922693580423169 - 1 = 7751061099802522589358967058392886922693580423168 from by norm_num]
    reduce_mod_char
  · have e : 7751061099802522589358967058392886922693580423169 - 1 = [2 ^ 19, 229 ^ 1, 9920257 ^ 1, 49765687 ^ 1, 860444447189 ^ 1, 151977745250209 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 2 = 3875530549901261294679483529196443461346790211584 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 3875530549901261294679483529196443461346790211584 = ((7751061099802522589358967058392886922693580423168 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 229 = 33847428383417129211174528639270248570714324992 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 33847428383417129211174528639270248570714324992 = ((7317832865302803289639208825019242716163535814959 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 9920257 = 781336723413770690553578103711717037441024 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 781336723413770690553578103711717037441024 = ((472488813781789409441716099641041244148692805072 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 49765687 = 155751112203123461138172714432594629361664 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 155751112203123461138172714432594629361664 = ((3213420233042156332432444397478977992925472261359 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_860444447189).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 860444447189 = 9008206311429622831302633002263642112 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 9008206311429622831302633002263642112 = ((6651582849059389004638000146337658131704924579330 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_151977745250209).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7751061099802522589358967058392886922693580423169 - 1) / 151977745250209 = 51001290268134592684338609955274752 from by norm_num]
      have h2 : (3 : ZMod 7751061099802522589358967058392886922693580423169) ^ 51001290268134592684338609955274752 = ((3636197304315504075223233290815393580250981455315 : ℕ) : ZMod 7751061099802522589358967058392886922693580423169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem fdvd_2 : 17 ∣ 1 + 2 ^ 4 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_2 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz17 : z ≠ 17)
    (hd : 1 + 2 ^ 4 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz hz17) (fdvd_2.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 17 g17 (by norm_num)

theorem fdvd_3 : 257 ∣ 1 + 2 ^ 8 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_3 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11 : z ≠ 11) (hz43 : z ≠ 43) (hz257 : z ≠ 257)
    (hd : 1 + 2 ^ 8 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz hz257) (fdvd_3.trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz hz43) 257 g257 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz hz11) 43 g43 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 257 g257 11 g11 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_4 : 65537 ∣ 1 + 2 ^ 16 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_4 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz65537 : z ≠ 65537)
    (hd : 1 + 2 ^ 16 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz hz65537) (fdvd_4.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 65537 g65537 (by norm_num)

theorem fdvd_5 : 641 ∣ 1 + 2 ^ 32 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_5 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz107 : z ≠ 107) (hz641 : z ≠ 641)
    (hd : 1 + 2 ^ 32 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g641 : 641 ∈ P := S2 641 (by norm_num) (by norm_num) (hnz hz641) (fdvd_5.trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz hz107) 641 g641 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 107 g107 (by norm_num)

theorem fdvd_5_alt1 : 6700417 ∣ 1 + 2 ^ 32 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_5_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz335021 : z ≠ 335021) (hz3350209 : z ≠ 3350209) (hz6700417 : z ≠ 6700417)
    (hd : 1 + 2 ^ 32 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6700417 : 6700417 ∈ P := S2 6700417 (by norm_num) (by norm_num) (hnz hz6700417) (fdvd_5_alt1.trans hd)
  have g3350209 : 3350209 ∈ P := S1 3350209 (by norm_num) (by norm_num) (hnz hz3350209) 6700417 g6700417 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz hz5) 3350209 g3350209 (by norm_num)
  have g335021 : 335021 ∈ P := S1 335021 (by norm_num) (by norm_num) (hnz hz335021) 3350209 g3350209 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 335021 g335021 5 g5 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_6 : 67280421310721 ∣ 1 + 2 ^ 64 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_6 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz67280421310721 : z ≠ 67280421310721)
    (hd : 1 + 2 ^ 64 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67280421310721 : 67280421310721 ∈ P := S2 67280421310721 prime_67280421310721 (by norm_num) (hnz hz67280421310721) (fdvd_6.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 67280421310721 g67280421310721 (by norm_num)

theorem fdvd_7 : 59649589127497217 ∣ 1 + 2 ^ 128 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_7 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz1440437 : z ≠ 1440437) (hz13562889751591 : z ≠ 13562889751591) (hz59649589127497217 : z ≠ 59649589127497217)
    (hd : 1 + 2 ^ 128 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59649589127497217 : 59649589127497217 ∈ P := S2 59649589127497217 prime_59649589127497217 (by norm_num) (hnz hz59649589127497217) (fdvd_7.trans hd)
  have g13562889751591 : 13562889751591 ∈ P := S1 13562889751591 prime_13562889751591 (by norm_num) (hnz hz13562889751591) 59649589127497217 g59649589127497217 (by norm_num)
  have g1440437 : 1440437 ∈ P := S1 1440437 (by norm_num) (by norm_num) (hnz hz1440437) 13562889751591 g13562889751591 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 59649589127497217 g59649589127497217 1440437 g1440437 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_8 : 1238926361552897 ∣ 1 + 2 ^ 256 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_8 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11621 : z ≠ 11621) (hz206487726925483 : z ≠ 206487726925483) (hz1238926361552897 : z ≠ 1238926361552897)
    (hd : 1 + 2 ^ 256 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1238926361552897 : 1238926361552897 ∈ P := S2 1238926361552897 prime_1238926361552897 (by norm_num) (hnz hz1238926361552897) (fdvd_8.trans hd)
  have g206487726925483 : 206487726925483 ∈ P := S1 206487726925483 prime_206487726925483 (by norm_num) (hnz hz206487726925483) 1238926361552897 g1238926361552897 (by norm_num)
  have g11621 : 11621 ∈ P := S1 11621 (by norm_num) (by norm_num) (hnz hz11621) 206487726925483 g206487726925483 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 1238926361552897 g1238926361552897 11621 g11621 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_9 : 2424833 ∣ 1 + 2 ^ 512 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_9 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz2424833 : z ≠ 2424833)
    (hd : 1 + 2 ^ 512 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2424833 : 2424833 ∈ P := S2 2424833 (by norm_num) (by norm_num) (hnz hz2424833) (fdvd_9.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 2424833 g2424833 (by norm_num)

theorem fdvd_10 : 45592577 ∣ 1 + 2 ^ 1024 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_10 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz45592577 : z ≠ 45592577)
    (hd : 1 + 2 ^ 1024 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g45592577 : 45592577 ∈ P := S2 45592577 (by norm_num) (by norm_num) (hnz hz45592577) (fdvd_10.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 45592577 g45592577 (by norm_num)

theorem fdvd_11 : 319489 ∣ 1 + 2 ^ 2048 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_11 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz743 : z ≠ 743) (hz319489 : z ≠ 319489)
    (hd : 1 + 2 ^ 2048 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g319489 : 319489 ∈ P := S2 319489 (by norm_num) (by norm_num) (hnz hz319489) (fdvd_11.trans hd)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz hz5) 319489 g319489 (by norm_num)
  have g743 : 743 ∈ P := S1 743 (by norm_num) (by norm_num) (hnz hz743) 319489 g319489 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 5 g5 743 g743 (by norm_num) (by norm_num)) (by norm_num)

theorem fkill_11_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11 : z ≠ 11) (hz43 : z ≠ 43) (hz743 : z ≠ 743) (hz319489 : z ≠ 319489)
    (hd : 1 + 2 ^ 2048 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g319489 : 319489 ∈ P := S2 319489 (by norm_num) (by norm_num) (hnz hz319489) (fdvd_11.trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz hz43) 319489 g319489 (by norm_num)
  have g743 : 743 ∈ P := S1 743 (by norm_num) (by norm_num) (hnz hz743) 319489 g319489 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz hz11) 43 g43 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 743 g743 11 g11 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_12 : 26017793 ∣ 1 + 2 ^ 4096 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_12 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz26017793 : z ≠ 26017793)
    (hd : 1 + 2 ^ 4096 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g26017793 : 26017793 ∈ P := S2 26017793 (by norm_num) (by norm_num) (hnz hz26017793) (fdvd_12.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 26017793 g26017793 (by norm_num)

theorem fdvd_13 : 2663848877152141313 ∣ 1 + 2 ^ 8192 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_13 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz2663848877152141313 : z ≠ 2663848877152141313)
    (hd : 1 + 2 ^ 8192 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2663848877152141313 : 2663848877152141313 ∈ P := S2 2663848877152141313 prime_2663848877152141313 (by norm_num) (hnz hz2663848877152141313) (fdvd_13.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 2663848877152141313 g2663848877152141313 (by norm_num)

theorem fdvd_15 : 2327042503868417 ∣ 1 + 2 ^ 32768 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_15 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz2327042503868417 : z ≠ 2327042503868417)
    (hd : 1 + 2 ^ 32768 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2327042503868417 : 2327042503868417 ∈ P := S2 2327042503868417 prime_2327042503868417 (by norm_num) (hnz hz2327042503868417) (fdvd_15.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 2327042503868417 g2327042503868417 (by norm_num)

theorem fdvd_16 : 825753601 ∣ 1 + 2 ^ 65536 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_16 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz113 : z ≠ 113) (hz3653777 : z ≠ 3653777) (hz825753601 : z ≠ 825753601)
    (hd : 1 + 2 ^ 65536 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g825753601 : 825753601 ∈ P := S2 825753601 prime_825753601 (by norm_num) (hnz hz825753601) (fdvd_16.trans hd)
  have g3653777 : 3653777 ∈ P := S1 3653777 (by norm_num) (by norm_num) (hnz hz3653777) 825753601 g825753601 (by norm_num)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz hz113) 825753601 g825753601 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 113 g113 3653777 g3653777 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_16_alt1 : 188981757975021318420037633 ∣ 1 + 2 ^ 65536 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_16_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz7 : z ≠ 7) (hz1389171559 : z ≠ 1389171559) (hz188981757975021318420037633 : z ≠ 188981757975021318420037633)
    (hd : 1 + 2 ^ 65536 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g188981757975021318420037633 : 188981757975021318420037633 ∈ P := S2 188981757975021318420037633 prime_188981757975021318420037633 (by norm_num) (hnz hz188981757975021318420037633) (fdvd_16_alt1.trans hd)
  have g1389171559 : 1389171559 ∈ P := S1 1389171559 prime_1389171559 (by norm_num) (hnz hz1389171559) 188981757975021318420037633 g188981757975021318420037633 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz hz7) 1389171559 g1389171559 (by norm_num)

theorem fdvd_17 : 31065037602817 ∣ 1 + 2 ^ 131072 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_17 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz17 : z ≠ 17) (hz67 : z ≠ 67) (hz1028941 : z ≠ 1028941) (hz231828638827 : z ≠ 231828638827) (hz31065037602817 : z ≠ 31065037602817)
    (hd : 1 + 2 ^ 131072 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31065037602817 : 31065037602817 ∈ P := S2 31065037602817 prime_31065037602817 (by norm_num) (hnz hz31065037602817) (fdvd_17.trans hd)
  have g231828638827 : 231828638827 ∈ P := S1 231828638827 prime_231828638827 (by norm_num) (hnz hz231828638827) 31065037602817 g31065037602817 (by norm_num)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz hz67) 31065037602817 g31065037602817 (by norm_num)
  have g1028941 : 1028941 ∈ P := S1 1028941 (by norm_num) (by norm_num) (hnz hz1028941) 231828638827 g231828638827 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz hz17) 67 g67 1028941 g1028941 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_17_alt1 : 7751061099802522589358967058392886922693580423169 ∣ 1 + 2 ^ 131072 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_17_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz7751061099802522589358967058392886922693580423169 : z ≠ 7751061099802522589358967058392886922693580423169)
    (hd : 1 + 2 ^ 131072 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7751061099802522589358967058392886922693580423169 : 7751061099802522589358967058392886922693580423169 ∈ P := S2 7751061099802522589358967058392886922693580423169 prime_7751061099802522589358967058392886922693580423169 (by norm_num) (hnz hz7751061099802522589358967058392886922693580423169) (fdvd_17_alt1.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 7751061099802522589358967058392886922693580423169 g7751061099802522589358967058392886922693580423169 (by norm_num)

theorem fdvd_18 : 13631489 ∣ 1 + 2 ^ 262144 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_18 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz13631489 : z ≠ 13631489)
    (hd : 1 + 2 ^ 262144 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13631489 : 13631489 ∈ P := S2 13631489 (by norm_num) (by norm_num) (hnz hz13631489) (fdvd_18.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) 13631489 g13631489 (by norm_num)

theorem fdvd_19 : 70525124609 ∣ 1 + 2 ^ 524288 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_19 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz17 : z ≠ 17) (hz3467 : z ≠ 3467) (hz70525124609 : z ≠ 70525124609)
    (hd : 1 + 2 ^ 524288 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g70525124609 : 70525124609 ∈ P := S2 70525124609 prime_70525124609 (by norm_num) (hnz hz70525124609) (fdvd_19.trans hd)
  have g3467 : 3467 ∈ P := S1 3467 (by norm_num) (by norm_num) (hnz hz3467) 70525124609 g70525124609 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz hz17) 3467 g3467 (by norm_num)

theorem fdvd_19_alt1 : 646730219521 ∣ 1 + 2 ^ 524288 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_19_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz5 : z ≠ 5) (hz149 : z ≠ 149) (hz161682554881 : z ≠ 161682554881) (hz323365109761 : z ≠ 323365109761) (hz646730219521 : z ≠ 646730219521)
    (hd : 1 + 2 ^ 524288 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g646730219521 : 646730219521 ∈ P := S2 646730219521 prime_646730219521 (by norm_num) (hnz hz646730219521) (fdvd_19_alt1.trans hd)
  have g323365109761 : 323365109761 ∈ P := S1 323365109761 prime_323365109761 (by norm_num) (hnz hz323365109761) 646730219521 g646730219521 (by norm_num)
  have g161682554881 : 161682554881 ∈ P := S1 161682554881 prime_161682554881 (by norm_num) (hnz hz161682554881) 323365109761 g323365109761 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz hz149) 161682554881 g161682554881 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz hz5) 149 g149 (by norm_num)

theorem fdvd_21 : 4485296422913 ∣ 1 + 2 ^ 2097152 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_21 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz10487 : z ≠ 10487) (hz4485296422913 : z ≠ 4485296422913)
    (hd : 1 + 2 ^ 2097152 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4485296422913 : 4485296422913 ∈ P := S2 4485296422913 prime_4485296422913 (by norm_num) (hnz hz4485296422913) (fdvd_21.trans hd)
  have g10487 : 10487 ∈ P := S1 10487 (by norm_num) (by norm_num) (hnz hz10487) 4485296422913 g4485296422913 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) 4485296422913 g4485296422913 10487 g10487 (by norm_num) (by norm_num)) (by norm_num)

theorem okill3 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hd : 1 + 2 ^ 3 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S5 3 (by norm_num) (by norm_num) (hnz hz3) ((by norm_num : 3 * 3 ∣ 1 + 2 ^ 3).trans hd)

theorem okill5 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11 : z ≠ 11) (hd : 1 + 2 ^ 5 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hnz hz11) ((by norm_num : 11 ∣ 1 + 2 ^ 5).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (hnz hz3) ((by norm_num : 3 ∣ 1 + 2 ^ 5).trans hd) 11 g11 (by norm_num)

theorem okill7 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11 : z ≠ 11) (hz43 : z ≠ 43) (hd : 1 + 2 ^ 7 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz hz43) ((by norm_num : 43 ∣ 1 + 2 ^ 7).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz hz11) 43 g43 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (hnz hz3) ((by norm_num : 3 ∣ 1 + 2 ^ 7).trans hd) 11 g11 (by norm_num)

theorem okill_mod3 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hzc : z % 3 = 1 ∨ ¬ z ∣ 2 ^ m + 1) (hm : m % 6 = 5) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 2) (e := m) (Nat.odd_iff.mpr (by omega))
  have hQ3 : Q % 3 = 2 := by
    have : Q % (2 + 1) = m % (2 + 1) := hQm
    norm_num at this
    omega
  obtain ⟨c, hc, hcQ, hc3⟩ := exists_prime_mod3 Q hQ3
  have hcd : c ∣ 2 ^ m + 1 := by
    rw [add_comm, hQ]
    exact hcQ.mul_left _
  have hc2 : c ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp hcd
    omega
  have hcz : z ≠ c := by
    rintro rfl
    rcases hzc with h | h
    · omega
    · exact h hcd
  have gc : c ∈ P := S2 c hc hc2 (hnz hcz) hcd
  have h3 : 3 ∣ 2 ^ m + 1 := by
    rw [add_comm, hQ]
    exact Dvd.intro Q rfl
  exact S4 3 (by norm_num) (by norm_num) (hnz hz3) h3 c gc (Nat.dvd_of_mod_eq_zero (by omega))

theorem tkill5 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz5 : z ≠ 5) (hd : 1 + 2 ^ 10 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S5 5 (by norm_num) (by norm_num) (hnz hz5) ((by norm_num : 5 * 5 ∣ 1 + 2 ^ 10).trans hd)

theorem tkill7 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz5 : z ≠ 5) (hz29 : z ≠ 29) (hd : 1 + 2 ^ 14 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29 : 29 ∈ P := S2 29 (by norm_num) (by norm_num) (hnz hz29) ((by norm_num : 29 ∣ 1 + 2 ^ 14).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz hz5) ((by norm_num : 5 ∣ 1 + 2 ^ 14).trans hd) 29 g29 (by norm_num)

theorem five_not_dvd_of_odd {m : ℕ} (hm : m % 2 = 1) : ¬ 5 ∣ 2 ^ m + 1 := by
  have e : 2 ^ m = 16 ^ (m / 4) * 2 ^ (m % 4) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h16 : 16 ^ (m / 4) % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  intro hd
  have h0 : (2 ^ m + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rw [e, Nat.add_mod, Nat.mul_mod, h16] at h0
  rcases h4 with h4 | h4 <;> rw [h4] at h0 <;> norm_num at h0

theorem two_adic_classes {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hz2100 : z < 2100) (hzn : z ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1) :
    (padicValNat 2 n % 6 ≠ 3) ∧
    (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) ∧
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) ∧
    ((z % 3 = 1 ∨ z = 5) → padicValNat 2 n % 6 ≠ 5) ∧
    (z ≠ 5 → padicValNat 2 n % 20 ≠ 10) ∧
    (z ≠ 5 → z ≠ 29 → padicValNat 2 n % 28 ≠ 14) ∧
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) ∧
    (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) ∧
    (padicValNat 2 n % 32 ≠ 16) ∧
    (padicValNat 2 n % 64 ≠ 32) ∧
    (padicValNat 2 n % 128 ≠ 64) ∧
    (padicValNat 2 n % 256 ≠ 128) ∧
    (padicValNat 2 n % 512 ≠ 256) ∧
    (padicValNat 2 n % 1024 ≠ 512) ∧
    (padicValNat 2 n % 2048 ≠ 1024) ∧
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) ∧
    (padicValNat 2 n % 8192 ≠ 4096) ∧
    (padicValNat 2 n % 16384 ≠ 8192) ∧
    (padicValNat 2 n % 65536 ≠ 32768) ∧
    (padicValNat 2 n % 131072 ≠ 65536) ∧
    (padicValNat 2 n % 262144 ≠ 131072) ∧
    (padicValNat 2 n % 524288 ≠ 262144) ∧
    (padicValNat 2 n % 1048576 ≠ 524288) ∧
    (padicValNat 2 n % 4194304 ≠ 2097152) := by
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by omega) hs
  rw [← Nat.factorization_def n Nat.prime_two]
  have D : ∀ e0 : ℕ, n.factorization 2 % (2 * e0) = e0 → 1 + 2 ^ e0 ∣ 2 ^ n.factorization 2 + 1 :=
    fun e0 he => by
      have := one_add_pow_dvd_of_odd_mul (z := 2) he
      rwa [add_comm 1 (2 ^ n.factorization 2)] at this
  exact ⟨fun hr => okill3 hP hz E (by omega) (D 3 (by omega)),
    fun h11 hr => okill5 hP hz E (by omega) h11 (D 5 (by omega)),
    fun h11 h43 hr => okill7 hP hz E (by omega) h11 h43 (D 7 (by omega)),
    fun hz35 hr => okill_mod3 hP hz E (by omega) (by
      rcases hz35 with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ five_not_dvd_of_odd (by omega))) hr,
    fun h5 hr => tkill5 hP hz E h5 (D 10 (by omega)),
    fun h5 h29 hr => tkill7 hP hz E h5 h29 (D 14 (by omega)),
    fun h17 hr => fkill_2 hP hz E (by omega) (by omega) (D 4 (by omega)),
    fun h11 h43 h257 hr => fkill_3 hP hz E (by omega) (by omega) (by omega) (by omega) (D 8 (by omega)),
    fun hr => fkill_4 hP hz E (by omega) (by omega) (D 16 (by omega)),
    fun hr => by
      by_cases hA0 : z ≠ 107 ∧ z ≠ 641
      · exact fkill_5 hP hz E (by omega) (by omega) (by omega) (D 32 (by omega))
      · exact fkill_5_alt1 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 32 (by omega)),
    fun hr => fkill_6 hP hz E (by omega) (by omega) (D 64 (by omega)),
    fun hr => fkill_7 hP hz E (by omega) (by omega) (by omega) (by omega) (D 128 (by omega)),
    fun hr => fkill_8 hP hz E (by omega) (by omega) (by omega) (by omega) (D 256 (by omega)),
    fun hr => fkill_9 hP hz E (by omega) (by omega) (D 512 (by omega)),
    fun hr => fkill_10 hP hz E (by omega) (by omega) (D 1024 (by omega)),
    fun h743 hr => by
      by_cases hA0 : z ≠ 5 ∧ z ≠ 743
      · exact fkill_11 hP hz E (by omega) (by omega) (by omega) (by omega) (D 2048 (by omega))
      · exact fkill_11_alt1 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 2048 (by omega)),
    fun hr => fkill_12 hP hz E (by omega) (by omega) (D 4096 (by omega)),
    fun hr => fkill_13 hP hz E (by omega) (by omega) (D 8192 (by omega)),
    fun hr => fkill_15 hP hz E (by omega) (by omega) (D 32768 (by omega)),
    fun hr => by
      by_cases hA0 : z ≠ 113
      · exact fkill_16 hP hz E (by omega) (by omega) (by omega) (by omega) (D 65536 (by omega))
      · exact fkill_16_alt1 hP hz E (by omega) (by omega) (by omega) (D 65536 (by omega)),
    fun hr => by
      by_cases hA0 : z ≠ 17 ∧ z ≠ 67
      · exact fkill_17 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 131072 (by omega))
      · exact fkill_17_alt1 hP hz E (by omega) (by omega) (D 131072 (by omega)),
    fun hr => fkill_18 hP hz E (by omega) (by omega) (D 262144 (by omega)),
    fun hr => by
      by_cases hA0 : z ≠ 17
      · exact fkill_19 hP hz E (by omega) (by omega) (by omega) (D 524288 (by omega))
      · exact fkill_19_alt1 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 524288 (by omega)),
    fun hr => fkill_21 hP hz E (by omega) (by omega) (by omega) (D 2097152 (by omega))⟩

theorem simple_of_unique_repeated {n z : ℕ} (hn : n ≠ 0)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) :
    z ∣ n ∧ ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ z → n.factorization r = 1 := by
  refine ⟨(dvd_pow_self z two_ne_zero).trans ((hS z).mpr rfl).2.2, fun r hr hr2 hrz => ?_⟩
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrd := Nat.dvd_of_mem_primeFactors hr
  have hpos : 0 < n.factorization r := hrp.factorization_pos_of_dvd hn hrd
  by_contra hne
  have h2 : 2 ≤ n.factorization r := by omega
  have : r ^ 2 ∣ n := (hrp.pow_dvd_iff_le_factorization hn).mpr h2
  exact hrz ((hS r).mp ⟨hrp, hr2, this⟩)

theorem H2_two_adic_classes {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hz2100 : z < 2100) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) :
    (padicValNat 2 n % 6 ≠ 3) ∧
    (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) ∧
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) ∧
    ((z % 3 = 1 ∨ z = 5) → padicValNat 2 n % 6 ≠ 5) ∧
    (z ≠ 5 → padicValNat 2 n % 20 ≠ 10) ∧
    (z ≠ 5 → z ≠ 29 → padicValNat 2 n % 28 ≠ 14) ∧
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) ∧
    (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) ∧
    (padicValNat 2 n % 32 ≠ 16) ∧
    (padicValNat 2 n % 64 ≠ 32) ∧
    (padicValNat 2 n % 128 ≠ 64) ∧
    (padicValNat 2 n % 256 ≠ 128) ∧
    (padicValNat 2 n % 512 ≠ 256) ∧
    (padicValNat 2 n % 1024 ≠ 512) ∧
    (padicValNat 2 n % 2048 ≠ 1024) ∧
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) ∧
    (padicValNat 2 n % 8192 ≠ 4096) ∧
    (padicValNat 2 n % 16384 ≠ 8192) ∧
    (padicValNat 2 n % 65536 ≠ 32768) ∧
    (padicValNat 2 n % 131072 ≠ 65536) ∧
    (padicValNat 2 n % 262144 ≠ 131072) ∧
    (padicValNat 2 n % 524288 ≠ 262144) ∧
    (padicValNat 2 n % 1048576 ≠ 524288) ∧
    (padicValNat 2 n % 4194304 ≠ 2097152) := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  exact two_adic_classes h hz hz5 hz2100 hzn hs

theorem prime_2937316727 : Nat.Prime 2937316727 := by
  refine lucas_primality 2937316727 (5 : ZMod 2937316727) ?_ (fun q hq hd => ?_)
  · rw [show 2937316727 - 1 = 2937316726 from by norm_num]
    reduce_mod_char
  · have e : 2937316727 - 1 = [2 ^ 1, 2833 ^ 1, 518411 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2 = 1468658363 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1468658363 = ((2937316726 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2833 = 1036822 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1036822 = ((559649464 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 518411 = 5666 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 5666 = ((1096917264 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_761145015334071629 : Nat.Prime 761145015334071629 := by
  refine lucas_primality 761145015334071629 (2 : ZMod 761145015334071629) ?_ (fun q hq hd => ?_)
  · rw [show 761145015334071629 - 1 = 761145015334071628 from by norm_num]
    reduce_mod_char
  · have e : 761145015334071629 - 1 = [2 ^ 2, 13 ^ 1, 1439 ^ 1, 3463 ^ 1, 2937316727 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2 = 380572507667035814 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 380572507667035814 = ((761145015334071628 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 13 = 58549616564159356 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 58549616564159356 = ((338322455532595746 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 1439 = 528940246931252 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 528940246931252 = ((329189789386551514 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 3463 = 219793536047956 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 219793536047956 = ((294223303145502828 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2937316727).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2937316727 = 259129364 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 259129364 = ((48063209786497848 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_643620696810643 : Nat.Prime 643620696810643 := by
  refine lucas_primality 643620696810643 (2 : ZMod 643620696810643) ?_ (fun q hq hd => ?_)
  · rw [show 643620696810643 - 1 = 643620696810642 from by norm_num]
    reduce_mod_char
  · have e : 643620696810643 - 1 = [2 ^ 1, 3 ^ 2, 127 ^ 1, 50153 ^ 1, 5613799 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 2 = 321810348405321 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 321810348405321 = ((643620696810642 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 3 = 214540232270214 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 214540232270214 = ((11262356464105 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 127 = 5067879502446 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 5067879502446 = ((371599021910739 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 50153 = 12833144514 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 12833144514 = ((250277297141578 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 5613799 = 114649758 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 114649758 = ((497809978569278 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8717008205877092841673 : Nat.Prime 8717008205877092841673 := by
  refine lucas_primality 8717008205877092841673 (10 : ZMod 8717008205877092841673) ?_ (fun q hq hd => ?_)
  · rw [show 8717008205877092841673 - 1 = 8717008205877092841672 from by norm_num]
    reduce_mod_char
  · have e : 8717008205877092841673 - 1 = [2 ^ 3, 3 ^ 2, 188107 ^ 1, 643620696810643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 2 = 4358504102938546420836 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 4358504102938546420836 = ((8717008205877092841672 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 3 = 2905669401959030947224 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 2905669401959030947224 = ((7343390186032111538464 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 188107 = 46340690170366296 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 46340690170366296 = ((2202464808706072287353 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_643620696810643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 643620696810643 = 13543704 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 13543704 = ((7313602266967842624858 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116928085873074369829035993834596371340386703423373313 : Nat.Prime 116928085873074369829035993834596371340386703423373313 := by
  refine lucas_primality 116928085873074369829035993834596371340386703423373313 (5 : ZMod 116928085873074369829035993834596371340386703423373313) ?_ (fun q hq hd => ?_)
  · rw [show 116928085873074369829035993834596371340386703423373313 - 1 = 116928085873074369829035993834596371340386703423373312 from by norm_num]
    reduce_mod_char
  · have e : 116928085873074369829035993834596371340386703423373313 - 1 = [2 ^ 16, 3 ^ 3, 9959563 ^ 1, 761145015334071629 ^ 1, 8717008205877092841673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 2 = 58464042936537184914517996917298185670193351711686656 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 58464042936537184914517996917298185670193351711686656 = ((116928085873074369829035993834596371340386703423373312 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 3 = 38976028624358123276345331278198790446795567807791104 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 38976028624358123276345331278198790446795567807791104 = ((49067573676489472842253551286141007228252506114172807 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 9959563 = 11740282768739388447970658334567126222343962624 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 11740282768739388447970658334567126222343962624 = ((42667818912291893027423909550891575419819132189033998 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_761145015334071629).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 761145015334071629 = 153621298855585163717133222561251328 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 153621298855585163717133222561251328 = ((113675781698961535315298001192578299458232658608361774 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8717008205877092841673).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 8717008205877092841673 = 13413786371594821026416520658944 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 13413786371594821026416520658944 = ((88896328563985109771361010271091762988159944350705466 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9661881871 : Nat.Prime 9661881871 := by
  refine lucas_primality 9661881871 (11 : ZMod 9661881871) ?_ (fun q hq hd => ?_)
  · rw [show 9661881871 - 1 = 9661881870 from by norm_num]
    reduce_mod_char
  · have e : 9661881871 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 127 ^ 1, 845309 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 2 = 4830940935 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 4830940935 = ((9661881870 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 3 = 3220627290 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 3220627290 = ((3357650980 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 5 = 1932376374 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 1932376374 = ((4559789779 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 127 = 76077810 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 76077810 = ((3475361764 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9661881871 - 1) / 845309 = 11430 from by norm_num]
      have h2 : (11 : ZMod 9661881871) ^ 11430 = ((41311167 : ℕ) : ZMod 9661881871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_603867617 : Nat.Prime 603867617 := by
  refine lucas_primality 603867617 (3 : ZMod 603867617) ?_ (fun q hq hd => ?_)
  · rw [show 603867617 - 1 = 603867616 from by norm_num]
    reduce_mod_char
  · have e : 603867617 - 1 = [2 ^ 5, 11 ^ 1, 1715533 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 2 = 301933808 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 301933808 = ((603867616 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 11 = 54897056 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 54897056 = ((218029995 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (603867617 - 1) / 1715533 = 352 from by norm_num]
      have h2 : (3 : ZMod 603867617) ^ 352 = ((321754386 : ℕ) : ZMod 603867617) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem fdvd_14 : 116928085873074369829035993834596371340386703423373313 ∣ 1 + 2 ^ 16384 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_14 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hzc : z ≠ 116928085873074369829035993834596371340386703423373313) (hz1 : z ≠ 9661881871) (hz2 : z ≠ 603867617)
    (hd : 1 + 2 ^ 16384 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g0 : 116928085873074369829035993834596371340386703423373313 ∈ P := S2 _ prime_116928085873074369829035993834596371340386703423373313 (by norm_num) (hnz hzc) (fdvd_14.trans hd)
  have g1 : 9661881871 ∈ P := S1 _ prime_9661881871 (by norm_num) (hnz hz1) _ g0 (by norm_num)
  have g2 : 603867617 ∈ P := S1 _ prime_603867617 (by norm_num) (hnz hz2) _ g1 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g2 (by norm_num)

theorem H2_two_adic_r14 {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hz2100 : z < 2100) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) :
    padicValNat 2 n % 32768 ≠ 16384 := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by omega) hs
  rw [← Nat.factorization_def n Nat.prime_two]
  intro hr
  have hd : 1 + 2 ^ 16384 ∣ 2 ^ n.factorization 2 + 1 := by
    have := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := 16384) (e := n.factorization 2) (by omega)
    rwa [add_comm 1 (2 ^ n.factorization 2)] at this
  exact fkill_14 hP hz E (by omega) (by omega) (by omega) (by omega) hd

theorem prime_1045429261 : Nat.Prime 1045429261 := by
  refine lucas_primality 1045429261 (6 : ZMod 1045429261) ?_ (fun q hq hd => ?_)
  · rw [show 1045429261 - 1 = 1045429260 from by norm_num]
    reduce_mod_char
  · have e : 1045429261 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 59 ^ 1, 295319 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1045429261 - 1) / 2 = 522714630 from by norm_num]
      have h2 : (6 : ZMod 1045429261) ^ 522714630 = ((1045429260 : ℕ) : ZMod 1045429261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1045429261 - 1) / 3 = 348476420 from by norm_num]
      have h2 : (6 : ZMod 1045429261) ^ 348476420 = ((978632389 : ℕ) : ZMod 1045429261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1045429261 - 1) / 5 = 209085852 from by norm_num]
      have h2 : (6 : ZMod 1045429261) ^ 209085852 = ((1017840621 : ℕ) : ZMod 1045429261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1045429261 - 1) / 59 = 17719140 from by norm_num]
      have h2 : (6 : ZMod 1045429261) ^ 17719140 = ((503612104 : ℕ) : ZMod 1045429261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1045429261 - 1) / 295319 = 3540 from by norm_num]
      have h2 : (6 : ZMod 1045429261) ^ 3540 = ((32043463 : ℕ) : ZMod 1045429261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52795084261 : Nat.Prime 52795084261 := by
  refine lucas_primality 52795084261 (11 : ZMod 52795084261) ?_ (fun q hq hd => ?_)
  · rw [show 52795084261 - 1 = 52795084260 from by norm_num]
    reduce_mod_char
  · have e : 52795084261 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 15377 ^ 1, 57223 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52795084261 - 1) / 2 = 26397542130 from by norm_num]
      have h2 : (11 : ZMod 52795084261) ^ 26397542130 = ((52795084260 : ℕ) : ZMod 52795084261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52795084261 - 1) / 3 = 17598361420 from by norm_num]
      have h2 : (11 : ZMod 52795084261) ^ 17598361420 = ((22050576295 : ℕ) : ZMod 52795084261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52795084261 - 1) / 5 = 10559016852 from by norm_num]
      have h2 : (11 : ZMod 52795084261) ^ 10559016852 = ((35652917991 : ℕ) : ZMod 52795084261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52795084261 - 1) / 15377 = 3433380 from by norm_num]
      have h2 : (11 : ZMod 52795084261) ^ 3433380 = ((3949758560 : ℕ) : ZMod 52795084261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52795084261 - 1) / 57223 = 922620 from by norm_num]
      have h2 : (11 : ZMod 52795084261) ^ 922620 = ((3087658517 : ℕ) : ZMod 52795084261) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_64658705994591851009055774868504577 : Nat.Prime 64658705994591851009055774868504577 := by
  refine lucas_primality 64658705994591851009055774868504577 (3 : ZMod 64658705994591851009055774868504577) ?_ (fun q hq hd => ?_)
  · rw [show 64658705994591851009055774868504577 - 1 = 64658705994591851009055774868504576 from by norm_num]
    reduce_mod_char
  · have e : 64658705994591851009055774868504577 - 1 = [2 ^ 24, 31 ^ 1, 2252461 ^ 1, 1045429261 ^ 1, 52795084261 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 2 = 32329352997295925504527887434252288 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 32329352997295925504527887434252288 = ((64658705994591851009055774868504576 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 31 = 2085764709502962935775992737693696 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 2085764709502962935775992737693696 = ((27148169837432786940997808126186547 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 2252461 = 28705804892778099602637193216 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 28705804892778099602637193216 = ((48778662124118120029412524795660816 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1045429261).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 1045429261 = 61848953732883750810812416 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 61848953732883750810812416 = ((5579996185421350680871962834478292 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_52795084261).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 52795084261 = 1224710726380174931132416 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 1224710726380174931132416 = ((53743358277992979144433879976849567 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_167772161 : Nat.Prime 167772161 := by
  refine lucas_primality 167772161 (3 : ZMod 167772161) ?_ (fun q hq hd => ?_)
  · rw [show 167772161 - 1 = 167772160 from by norm_num]
    reduce_mod_char
  · have e : 167772161 - 1 = [2 ^ 25, 5 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167772161 - 1) / 2 = 83886080 from by norm_num]
      have h2 : (3 : ZMod 167772161) ^ 83886080 = ((167772160 : ℕ) : ZMod 167772161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (167772161 - 1) / 5 = 33554432 from by norm_num]
      have h2 : (3 : ZMod 167772161) ^ 33554432 = ((124765 : ℕ) : ZMod 167772161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_204393464266227713 : Nat.Prime 204393464266227713 := by
  refine lucas_primality 204393464266227713 (3 : ZMod 204393464266227713) ?_ (fun q hq hd => ?_)
  · rw [show 204393464266227713 - 1 = 204393464266227712 from by norm_num]
    reduce_mod_char
  · have e : 204393464266227713 - 1 = [2 ^ 27, 7 ^ 2, 131 ^ 2, 1811 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (204393464266227713 - 1) / 2 = 102196732133113856 from by norm_num]
      have h2 : (3 : ZMod 204393464266227713) ^ 102196732133113856 = ((204393464266227712 : ℕ) : ZMod 204393464266227713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (204393464266227713 - 1) / 7 = 29199066323746816 from by norm_num]
      have h2 : (3 : ZMod 204393464266227713) ^ 29199066323746816 = ((13657310758167694 : ℕ) : ZMod 204393464266227713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (204393464266227713 - 1) / 131 = 1560255452413952 from by norm_num]
      have h2 : (3 : ZMod 204393464266227713) ^ 1560255452413952 = ((100538011925228750 : ℕ) : ZMod 204393464266227713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (204393464266227713 - 1) / 1811 = 112862211080192 from by norm_num]
      have h2 : (3 : ZMod 204393464266227713) ^ 112862211080192 = ((134785283643729755 : ℕ) : ZMod 204393464266227713) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76861124116481 : Nat.Prime 76861124116481 := by
  refine lucas_primality 76861124116481 (7 : ZMod 76861124116481) ?_ (fun q hq hd => ?_)
  · rw [show 76861124116481 - 1 = 76861124116480 from by norm_num]
    reduce_mod_char
  · have e : 76861124116481 - 1 = [2 ^ 29, 5 ^ 1, 11 ^ 1, 19 ^ 1, 137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76861124116481 - 1) / 2 = 38430562058240 from by norm_num]
      have h2 : (7 : ZMod 76861124116481) ^ 38430562058240 = ((76861124116480 : ℕ) : ZMod 76861124116481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76861124116481 - 1) / 5 = 15372224823296 from by norm_num]
      have h2 : (7 : ZMod 76861124116481) ^ 15372224823296 = ((47448897746057 : ℕ) : ZMod 76861124116481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76861124116481 - 1) / 11 = 6987374919680 from by norm_num]
      have h2 : (7 : ZMod 76861124116481) ^ 6987374919680 = ((71820532247742 : ℕ) : ZMod 76861124116481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76861124116481 - 1) / 19 = 4045322321920 from by norm_num]
      have h2 : (7 : ZMod 76861124116481) ^ 4045322321920 = ((10224199824825 : ℕ) : ZMod 76861124116481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76861124116481 - 1) / 137 = 561030103040 from by norm_num]
      have h2 : (7 : ZMod 76861124116481) ^ 561030103040 = ((7802281065447 : ℕ) : ZMod 76861124116481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12810187352747 : Nat.Prime 12810187352747 := by
  refine lucas_primality 12810187352747 (2 : ZMod 12810187352747) ?_ (fun q hq hd => ?_)
  · rw [show 12810187352747 - 1 = 12810187352746 from by norm_num]
    reduce_mod_char
  · have e : 12810187352747 - 1 = [2 ^ 1, 7 ^ 2, 47 ^ 1, 101 ^ 1, 27536591 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 2 = 6405093676373 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 6405093676373 = ((12810187352746 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 7 = 1830026764678 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 1830026764678 = ((8277357376929 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 47 = 272557177718 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 272557177718 = ((3745599354904 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 101 = 126833538146 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 126833538146 = ((11745341365340 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 27536591 = 465206 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 465206 = ((90982695622 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_151413703311361 : Nat.Prime 151413703311361 := by
  refine lucas_primality 151413703311361 (33 : ZMod 151413703311361) ?_ (fun q hq hd => ?_)
  · rw [show 151413703311361 - 1 = 151413703311360 from by norm_num]
    reduce_mod_char
  · have e : 151413703311361 - 1 = [2 ^ 30, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 79 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 2 = 75706851655680 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 75706851655680 = ((151413703311360 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 3 = 50471234437120 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 50471234437120 = ((131986062678402 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 5 = 30282740662272 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 30282740662272 = ((22352082704716 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 7 = 21630529044480 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 21630529044480 = ((70369557975742 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 17 = 8906688430080 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 8906688430080 = ((137253377574387 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (151413703311361 - 1) / 79 = 1916629155840 from by norm_num]
      have h2 : (33 : ZMod 151413703311361) ^ 1916629155840 = ((146333068850969 : ℕ) : ZMod 151413703311361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1766730974551267606529 : Nat.Prime 1766730974551267606529 := by
  refine lucas_primality 1766730974551267606529 (11 : ZMod 1766730974551267606529) ?_ (fun q hq hd => ?_)
  · rw [show 1766730974551267606529 - 1 = 1766730974551267606528 from by norm_num]
    reduce_mod_char
  · have e : 1766730974551267606529 - 1 = [2 ^ 36, 31 ^ 1, 89 ^ 1, 9318347 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1766730974551267606529 - 1) / 2 = 883365487275633803264 from by norm_num]
      have h2 : (11 : ZMod 1766730974551267606529) ^ 883365487275633803264 = ((1766730974551267606528 : ℕ) : ZMod 1766730974551267606529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1766730974551267606529 - 1) / 31 = 56991321759718309888 from by norm_num]
      have h2 : (11 : ZMod 1766730974551267606529) ^ 56991321759718309888 = ((1651749584359224991661 : ℕ) : ZMod 1766730974551267606529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1766730974551267606529 - 1) / 89 = 19850909826418737152 from by norm_num]
      have h2 : (11 : ZMod 1766730974551267606529) ^ 19850909826418737152 = ((1246222380770990744328 : ℕ) : ZMod 1766730974551267606529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1766730974551267606529 - 1) / 9318347 = 189597036314624 from by norm_num]
      have h2 : (11 : ZMod 1766730974551267606529) ^ 189597036314624 = ((1072103747022876754016 : ℕ) : ZMod 1766730974551267606529) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2405286912458753 : Nat.Prime 2405286912458753 := by
  refine lucas_primality 2405286912458753 (3 : ZMod 2405286912458753) ?_ (fun q hq hd => ?_)
  · rw [show 2405286912458753 - 1 = 2405286912458752 from by norm_num]
    reduce_mod_char
  · have e : 2405286912458753 - 1 = [2 ^ 31, 7 ^ 1, 53 ^ 1, 3019 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2405286912458753 - 1) / 2 = 1202643456229376 from by norm_num]
      have h2 : (3 : ZMod 2405286912458753) ^ 1202643456229376 = ((2405286912458752 : ℕ) : ZMod 2405286912458753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2405286912458753 - 1) / 7 = 343612416065536 from by norm_num]
      have h2 : (3 : ZMod 2405286912458753) ^ 343612416065536 = ((1913725497003471 : ℕ) : ZMod 2405286912458753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2405286912458753 - 1) / 53 = 45382771933184 from by norm_num]
      have h2 : (3 : ZMod 2405286912458753) ^ 45382771933184 = ((1997065257430779 : ℕ) : ZMod 2405286912458753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2405286912458753 - 1) / 3019 = 796716433408 from by norm_num]
      have h2 : (3 : ZMod 2405286912458753) ^ 796716433408 = ((513594600330589 : ℕ) : ZMod 2405286912458753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_640126220763137 : Nat.Prime 640126220763137 := by
  refine lucas_primality 640126220763137 (3 : ZMod 640126220763137) ?_ (fun q hq hd => ?_)
  · rw [show 640126220763137 - 1 = 640126220763136 from by norm_num]
    reduce_mod_char
  · have e : 640126220763137 - 1 = [2 ^ 32, 103 ^ 1, 1447 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (640126220763137 - 1) / 2 = 320063110381568 from by norm_num]
      have h2 : (3 : ZMod 640126220763137) ^ 320063110381568 = ((640126220763136 : ℕ) : ZMod 640126220763137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (640126220763137 - 1) / 103 = 6214817677312 from by norm_num]
      have h2 : (3 : ZMod 640126220763137) ^ 6214817677312 = ((243907819851716 : ℕ) : ZMod 640126220763137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (640126220763137 - 1) / 1447 = 442381631488 from by norm_num]
      have h2 : (3 : ZMod 640126220763137) ^ 442381631488 = ((205970114584614 : ℕ) : ZMod 640126220763137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1095981164658689 : Nat.Prime 1095981164658689 := by
  refine lucas_primality 1095981164658689 (3 : ZMod 1095981164658689) ?_ (fun q hq hd => ?_)
  · rw [show 1095981164658689 - 1 = 1095981164658688 from by norm_num]
    reduce_mod_char
  · have e : 1095981164658689 - 1 = [2 ^ 33, 7 ^ 1, 11 ^ 1, 1657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095981164658689 - 1) / 2 = 547990582329344 from by norm_num]
      have h2 : (3 : ZMod 1095981164658689) ^ 547990582329344 = ((1095981164658688 : ℕ) : ZMod 1095981164658689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095981164658689 - 1) / 7 = 156568737808384 from by norm_num]
      have h2 : (3 : ZMod 1095981164658689) ^ 156568737808384 = ((752621836606710 : ℕ) : ZMod 1095981164658689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095981164658689 - 1) / 11 = 99634651332608 from by norm_num]
      have h2 : (3 : ZMod 1095981164658689) ^ 99634651332608 = ((113738801662609 : ℕ) : ZMod 1095981164658689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1095981164658689 - 1) / 1657 = 661424963584 from by norm_num]
      have h2 : (3 : ZMod 1095981164658689) ^ 661424963584 = ((891046064145297 : ℕ) : ZMod 1095981164658689) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_140091319777 : Nat.Prime 140091319777 := by
  refine lucas_primality 140091319777 (10 : ZMod 140091319777) ?_ (fun q hq hd => ?_)
  · rw [show 140091319777 - 1 = 140091319776 from by norm_num]
    reduce_mod_char
  · have e : 140091319777 - 1 = [2 ^ 5, 3 ^ 1, 2719 ^ 1, 536699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140091319777 - 1) / 2 = 70045659888 from by norm_num]
      have h2 : (10 : ZMod 140091319777) ^ 70045659888 = ((140091319776 : ℕ) : ZMod 140091319777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140091319777 - 1) / 3 = 46697106592 from by norm_num]
      have h2 : (10 : ZMod 140091319777) ^ 46697106592 = ((32107702873 : ℕ) : ZMod 140091319777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140091319777 - 1) / 2719 = 51523104 from by norm_num]
      have h2 : (10 : ZMod 140091319777) ^ 51523104 = ((18282743147 : ℕ) : ZMod 140091319777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (140091319777 - 1) / 536699 = 261024 from by norm_num]
      have h2 : (10 : ZMod 140091319777) ^ 261024 = ((108569525472 : ℕ) : ZMod 140091319777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_46931635677864055013377 : Nat.Prime 46931635677864055013377 := by
  refine lucas_primality 46931635677864055013377 (5 : ZMod 46931635677864055013377) ?_ (fun q hq hd => ?_)
  · rw [show 46931635677864055013377 - 1 = 46931635677864055013376 from by norm_num]
    reduce_mod_char
  · have e : 46931635677864055013377 - 1 = [2 ^ 33, 3 ^ 1, 13 ^ 1, 140091319777 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46931635677864055013377 - 1) / 2 = 23465817838932027506688 from by norm_num]
      have h2 : (5 : ZMod 46931635677864055013377) ^ 23465817838932027506688 = ((46931635677864055013376 : ℕ) : ZMod 46931635677864055013377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46931635677864055013377 - 1) / 3 = 15643878559288018337792 from by norm_num]
      have h2 : (5 : ZMod 46931635677864055013377) ^ 15643878559288018337792 = ((25025981229523946108435 : ℕ) : ZMod 46931635677864055013377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46931635677864055013377 - 1) / 13 = 3610125821374158077952 from by norm_num]
      have h2 : (5 : ZMod 46931635677864055013377) ^ 3610125821374158077952 = ((6787248248422011556651 : ℕ) : ZMod 46931635677864055013377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_140091319777).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46931635677864055013377 - 1) / 140091319777 = 335007449088 from by norm_num]
      have h2 : (5 : ZMod 46931635677864055013377) ^ 335007449088 = ((24553789991219906639167 : ℕ) : ZMod 46931635677864055013377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1009632977 : Nat.Prime 1009632977 := by
  refine lucas_primality 1009632977 (3 : ZMod 1009632977) ?_ (fun q hq hd => ?_)
  · rw [show 1009632977 - 1 = 1009632976 from by norm_num]
    reduce_mod_char
  · have e : 1009632977 - 1 = [2 ^ 4, 11 ^ 1, 5736551 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1009632977 - 1) / 2 = 504816488 from by norm_num]
      have h2 : (3 : ZMod 1009632977) ^ 504816488 = ((1009632976 : ℕ) : ZMod 1009632977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1009632977 - 1) / 11 = 91784816 from by norm_num]
      have h2 : (3 : ZMod 1009632977) ^ 91784816 = ((207116376 : ℕ) : ZMod 1009632977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1009632977 - 1) / 5736551 = 176 from by norm_num]
      have h2 : (3 : ZMod 1009632977) ^ 176 = ((241987775 : ℕ) : ZMod 1009632977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3352259691276003929527 : Nat.Prime 3352259691276003929527 := by
  refine lucas_primality 3352259691276003929527 (3 : ZMod 3352259691276003929527) ?_ (fun q hq hd => ?_)
  · rw [show 3352259691276003929527 - 1 = 3352259691276003929526 from by norm_num]
    reduce_mod_char
  · have e : 3352259691276003929527 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 127 ^ 1, 991 ^ 1, 628127 ^ 1, 1009632977 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 2 = 1676129845638001964763 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 1676129845638001964763 = ((3352259691276003929526 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 3 = 1117419897092001309842 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 1117419897092001309842 = ((745938595726502505924 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 7 = 478894241610857704218 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 478894241610857704218 = ((2235534603214076250295 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 127 = 26395745600598456138 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 26395745600598456138 = ((2553278141219971301173 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 991 = 3382704027523717386 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 3382704027523717386 = ((2745960697633881156733 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 628127 = 5336913858624138 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 5336913858624138 = ((2538230462553413146783 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1009632977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3352259691276003929527 - 1) / 1009632977 = 3320275553238 from by norm_num]
      have h2 : (3 : ZMod 3352259691276003929527) ^ 3320275553238 = ((1638811128758156419201 : ℕ) : ZMod 3352259691276003929527) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_159526159847 : Nat.Prime 159526159847 := by
  refine lucas_primality 159526159847 (5 : ZMod 159526159847) ?_ (fun q hq hd => ?_)
  · rw [show 159526159847 - 1 = 159526159846 from by norm_num]
    reduce_mod_char
  · have e : 159526159847 - 1 = [2 ^ 1, 397 ^ 1, 3257 ^ 1, 61687 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159526159847 - 1) / 2 = 79763079923 from by norm_num]
      have h2 : (5 : ZMod 159526159847) ^ 79763079923 = ((159526159846 : ℕ) : ZMod 159526159847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159526159847 - 1) / 397 = 401829118 from by norm_num]
      have h2 : (5 : ZMod 159526159847) ^ 401829118 = ((152715285725 : ℕ) : ZMod 159526159847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159526159847 - 1) / 3257 = 48979478 from by norm_num]
      have h2 : (5 : ZMod 159526159847) ^ 48979478 = ((110271628876 : ℕ) : ZMod 159526159847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159526159847 - 1) / 61687 = 2586058 from by norm_num]
      have h2 : (5 : ZMod 159526159847) ^ 2586058 = ((69364311608 : ℕ) : ZMod 159526159847) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_25409026523137 : Nat.Prime 25409026523137 := by
  refine lucas_primality 25409026523137 (5 : ZMod 25409026523137) ?_ (fun q hq hd => ?_)
  · rw [show 25409026523137 - 1 = 25409026523136 from by norm_num]
    reduce_mod_char
  · have e : 25409026523137 - 1 = [2 ^ 34, 3 ^ 1, 17 ^ 1, 29 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25409026523137 - 1) / 2 = 12704513261568 from by norm_num]
      have h2 : (5 : ZMod 25409026523137) ^ 12704513261568 = ((25409026523136 : ℕ) : ZMod 25409026523137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25409026523137 - 1) / 3 = 8469675507712 from by norm_num]
      have h2 : (5 : ZMod 25409026523137) ^ 8469675507712 = ((21491292258933 : ℕ) : ZMod 25409026523137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25409026523137 - 1) / 17 = 1494648619008 from by norm_num]
      have h2 : (5 : ZMod 25409026523137) ^ 1494648619008 = ((9336019829233 : ℕ) : ZMod 25409026523137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25409026523137 - 1) / 29 = 876173328384 from by norm_num]
      have h2 : (5 : ZMod 25409026523137) ^ 876173328384 = ((6002999543950 : ℕ) : ZMod 25409026523137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12704513261569 : Nat.Prime 12704513261569 := by
  refine lucas_primality 12704513261569 (11 : ZMod 12704513261569) ?_ (fun q hq hd => ?_)
  · rw [show 12704513261569 - 1 = 12704513261568 from by norm_num]
    reduce_mod_char
  · have e : 12704513261569 - 1 = [2 ^ 33, 3 ^ 1, 17 ^ 1, 29 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12704513261569 - 1) / 2 = 6352256630784 from by norm_num]
      have h2 : (11 : ZMod 12704513261569) ^ 6352256630784 = ((12704513261568 : ℕ) : ZMod 12704513261569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12704513261569 - 1) / 3 = 4234837753856 from by norm_num]
      have h2 : (11 : ZMod 12704513261569) ^ 4234837753856 = ((12374367498982 : ℕ) : ZMod 12704513261569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12704513261569 - 1) / 17 = 747324309504 from by norm_num]
      have h2 : (11 : ZMod 12704513261569) ^ 747324309504 = ((52898938205 : ℕ) : ZMod 12704513261569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12704513261569 - 1) / 29 = 438086664192 from by norm_num]
      have h2 : (11 : ZMod 12704513261569) ^ 438086664192 = ((11634122167594 : ℕ) : ZMod 12704513261569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem fdvd_22_64658705994591851009055774868504577 : 64658705994591851009055774868504577 ∣ 1 + 2 ^ 4194304 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_22 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz64658705994591851009055774868504577 : z ≠ 64658705994591851009055774868504577)
    (hd : 1 + 2 ^ 4194304 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g64658705994591851009055774868504577 : 64658705994591851009055774868504577 ∈ P := S2 _ prime_64658705994591851009055774868504577 (by norm_num) (hnz hz64658705994591851009055774868504577) (fdvd_22_64658705994591851009055774868504577.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g64658705994591851009055774868504577 (by norm_num)

theorem fdvd_23_167772161 : 167772161 ∣ 1 + 2 ^ 8388608 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_23 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz27962027 : z ≠ 27962027) (hz167772161 : z ≠ 167772161)
    (hd : 1 + 2 ^ 8388608 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g167772161 : 167772161 ∈ P := S2 _ prime_167772161 (by norm_num) (hnz hz167772161) (fdvd_23_167772161.trans hd)
  have g27962027 : 27962027 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz27962027) _ g167772161 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g27962027 (by norm_num)

theorem fdvd_25_204393464266227713 : 204393464266227713 ∣ 1 + 2 ^ 33554432 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_25 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz204393464266227713 : z ≠ 204393464266227713)
    (hd : 1 + 2 ^ 33554432 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g204393464266227713 : 204393464266227713 ∈ P := S2 _ prime_204393464266227713 (by norm_num) (hnz hz204393464266227713) (fdvd_25_204393464266227713.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g204393464266227713 (by norm_num)

theorem fdvd_26_76861124116481 : 76861124116481 ∣ 1 + 2 ^ 67108864 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_26 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz12810187352747 : z ≠ 12810187352747) (hz76861124116481 : z ≠ 76861124116481)
    (hd : 1 + 2 ^ 67108864 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g76861124116481 : 76861124116481 ∈ P := S2 _ prime_76861124116481 (by norm_num) (hnz hz76861124116481) (fdvd_26_76861124116481.trans hd)
  have g12810187352747 : 12810187352747 ∈ P := S1 _ prime_12810187352747 (by norm_num) (hnz hz12810187352747) _ g76861124116481 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g76861124116481 _ g12810187352747 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_27_151413703311361 : 151413703311361 ∣ 1 + 2 ^ 134217728 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_27 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz179 : z ≠ 179) (hz151413703311361 : z ≠ 151413703311361)
    (hd : 1 + 2 ^ 134217728 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g151413703311361 : 151413703311361 ∈ P := S2 _ prime_151413703311361 (by norm_num) (hnz hz151413703311361) (fdvd_27_151413703311361.trans hd)
  have g179 : 179 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz179) _ g151413703311361 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g179 (by norm_num)

theorem fkill_27_alt {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz251 : z ≠ 251) (hz151413703311361 : z ≠ 151413703311361)
    (hd : 1 + 2 ^ 134217728 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g151413703311361 : 151413703311361 ∈ P := S2 _ prime_151413703311361 (by norm_num) (hnz hz151413703311361) (fdvd_27_151413703311361.trans hd)
  have g251 : 251 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz251) _ g151413703311361 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g251 (by norm_num)

theorem fdvd_28_1766730974551267606529 : 1766730974551267606529 ∣ 1 + 2 ^ 268435456 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_28 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz1766730974551267606529 : z ≠ 1766730974551267606529)
    (hd : 1 + 2 ^ 268435456 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1766730974551267606529 : 1766730974551267606529 ∈ P := S2 _ prime_1766730974551267606529 (by norm_num) (hnz hz1766730974551267606529) (fdvd_28_1766730974551267606529.trans hd)
  have g5 : 5 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz5) _ g1766730974551267606529 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g1766730974551267606529 _ g5 (by norm_num) (by norm_num)) (by norm_num)

theorem fkill_28_alt {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz11 : z ≠ 11) (hz1766730974551267606529 : z ≠ 1766730974551267606529)
    (hd : 1 + 2 ^ 268435456 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1766730974551267606529 : 1766730974551267606529 ∈ P := S2 _ prime_1766730974551267606529 (by norm_num) (hnz hz1766730974551267606529) (fdvd_28_1766730974551267606529.trans hd)
  have g11 : 11 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz11) _ g1766730974551267606529 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g1766730974551267606529 _ g11 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_29_2405286912458753 : 2405286912458753 ∣ 1 + 2 ^ 536870912 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_29 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz2405286912458753 : z ≠ 2405286912458753)
    (hd : 1 + 2 ^ 536870912 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2405286912458753 : 2405286912458753 ∈ P := S2 _ prime_2405286912458753 (by norm_num) (hnz hz2405286912458753) (fdvd_29_2405286912458753.trans hd)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g2405286912458753 (by norm_num)

theorem fdvd_30_640126220763137 : 640126220763137 ∣ 1 + 2 ^ 1073741824 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fdvd_30_1095981164658689 : 1095981164658689 ∣ 1 + 2 ^ 1073741824 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_30 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz640126220763137 : z ≠ 640126220763137) (hz1095981164658689 : z ≠ 1095981164658689)
    (hd : 1 + 2 ^ 1073741824 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g640126220763137 : 640126220763137 ∈ P := S2 _ prime_640126220763137 (by norm_num) (hnz hz640126220763137) (fdvd_30_640126220763137.trans hd)
  have g1095981164658689 : 1095981164658689 ∈ P := S2 _ prime_1095981164658689 (by norm_num) (hnz hz1095981164658689) (fdvd_30_1095981164658689.trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g640126220763137 _ g1095981164658689 (by norm_num) (by norm_num)) (by norm_num)

theorem fdvd_31_46931635677864055013377 : 46931635677864055013377 ∣ 1 + 2 ^ 2147483648 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_31 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz159526159847 : z ≠ 159526159847) (hz3352259691276003929527 : z ≠ 3352259691276003929527) (hz46931635677864055013377 : z ≠ 46931635677864055013377)
    (hd : 1 + 2 ^ 2147483648 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g46931635677864055013377 : 46931635677864055013377 ∈ P := S2 _ prime_46931635677864055013377 (by norm_num) (hnz hz46931635677864055013377) (fdvd_31_46931635677864055013377.trans hd)
  have g3352259691276003929527 : 3352259691276003929527 ∈ P := S1 _ prime_3352259691276003929527 (by norm_num) (hnz hz3352259691276003929527) _ g46931635677864055013377 (by norm_num)
  have g159526159847 : 159526159847 ∈ P := S1 _ prime_159526159847 (by norm_num) (hnz hz159526159847) _ g3352259691276003929527 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (hnz hz3) _ g159526159847 (by norm_num)

theorem fdvd_32_25409026523137 : 25409026523137 ∣ 1 + 2 ^ 4294967296 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  reduce_mod_char

theorem fkill_32 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz167 : z ≠ 167) (hz12704513261569 : z ≠ 12704513261569) (hz25409026523137 : z ≠ 25409026523137)
    (hd : 1 + 2 ^ 4294967296 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25409026523137 : 25409026523137 ∈ P := S2 _ prime_25409026523137 (by norm_num) (hnz hz25409026523137) (fdvd_32_25409026523137.trans hd)
  have g12704513261569 : 12704513261569 ∈ P := S1 _ prime_12704513261569 (by norm_num) (hnz hz12704513261569) _ g25409026523137 (by norm_num)
  have g5 : 5 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz5) _ g12704513261569 (by norm_num)
  have g167 : 167 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz167) _ g12704513261569 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g5 _ g167 (by norm_num) (by norm_num)) (by norm_num)

theorem fkill_32_alt1 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz7 : z ≠ 7) (hz13 : z ≠ 13) (hz167 : z ≠ 167) (hz12704513261569 : z ≠ 12704513261569) (hz25409026523137 : z ≠ 25409026523137)
    (hd : 1 + 2 ^ 4294967296 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25409026523137 : 25409026523137 ∈ P := S2 _ prime_25409026523137 (by norm_num) (hnz hz25409026523137) (fdvd_32_25409026523137.trans hd)
  have g12704513261569 : 12704513261569 ∈ P := S1 _ prime_12704513261569 (by norm_num) (hnz hz12704513261569) _ g25409026523137 (by norm_num)
  have g13 : 13 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz13) _ g12704513261569 (by norm_num)
  have g167 : 167 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz167) _ g12704513261569 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz hz7) _ g13 _ g167 (by norm_num) (by norm_num)) (by norm_num)

theorem fkill_32_alt2 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (hz3 : z ≠ 3) (hz5 : z ≠ 5) (hz2081 : z ≠ 2081) (hz12704513261569 : z ≠ 12704513261569) (hz25409026523137 : z ≠ 25409026523137)
    (hd : 1 + 2 ^ 4294967296 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ z ^ e → c ∈ ({z} : Finset ℕ) := fun c hc h =>
    Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc hz).mp (hc.dvd_of_dvd_pow h))
  have hnz : ∀ {c : ℕ}, z ≠ c → c ∉ ({z} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h').symm
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25409026523137 : 25409026523137 ∈ P := S2 _ prime_25409026523137 (by norm_num) (hnz hz25409026523137) (fdvd_32_25409026523137.trans hd)
  have g12704513261569 : 12704513261569 ∈ P := S1 _ prime_12704513261569 (by norm_num) (hnz hz12704513261569) _ g25409026523137 (by norm_num)
  have g5 : 5 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz5) _ g12704513261569 (by norm_num)
  have g2081 : 2081 ∈ P := S1 _ (by norm_num) (by norm_num) (hnz hz2081) _ g12704513261569 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (hnz hz3) _ g5 _ g2081 (by norm_num) (by norm_num)) (by norm_num)

theorem H2_two_adic_high {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz5 : 5 ≤ z)
    (hz2100 : z < 2100) (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) :
    (padicValNat 2 n % 8388608 ≠ 4194304) ∧
    (padicValNat 2 n % 16777216 ≠ 8388608) ∧
    (padicValNat 2 n % 67108864 ≠ 33554432) ∧
    (padicValNat 2 n % 134217728 ≠ 67108864) ∧
    (padicValNat 2 n % 268435456 ≠ 134217728) ∧
    (padicValNat 2 n % 536870912 ≠ 268435456) ∧
    (padicValNat 2 n % 1073741824 ≠ 536870912) ∧
    (padicValNat 2 n % 2147483648 ≠ 1073741824) ∧
    (padicValNat 2 n % 4294967296 ≠ 2147483648) ∧
    (padicValNat 2 n % 8589934592 ≠ 4294967296) := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by omega) hs
  rw [← Nat.factorization_def n Nat.prime_two]
  have D : ∀ e0 : ℕ, n.factorization 2 % (2 * e0) = e0 → 1 + 2 ^ e0 ∣ 2 ^ n.factorization 2 + 1 :=
    fun e0 he0 => by
      have := one_add_pow_dvd_of_odd_mul (z := 2) he0
      rwa [add_comm 1 (2 ^ n.factorization 2)] at this
  exact ⟨fun hr => fkill_22 hP hz E (by omega) (by omega) (D 4194304 (by omega)),
    fun hr => fkill_23 hP hz E (by omega) (by omega) (by omega) (D 8388608 (by omega)),
    fun hr => fkill_25 hP hz E (by omega) (by omega) (D 33554432 (by omega)),
    fun hr => fkill_26 hP hz E (by omega) (by omega) (by omega) (D 67108864 (by omega)),
    fun hr => by
      by_cases hA : z = 179
      · exact fkill_27_alt hP hz E (by omega) (by omega) (by omega) (D 134217728 (by omega))
      · exact fkill_27 hP hz E (by omega) (by omega) (by omega) (D 134217728 (by omega)),
    fun hr => by
      by_cases hA : z = 5
      · exact fkill_28_alt hP hz E (by omega) (by omega) (by omega) (D 268435456 (by omega))
      · exact fkill_28 hP hz E (by omega) (by omega) (by omega) (D 268435456 (by omega)),
    fun hr => fkill_29 hP hz E (by omega) (by omega) (D 536870912 (by omega)),
    fun hr => fkill_30 hP hz E (by omega) (by omega) (by omega) (D 1073741824 (by omega)),
    fun hr => fkill_31 hP hz E (by omega) (by omega) (by omega) (by omega) (D 2147483648 (by omega)),
    fun hr => by
      by_cases hA : z = 5
      · exact fkill_32_alt1 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 4294967296 (by omega))
      by_cases hB : z = 167
      · exact fkill_32_alt2 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 4294967296 (by omega))
      exact fkill_32 hP hz E (by omega) (by omega) (by omega) (by omega) (by omega) (D 4294967296 (by omega))⟩

theorem hK54 : ∀ c : ℕ, c.Prime → c ∣ 5 ^ 4 → c ∈ ({5} : Finset ℕ) := fun c hc h =>
  Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc (by norm_num)).mp (hc.dvd_of_dvd_pow h))

theorem core5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) :
    3 ∈ P ∧ (∀ p ∈ P, ¬ 3 ∣ p + 1) ∧ 313 ∈ P ∧ 157 ∈ P ∧ 79 ∈ P ∧ (∀ p ∈ P, ¬ 313 ∣ p + 1) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK54 E
  have h3 : 3 ∣ 2 ^ m + 1 := three_dvd_two_pow_add_one hm
  have n3 : (3 : ℕ) ∉ ({5} : Finset ℕ) := by decide
  have g3 := S2 3 (by norm_num) (by norm_num) n3 h3
  have g313 := S7 313 (by norm_num) (by norm_num) (by decide) (by norm_num)
  have g157 := S1 157 (by norm_num) (by norm_num) (by decide) 313 g313 (by norm_num)
  have g79 := S1 79 (by norm_num) (by norm_num) (by decide) 157 g157 (by norm_num)
  exact ⟨g3, fun p hp => S4 3 (by norm_num) (by norm_num) n3 h3 p hp, g313, g157, g79,
    fun p hp => S8 313 (by norm_num) (by norm_num) (by decide) (by norm_num) p hp⟩

theorem budget5 {m : ℕ} {P A : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hA : A ⊆ P) : ¬ 5 ^ 5 ∣ ∏ p ∈ A, (p + 1) := by
  intro h
  have h1 : ∏ p ∈ A, (p + 1) ∣ ∏ p ∈ P, (p + 1) := Finset.prod_dvd_prod_of_subset _ _ _ hA
  have h2 : 5 ^ 5 ∣ 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p := by
    rw [← E]
    exact (h.trans h1).mul_left _
  have e : 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p = 5 ^ 4 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
  rw [e, pow_succ] at h2
  have h3 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  have p5 : (5 : ℕ).Prime := by norm_num
  rcases (Nat.Prime.dvd_mul p5).mp h3 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq p5 Nat.prime_two).mp (p5.dvd_of_dvd_pow h)
    omega
  · obtain ⟨p, hp, h5p⟩ := (Prime.dvd_finsetProd_iff p5.prime _).mp h
    have := (Nat.prime_dvd_prime_iff_eq p5 (hP p hp).1).mp h5p
    exact hP5 (this ▸ hp)

theorem zleaf_cases {q : ℕ} (hq : q.Prime) (hl : ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5)
    (h5 : 5 ∣ q + 1) : q = 19 ∨ q = 79 ∨ q = 199 ∨ q = 499 ∨ 1249 ≤ q := by
  obtain ⟨k, j, hkj⟩ := two_pow_mul_pow_of_odd_primes_eq (M := q + 1) (z := 5) (by omega) hl
  by_contra hcon
  have hlt : q < 1249 := by omega
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h5j : 1 ≤ 5 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have hk : k < 11 := by
    by_contra h
    have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hj : j < 5 := by
    by_contra h
    have : 5 ^ 5 ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have hq' : q = 2 ^ k * 5 ^ j - 1 := by omega
  interval_cases k <;> interval_cases j <;> norm_num at hq' <;> subst hq' <;>
    first | (norm_num at hq; done) | (norm_num at hcon; done) | (norm_num at h5; done)

theorem master5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (thr : ℕ) (I IL Ms : Finset ℕ) (hIP : I ⊆ P) (hI : ∀ p ∈ P, p < thr → p ∈ I)
    (hIL : ∀ q ∈ I, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ IL) (hILI : IL ⊆ I)
    (hMs : ∀ q ∈ ({3, 7, 31, 127} : Finset ℕ), thr ≤ q → q ∉ I → q ∈ Ms)
    (hMs2 : ∀ q ∈ Ms, 2 ≤ q)
    (c5 : ℕ) (hc5 : 5 ^ c5 ∣ ∏ p ∈ I, (p + 1))
    (zm : ℕ) (hzm2 : 2 ≤ zm)
    (hzm : ∀ q : ℕ, q.Prime → thr ≤ q → q ∉ I →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → 5 ∣ q + 1 → zm ≤ q) :
    2 ≤ (1 + 1 / (2 : ℚ) ^ m) * (626 / 625) * ((∏ q ∈ IL, β q) *
      (∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (2048 / 2047) *
      (((zm : ℚ) + 1) / ((zm : ℚ) - 1)) ^ (4 - c5)) := by
  classical
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK54 (by norm_num) E β hB h4
  have hleaf : ∀ q ∈ L, ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5 := fun q hq c hc h2 hd =>
    Finset.mem_singleton.mp (hLleaf q hq c hc h2 hd)
  have hβ1 : ∀ p ∈ P, 1 ≤ β p := fun p hp => by
    have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hB1 : ∀ q : ℕ, 2 ≤ q → (1 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hβ0 : ∀ q ∈ L, 0 ≤ β q := fun q hq => le_trans zero_le_one (hβ1 q (hLP hq))
  have hBq : ∀ q ∈ L, β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => (hB q (hLP hq)).2
  have p1 : ∏ q ∈ L.filter (fun q => q ∈ I), β q ≤ ∏ q ∈ IL, β q := by
    refine Finset.prod_le_prod_of_subset_of_one_le (f := β) ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqL, hqI⟩ := Finset.mem_filter.mp hq
      exact hIL q hqI (hleaf q hqL)
    · intro q hq
      exact hβ0 q (Finset.mem_filter.mp hq).1
    · intro q hq _
      exact hβ1 q (hIP (hILI hq))
  have hge : ∀ q ∈ L.filter (fun q => q ∉ I), thr ≤ q := fun q hq => by
    obtain ⟨hqL, hqI⟩ := Finset.mem_filter.mp hq
    by_contra h
    exact hqI (hI q (hLP hqL) (by omega))
  have hZsub : (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1) ⊆ P := fun q hq =>
    hLP (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hZcard : c5 + ((L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1)).card ≤ 4 := by
    by_contra hcon
    apply budget5 hP hP5 E (Finset.union_subset hIP hZsub)
    have hdisj : Disjoint I ((L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1)) :=
      Finset.disjoint_left.mpr (fun q hqI hqZ =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hqZ).1).2 hqI)
    rw [Finset.prod_union hdisj]
    have hZd : 5 ^ ((L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1)).card ∣
        ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1), (q + 1) := by
      rw [← Finset.prod_const]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => (Finset.mem_filter.mp hq).2)
    have h55 : 5 ≤ c5 + ((L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1)).card := by omega
    exact (Nat.pow_dvd_pow 5 h55).trans (by rw [pow_add]; exact mul_dvd_mul hc5 hZd)
  have pZ : ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1), β q ≤
      (((zm : ℚ) + 1) / ((zm : ℚ) - 1)) ^ (4 - c5) := by
    have h1 : ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1), β q ≤
        ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1),
          (((zm : ℚ) + 1) / ((zm : ℚ) - 1)) := by
      refine Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp
        (Finset.mem_filter.mp hq).1).1) (fun q hq => ?_)
      obtain ⟨hq1, h5⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hqI⟩ := Finset.mem_filter.mp hq1
      exact (hBq q hqL).trans (B_anti hzm2
        (hzm q (hP q (hLP hqL)).1 (hge q hq1) hqI (hleaf q hqL) h5))
    rw [Finset.prod_const] at h1
    exact h1.trans (pow_le_pow_right₀ (hB1 zm hzm2) (by omega))
  have hM2pow : ∀ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => ¬ 5 ∣ q + 1),
      ∃ k, q + 1 = 2 ^ k := fun q hq => by
    obtain ⟨hq1, h5⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqL, -⟩ := Finset.mem_filter.mp hq1
    exact two_pow_of_no_odd_prime (fun c hc h2 hd => h5 (hleaf q hqL c hc h2 hd ▸ hd))
  have pM : ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => ¬ 5 ∣ q + 1), β q ≤
      (∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (2048 / 2047) := by
    set M2 := (L.filter (fun q => q ∉ I)).filter (fun q => ¬ 5 ∣ q + 1) with hM2
    have hM2L : ∀ q ∈ M2, q ∈ L := fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have hsplit := Finset.prod_filter_mul_prod_filter_not M2 (fun q => q < 8191) β
    have hsmall : ∏ q ∈ M2.filter (fun q => q < 8191), β q ≤
        ∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1)) := by
      calc ∏ q ∈ M2.filter (fun q => q < 8191), β q
          ≤ ∏ q ∈ M2.filter (fun q => q < 8191), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
            Finset.prod_le_prod (fun q hq => hβ0 q (hM2L q (Finset.mem_filter.mp hq).1))
              (fun q hq => hBq q (hM2L q (Finset.mem_filter.mp hq).1))
        _ ≤ ∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1)) := by
            refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
            · intro q hq
              obtain ⟨hqM, hlt⟩ := Finset.mem_filter.mp hq
              obtain ⟨hq1, -⟩ := Finset.mem_filter.mp hqM
              obtain ⟨k, hk⟩ := hM2pow q hqM
              have hm := mersenne_small (hP q (hLP (hM2L q hqM))).1 hk hlt
              refine hMs q ?_ (hge q hq1) (Finset.mem_filter.mp hq1).2
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact hm
            · intro q hq
              exact le_trans zero_le_one (hB1 q (hP q (hLP (hM2L q
                (Finset.mem_filter.mp hq).1))).1.two_le)
            · intro q hq _
              exact hB1 q (hMs2 q hq)
    have htail : ∏ q ∈ M2.filter (fun q => ¬ q < 8191), β q ≤ 2048 / 2047 := by
      have hmemT : ∀ q ∈ M2.filter (fun q => ¬ q < 8191), q ∈ M2 ∧ 8191 ≤ q := fun q hq => by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
        exact ⟨h1, by omega⟩
      have hle : ∏ q ∈ M2.filter (fun q => ¬ q < 8191), β q ≤
          ∏ q ∈ M2.filter (fun q => ¬ q < 8191), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
        Finset.prod_le_prod (fun q hq => hβ0 q (hM2L q (hmemT q hq).1))
          (fun q hq => hBq q (hM2L q (hmemT q hq).1))
      have htb := tail_bound _ _ 8191 rfl (by norm_num) (fun q hq => (hmemT q hq).2)
        (fun q hq q' hq' hlt => by
          obtain ⟨k, hk⟩ := hM2pow q (hmemT q hq).1
          obtain ⟨k', hk'⟩ := hM2pow q' (hmemT q' hq').1
          have hkk : k < k' := by
            by_contra hcon
            have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [pow_succ] at this
          omega)
      refine hle.trans (htb.trans ?_)
      norm_num
    rw [← hsplit]
    refine mul_le_mul hsmall htail ?_ ?_
    · exact Finset.prod_nonneg fun q hq => hβ0 q (hM2L q (Finset.mem_filter.mp hq).1)
    · exact Finset.prod_nonneg fun q hq => le_trans zero_le_one (hB1 q (hMs2 q hq))
  have hL : ∏ q ∈ L, β q ≤ (∏ q ∈ IL, β q) * (∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1))) *
      (2048 / 2047) * (((zm : ℚ) + 1) / ((zm : ℚ) - 1)) ^ (4 - c5) := by
    rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => q ∈ I),
      ← Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => q ∉ I)) (fun q => 5 ∣ q + 1)]
    have n1 : 0 ≤ ∏ q ∈ L.filter (fun q => q ∈ I), β q :=
      Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp hq).1
    have n2 : 0 ≤ ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1), β q :=
      Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have n3 : 0 ≤ ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => ¬ 5 ∣ q + 1), β q :=
      Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have n4 : 0 ≤ ∏ q ∈ IL, β q := Finset.prod_nonneg fun q hq => le_trans zero_le_one (hβ1 q (hIP (hILI hq)))
    have n5 : 0 ≤ (∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (2048 / 2047) :=
      mul_nonneg (Finset.prod_nonneg fun q hq => le_trans zero_le_one (hB1 q (hMs2 q hq))) (by norm_num)
    calc (∏ q ∈ L.filter (fun q => q ∈ I), β q) *
          ((∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => 5 ∣ q + 1), β q) *
            ∏ q ∈ (L.filter (fun q => q ∉ I)).filter (fun q => ¬ 5 ∣ q + 1), β q)
        ≤ (∏ q ∈ IL, β q) * ((((zm : ℚ) + 1) / ((zm : ℚ) - 1)) ^ (4 - c5) *
            ((∏ q ∈ Ms, (((q : ℚ) + 1) / ((q : ℚ) - 1))) * (2048 / 2047))) :=
          mul_le_mul p1 (mul_le_mul pZ pM n3 (pow_nonneg (le_trans zero_le_one (hB1 zm hzm2)) _))
            (mul_nonneg n2 n3) n4
      _ = _ := by ring
  have e : (((1 + 5 ^ 4 : ℕ) : ℚ) / ((5 ^ 4 : ℕ) : ℚ)) = 626 / 625 := by norm_num
  rw [e] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_left hL (by positivity))

theorem step_ge {c t p : ℕ} {x v : ℚ} (ht : 2 ≤ t) (hp : t ≤ p)
    (hx : x ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (hv : (1 + 1 / (c : ℚ)) * (((t : ℚ) + 1) / ((t : ℚ) - 1)) ≤ v) : (1 + 1 / (c : ℚ)) * x ≤ v :=
  (mul_le_mul_of_nonneg_left (hx.trans (B_anti ht hp)) (by positivity)).trans hv

theorem fin5 {m : ℕ} (hm : 13 ≤ m) {X : ℚ} (h : 2 ≤ (1 + 1 / (2 : ℚ) ^ m) * (626 / 625) * X)
    (hlt : (1 + 1 / 8192) * (626 / 625) * X < 2) : False := by
  have h2 : (2 : ℚ) ^ 13 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hpos : (0 : ℚ) < 2 ^ m := by positivity
  have h3 : 1 / (2 : ℚ) ^ m ≤ 1 / 8192 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    norm_num at h2 ⊢
    linarith
  have hX : 0 ≤ X := by
    by_contra hneg
    push_neg at hneg
    have : (1 + 1 / (2 : ℚ) ^ m) * (626 / 625) * X < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have : (1 + 1 / (2 : ℚ) ^ m) * (626 / 625) * X ≤ (1 + 1 / 8192) * (626 / 625) * X := by
    apply mul_le_mul_of_nonneg_right _ hX
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith
  linarith

set_option maxHeartbeats 1000000 in
theorem node_12 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (5120 / 4869 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (4960 / 4869 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (1400 / 1389 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 397 then (1393 / 1389 : ℚ) else if p = 487 then (4880 / 4869 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 487 := S3 61 (by norm_num) (by norm_num) (by decide) p hp 487 (hIP 487 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 397 := S3 199 (by norm_num) (by norm_num) (by decide) p hp 397 (hIP 397 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 5557 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 9739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 199 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 61 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397, 487} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (224 / 213 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (217 / 213 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (1400 / 1389 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 397 then (1393 / 1389 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 853 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 397 := S3 199 (by norm_num) (by norm_num) (by decide) p hp 397 (hIP 397 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 5557 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 199 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 398 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_409 : 409 ∉ P := fun hq => budget5 hP hP5 E (A := insert 409 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_421 : 421 ∉ P := fun hq => absurd (hI 211 (S1 211 (by norm_num) (by norm_num) (by decide) 421 hq (by norm_num)) (by norm_num)) (by simp)
  have x_433 : 433 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 433 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_439 : 439 ∉ P := fun hq => budget5 hP hP5 E (A := insert 439 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_457 : 457 ∉ P := fun hq => absurd (hI 229 (S1 229 (by norm_num) (by norm_num) (by decide) 457 hq (by norm_num)) (by norm_num)) (by simp)
  have x_463 : 463 ∉ P := fun hq => h3 29 (S1 29 (by norm_num) (by norm_num) (by decide) 463 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 487 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313, 397} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 398
    · exact hI p hp hpt
    have hge : 398 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 487 ∈ P
  · exact node_12 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 487
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 487 := by omega
            subst this
            simp)
  · exact node_13 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 487
          · exact hJ p hp h
          · have : p = 487 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_14 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 398 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (3200 / 3183 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 398
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 6367 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 32 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 398 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_10 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_211 : 211 ∉ P := fun hq => h3 53 (S1 53 (by norm_num) (by norm_num) (by decide) 211 hq (by norm_num)) (by norm_num)
  have x_223 : 223 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 223 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_229 : 229 ∉ P := fun hq => budget5 hP hP5 E (A := insert 229 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_241 : 241 ∉ P := fun hq => S6 11 (by norm_num) (by norm_num) (by decide) 241 hq (by norm_num)
  have x_271 : 271 ∉ P := fun hq => h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 271 hq (by norm_num)) (by norm_num)
  have x_277 : 277 ∉ P := fun hq => absurd (hI 139 (S1 139 (by norm_num) (by norm_num) (by decide) 277 hq (by norm_num)) (by norm_num)) (by simp)
  have x_283 : 283 ∉ P := fun hq => h3 71 (S1 71 (by norm_num) (by norm_num) (by decide) 283 hq (by norm_num)) (by norm_num)
  have x_307 : 307 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 307 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_331 : 331 ∉ P := fun hq => h3 83 (S1 83 (by norm_num) (by norm_num) (by decide) 331 hq (by norm_num)) (by norm_num)
  have x_337 : 337 ∉ P := fun hq => S6 13 (by norm_num) (by norm_num) (by decide) 337 hq (by norm_num)
  have x_349 : 349 ∉ P := fun hq => budget5 hP hP5 E (A := insert 349 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have x_367 : 367 ∉ P := fun hq => h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 367 hq (by norm_num)) (by norm_num)
  have x_373 : 373 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 373 hq (by norm_num)) (by norm_num)
  have x_379 : 379 ∉ P := fun hq => budget5 hP hP5 E (A := insert 379 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ))
      (Finset.insert_subset hq (fun p hp => hIP p hp)) (by decide)
  have hJ : ∀ p ∈ P, p < 397 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 199, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 200
    · exact hI p hp hpt
    have hge : 200 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 397 ∈ P
  · exact node_11 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 397
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 397 := by omega
            subst this
            simp)
  · exact node_14 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 397
          · exact hJ p hp h
          · have : p = 397 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (5120 / 4869 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (4960 / 4869 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else if p = 487 then (4880 / 4869 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 487 := S3 61 (by norm_num) (by norm_num) (by decide) p hp 487 (hIP 487 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 9739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 61 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313, 487} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 488 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (224 / 213 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (217 / 213 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 853 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 488
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 488 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_211 : 211 ∉ P := fun hq => h3 53 (S1 53 (by norm_num) (by norm_num) (by decide) 211 hq (by norm_num)) (by norm_num)
  have x_223 : 223 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 223 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_229 : 229 ∉ P := fun hq => h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 229 hq (by norm_num)) (by norm_num)
  have x_241 : 241 ∉ P := fun hq => S6 11 (by norm_num) (by norm_num) (by decide) 241 hq (by norm_num)
  have x_271 : 271 ∉ P := fun hq => h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 271 hq (by norm_num)) (by norm_num)
  have x_277 : 277 ∉ P := fun hq => absurd (hI 139 (S1 139 (by norm_num) (by norm_num) (by decide) 277 hq (by norm_num)) (by norm_num)) (by simp)
  have x_283 : 283 ∉ P := fun hq => h3 71 (S1 71 (by norm_num) (by norm_num) (by decide) 283 hq (by norm_num)) (by norm_num)
  have x_307 : 307 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 307 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_331 : 331 ∉ P := fun hq => h3 83 (S1 83 (by norm_num) (by norm_num) (by decide) 331 hq (by norm_num)) (by norm_num)
  have x_337 : 337 ∉ P := fun hq => S6 13 (by norm_num) (by norm_num) (by decide) 337 hq (by norm_num)
  have x_349 : 349 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 349 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_367 : 367 ∉ P := fun hq => h3 23 (S1 23 (by norm_num) (by norm_num) (by decide) 367 hq (by norm_num)) (by norm_num)
  have x_373 : 373 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 373 hq (by norm_num)) (by norm_num)
  have x_379 : 379 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 379 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_397 : 397 ∉ P := fun hq => absurd (hI 199 (S1 199 (by norm_num) (by norm_num) (by decide) 397 hq (by norm_num)) (by norm_num)) (by simp)
  have x_409 : 409 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 409 hq (by norm_num)) (by norm_num)
  have x_421 : 421 ∉ P := fun hq => x_211 (S1 211 (by norm_num) (by norm_num) (by decide) 421 hq (by norm_num))
  have x_433 : 433 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 433 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_439 : 439 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 439 hq (by norm_num)) (by norm_num)
  have x_457 : 457 ∉ P := fun hq => x_229 (S1 229 (by norm_num) (by norm_num) (by decide) 457 hq (by norm_num))
  have x_463 : 463 ∉ P := fun hq => h3 29 (S1 29 (by norm_num) (by norm_num) (by decide) 463 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 487 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 200
    · exact hI p hp hpt
    have hge : 200 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 487 ∈ P
  · exact node_16 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 487
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 487 := by omega
            subst this
            simp)
  · exact node_17 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 487
          · exact hJ p hp h
          · have : p = 487 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num)
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact node_10 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact node_15 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_20 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_18 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num)
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact node_19 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact node_20 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_9 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_18 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_24 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_22 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num)
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact node_23 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact node_24 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_25 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num)
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (26 / 21 : ℚ) else if p = 13 then (13 / 12 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 337 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 26 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 199
      · have hpI := hJ p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 199 ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hJ hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_22 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_25 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact node_8 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact node_21 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_29 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 199 then (100 / 99 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 397 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 199, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127, 199} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 4 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_30 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 200 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 200
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 200 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 499 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_28 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_139 : 139 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 139 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_151 : 151 ∉ P := fun hq => absurd (S3 19 (by norm_num) (by norm_num) (by decide) 151 hq 37
      (hIP 37 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_163 : 163 ∉ P := fun hq => h3 41 (S1 41 (by norm_num) (by norm_num) (by decide) 163 hq (by norm_num)) (by norm_num)
  have x_181 : 181 ∉ P := fun hq => absurd (S3 7 (by norm_num) (by norm_num) (by decide) 181 hq 13
      (hIP 13 (by simp)) (by norm_num) (by norm_num)) (by norm_num)
  have x_193 : 193 ∉ P := fun hq => absurd (hI 97 (S1 97 (by norm_num) (by norm_num) (by decide) 193 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 199 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 127, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 128
    · exact hI p hp hpt
    have hge : 128 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 199 ∈ P
  · exact node_29 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 199
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 199 := by omega
            subst this
            simp)
  · exact node_30 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 199
          · exact hJ p hp h
          · have : p = 199 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_27 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_28 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_31 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_33 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_34 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_32 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_33 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_34 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_26 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact node_27 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact node_32 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_67 : 67 ∉ P := fun hq => h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 67 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 73 → p ∈ ({3, 7, 13, 19, 31, 37, 61, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 62
    · exact hI p hp hpt
    have hge : 62 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 73 ∈ P
  · exact node_7 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 73
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 73 := by omega
            subst this
            simp)
  · exact node_26 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 73
          · exact hJ p hp h
          · have : p = 73 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_38 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 103, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_39 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (512 / 411 : ℚ) else if p = 13 then (448 / 411 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 103 then (416 / 411 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 103 := S3 13 (by norm_num) (by norm_num) (by decide) p hp 103 (hIP 103 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 823 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 13 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_37 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 103, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_38 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_39 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 127 then (112 / 111 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1777 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79, 127} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 127, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79, 127} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_42 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 128 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (56 / 45 : ℚ) else if p = 13 then (49 / 45 : ℚ) else if p = 19 then (56 / 51 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (266 / 255 : ℚ) else if p = 73 then (259 / 255 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 181 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 73 := S3 37 (by norm_num) (by norm_num) (by decide) p hp 73 (hIP 73 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 128
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 1021 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 37 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 128 ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) (∅ : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp at hq) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_40 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 104 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_109 : 109 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 109 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 127 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 104
    · exact hI p hp hpt
    have hge : 104 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 127 ∈ P
  · exact node_41 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 127
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 127 := by omega
            subst this
            simp)
  · exact node_42 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 127
          · exact hJ p hp h
          · have : p = 127 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_36 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_97 : 97 ∉ P := fun hq => S6 7 (by norm_num) (by norm_num) (by decide) 97 hq (by norm_num)
  have hJ : ∀ p ∈ P, p < 103 → p ∈ ({3, 7, 13, 19, 31, 37, 73, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 74
    · exact hI p hp hpt
    have hge : 74 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 103 ∈ P
  · exact node_37 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 103
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 103 := by omega
            subst this
            simp)
  · exact node_40 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 103
          · exact hJ p hp h
          · have : p = 103 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_43 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 74 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (400 / 369 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 37 then (380 / 369 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 37 := S3 19 (by norm_num) (by norm_num) (by decide) p hp 37 (hIP 37 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 74
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 739 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 20 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 19 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 74 ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_35 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_67 : 67 ∉ P := fun hq => h3 17 (S1 17 (by norm_num) (by norm_num) (by decide) 67 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 73 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 62
    · exact hI p hp hpt
    have hge : 62 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 73 ∈ P
  · exact node_36 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 73
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 73 := by omega
            subst this
            simp)
  · exact node_43 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 73
          · exact hJ p hp h
          · have : p = 73 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 38 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_43 : 43 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 43 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 61 → p ∈ ({3, 7, 13, 19, 31, 37, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 38
    · exact hI p hp hpt
    have hge : 38 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 61 ∈ P
  · exact node_6 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 61
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 61 := by omega
            subst this
            simp)
  · exact node_35 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 61
          · exact hJ p hp h
          · have : p = 61 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_45 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (16 / 15 : ℚ) else if p = 31 then (256 / 243 : ℚ) else if p = 61 then (248 / 243 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, n8, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 151 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 61 := S3 31 (by norm_num) (by norm_num) (by decide) p hp 61 (hIP 61 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 487 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 31 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 62 ({3, 7, 13, 19, 31, 61, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_46 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 62 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (16 / 15 : ℚ) else if p = 31 then (28 / 27 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, n7, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 151 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 62
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 433 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 31, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 62 ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 31, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_44 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 38 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_43 : 43 ∉ P := fun hq => h3 11 (S1 11 (by norm_num) (by norm_num) (by decide) 43 hq (by norm_num)) (by norm_num)
  have hJ : ∀ p ∈ P, p < 61 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 38
    · exact hI p hp hpt
    have hge : 38 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 61 ∈ P
  · exact node_45 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 61
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 61 := by omega
            subst this
            simp)
  · exact node_46 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 61
          · exact hJ p hp h
          · have : p = 61 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 32 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 37 → p ∈ ({3, 7, 13, 19, 31, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 32
    · exact hI p hp hpt
    have hge : 32 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 37 ∈ P
  · exact node_5 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 37
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 37 := by omega
            subst this
            simp)
  · exact node_44 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 37
          · exact hJ p hp h
          · have : p = 37 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_47 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 32 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, n6, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 32
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 32
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 32 ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 79} : Finset ℕ) ({127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 31 → p ∈ ({3, 7, 13, 19, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 20
    · exact hI p hp hpt
    have hge : 20 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 31 ∈ P
  · exact node_4 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 31
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 31 := by omega
            subst this
            simp)
  · exact node_47 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 31
          · exact hJ p hp h
          · have : p = 31 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_48 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (64 / 51 : ℚ) else if p = 13 then (56 / 51 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 13 := S3 7 (by norm_num) (by norm_num) (by decide) p hp 13 (hIP 13 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 103 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 8 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 7 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 13, 79, 157, 313} : Finset ℕ) ({3, 7, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 14 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 7, 13, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 14
    · exact hI p hp hpt
    have hge : 14 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact node_3 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact node_48 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_50 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (7 / 6 : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, n5, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 97 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 19, 79, 157, 313} : Finset ℕ) ({3, 7, 19, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_51 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 7 then (7 / 6 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 7, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 97 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 14 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 7, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 7, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 7, 79, 157, 313} : Finset ℕ) ({3, 7, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_49 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 14 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 14
    · exact hI p hp hpt
    have hge : 14 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact node_50 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact node_51 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 7, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 8 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 13 → p ∈ ({3, 7, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 8
    · exact hI p hp hpt
    have hge : 8 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 13 ∈ P
  · exact node_2 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 13
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 13 := by omega
            subst this
            simp)
  · exact node_49 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 13
          · exact hJ p hp h
          · have : p = 13 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_53 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 19, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 19, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 19 then (10 / 9 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 19, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 19, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3, n4⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, n4, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · by_cases hpt : p < 20
      · have hpI := hI p hp hpt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
        rcases hpI with rfl | rfl | rfl | rfl | rfl <;> omega
      · have hpp := (hP p hp).1
        have hp3 := h3 p hp
        have hpge : 37 ≤ p := by
          by_contra hlt
          obtain ⟨k, hk⟩ := hd
          have hk2 : k ≤ 2 := by omega
          interval_cases k <;> first | omega | (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hk; norm_num at hpp)
        refine step_ge (by norm_num) hpge (hB p hp).2 ?_
        rw [hβ]
        norm_num
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 19, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 19, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 19, 79, 157, 313} : Finset ℕ) ({3, 19, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 2 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_54 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 20 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then (4 / 3 : ℚ) else if p = 79 then (320 / 313 : ℚ) else if p = 157 then (316 / 313 : ℚ) else if p = 313 then (314 / 313 : ℚ) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases hpI : p ∈ ({3, 79, 157, 313} : Finset ℕ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hpI
      rcases hpI with rfl | rfl | rfl | rfl <;> rw [hβ] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpI
      obtain ⟨n0, n1, n2, n3⟩ := hpI
      rw [hβ]
      simp only [n0, n1, n2, n3, if_false]
      exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  have h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({5} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
      β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c := by
    intro p hp c hc hd hmin hne
    by_cases hcI : c ∈ ({3, 79, 157, 313} : Finset ℕ)
    swap
    · exfalso
      apply hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcI
      obtain ⟨n0, n1, n2, n3⟩ := hcI
      rw [hβ]
      simp only [n0, n1, n2, n3, if_false]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcI
    rcases hcI with rfl | rfl | rfl | rfl
    · exact absurd hd (h3 p hp)
    · obtain rfl : p = 157 := S3 79 (by norm_num) (by norm_num) (by decide) p hp 157 (hIP 157 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · obtain rfl : p = 313 := S3 157 (by norm_num) (by norm_num) (by decide) p hp 313 (hIP 313 (by simp)) hd
        (by norm_num)
      simp only [hβ]
      norm_num
    · exact absurd hd (h313 p hp)
  have hIL : ∀ q ∈ ({3, 79, 157, 313} : Finset ℕ), (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = 5) → q ∈ ({3, 79} : Finset ℕ) := by
    intro q hq hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact absurd (hl 79 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · exact absurd (hl 157 (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  have hX := master5 hP hP5 E β hB h4 20 ({3, 79, 157, 313} : Finset ℕ) ({3, 79} : Finset ℕ) ({31, 127} : Finset ℕ) (fun p hp => hIP p hp) hI hIL
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; omega)
    (by intro q hq h1 h2; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl <;> first | omega | (exfalso; apply h2; simp; done) | simp)
    (by intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq; omega) 1 (by decide) 199 (by norm_num)
    (by intro q hq h1 h2 hl h5
        rcases zleaf_cases hq hl h5 with rfl | rfl | rfl | rfl | h <;> first | omega | (exfalso; apply h2; simp; done))
  exact fin5 hm hX (by norm_num [hβ, Finset.prod_insert, Finset.prod_singleton])

set_option maxHeartbeats 1000000 in
theorem node_52 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 8 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have x_13 : 13 ∉ P := fun hq => absurd (hI 7 (S1 7 (by norm_num) (by norm_num) (by decide) 13 hq (by norm_num)) (by norm_num)) (by simp)
  have hJ : ∀ p ∈ P, p < 19 → p ∈ ({3, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 8
    · exact hI p hp hpt
    have hge : 8 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 19 ∈ P
  · exact node_53 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 19
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 19 := by omega
            subst this
            simp)
  · exact node_54 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 19
          · exact hJ p hp h
          · have : p = 19 := by omega
            subst this
            exact absurd hp hc)

set_option maxHeartbeats 1000000 in
theorem node_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1)
    (hIP : ∀ p ∈ ({3, 79, 157, 313} : Finset ℕ), p ∈ P)
    (hI : ∀ p ∈ P, p < 3 → p ∈ ({3, 79, 157, 313} : Finset ℕ)) : False := by
  obtain ⟨S1, -, S3, -, -, S6, -, -⟩ := facts hP hK54 E
  obtain ⟨-, h3, -, -, -, h313⟩ := core5 hP E hodd
  have hJ : ∀ p ∈ P, p < 7 → p ∈ ({3, 79, 157, 313} : Finset ℕ) := by
    intro p hp hlt
    by_cases hpt : p < 3
    · exact hI p hp hpt
    have hge : 3 ≤ p := by omega
    have hpp := (hP p hp).1
    have hp3 := h3 p hp
    interval_cases p <;> first | (simp; done) | omega | (norm_num at hpp; done) | contradiction
  by_cases hc : 7 ∈ P
  · exact node_1 hP hP5 E hm hodd
      (by intro p hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> first | exact hc | (apply hIP; simp))
      (by intro p hp hlt
          by_cases h : p < 7
          · have := hJ p hp h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            omega
          · have : p = 7 := by omega
            subst this
            simp)
  · exact node_52 hP hP5 E hm hodd hIP
      (by intro p hp hlt
          by_cases h : p < 7
          · exact hJ p hp h
          · have : p = 7 := by omega
            subst this
            exact absurd hp hc)

theorem odd_core {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hP5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 4 * ∏ p ∈ P, p)
    (hm : 13 ≤ m) (hodd : m % 2 = 1) : False := by
  obtain ⟨g3, -, g313, g157, g79, -⟩ := core5 hP E hodd
  exact node_0 hP hP5 E hm hodd
    (by intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> assumption)
    (by intro p hp hlt
        have h1 := (hP p hp).1.two_le
        have h2 := (hP p hp).2
        omega)

theorem m_one {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ 1 + 1) * (1 + 5 ^ 4) * ∏ p ∈ P, (p + 1) = 2 ^ (1 + 1) * 5 ^ 4 * ∏ p ∈ P, p) :
    False := by
  obtain ⟨g3, -, g313, g157, g79, -⟩ := core5 hP E (by norm_num)
  have hA : ({3, 79, 157, 313} : Finset ℕ) ⊆ P := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have h1 := Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) hA
  have h2 : 2 ^ 5 ∣ ∏ p ∈ ({3, 79, 157, 313} : Finset ℕ), (p + 1) := by decide
  have h3 : 2 ^ 5 ∣ 2 ^ (1 + 1) * 5 ^ 4 * ∏ p ∈ P, p := by
    rw [← E]
    exact (h2.trans h1).mul_left _
  have e : 2 ^ (1 + 1) * 5 ^ 4 * ∏ p ∈ P, p = 2 ^ 2 * (5 ^ 4 * ∏ p ∈ P, p) := by ring
  rw [e, show (2 : ℕ) ^ 5 = 2 ^ 2 * 8 by norm_num] at h3
  have h4 : 8 ∣ 5 ^ 4 * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  have h5 : 2 ∣ ∏ p ∈ P, p := by
    have h6 : 2 ∣ 5 ^ 4 * ∏ p ∈ P, p := (by norm_num : (2 : ℕ) ∣ 8).trans h4
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h6 with h | h
    · norm_num at h
    · exact h
  obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h5
  exact (hP p hp).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP p hp).1).mp h2p).symm

theorem five_four_two_adic_even {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) (he : n.factorization 5 = 4) :
    Even (padicValNat 2 n) := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [he] at E
  have hP5 : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) := by simp
  rw [← Nat.factorization_def n Nat.prime_two, Nat.even_iff]
  by_contra hodd
  have hodd' : n.factorization 2 % 2 = 1 := by omega
  have D : ∀ e0 : ℕ, n.factorization 2 % (2 * e0) = e0 → 1 + 2 ^ e0 ∣ 2 ^ n.factorization 2 + 1 :=
    fun e0 he0 => by
      have := one_add_pow_dvd_of_odd_mul (z := 2) he0
      rwa [add_comm 1 (2 ^ n.factorization 2)] at this
  have c3 : n.factorization 2 % 6 ≠ 3 := fun hr =>
    okill3 hP (by norm_num) E (by norm_num) (D 3 (by omega))
  have c5 : n.factorization 2 % 6 ≠ 5 := fun hr =>
    okill_mod3 hP (by norm_num) E (by norm_num) (Or.inr (five_not_dvd_of_odd hodd')) hr
  have c7 : n.factorization 2 % 14 ≠ 7 := fun hr =>
    okill7 hP (by norm_num) E (by norm_num) (by norm_num) (by norm_num) (D 7 (by omega))
  rcases lt_or_ge (n.factorization 2) 13 with hlt | hge
  · have h1 : n.factorization 2 = 1 := by omega
    rw [h1] at E
    exact m_one hP E
  · exact odd_core hP hP5 E hge hodd'

theorem hK5 (e : ℕ) : ∀ c : ℕ, c.Prime → c ∣ 5 ^ e → c ∈ ({5} : Finset ℕ) := fun c hc h =>
  Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hc Nat.prime_five).mp (hc.dvd_of_dvd_pow h))

theorem lhs_dvd {m e R : ℕ} {P F : Finset ℕ}
    (hR : R ∣ 2 ^ m + 1) (hF : F ⊆ P) :
    R * (1 + 5 ^ e) * ∏ p ∈ F, (p + 1) ∣ (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) :=
  mul_dvd_mul (mul_dvd_mul hR dvd_rfl) (Finset.prod_dvd_prod_of_subset _ _ _ hF)

theorem kill_sq {m e R c : ℕ} {P F : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hR : R ∣ 2 ^ m + 1) (hF : F ⊆ P) (hc : c.Prime) (hc2 : c ≠ 2) (hc5 : c ≠ 5)
    (h : c * c ∣ R * (1 + 5 ^ e) * ∏ p ∈ F, (p + 1)) : False :=
  S_sq hP (hK5 e) E hc hc2 (fun h' => hc5 (Finset.mem_singleton.mp h')) (h.trans (lhs_dvd hR hF))

theorem kill_v5 {m e R : ℕ} {P F : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p)
    (hR : R ∣ 2 ^ m + 1) (hF : F ⊆ P)
    (h : 5 ^ (e + 1) ∣ R * (1 + 5 ^ e) * ∏ p ∈ F, (p + 1)) : False := by
  have h1 := h.trans (lhs_dvd hR hF)
  rw [E] at h1
  have e1 : 2 ^ (m + 1) * 5 ^ e * ∏ p ∈ P, p = 5 ^ e * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
  rw [e1, pow_succ] at h1
  have h2 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h2 with h3 | h3
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
      (Nat.prime_five.dvd_of_dvd_pow h3)
    norm_num at this
  · obtain ⟨p, hp, h4⟩ := (Prime.dvd_finsetProd_iff Nat.prime_five.prime _).mp h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five (hP p hp).1).mp h4
    exact h5 (this ▸ hp)

theorem setup {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) :
    (∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)), p.Prime ∧ p ≠ 2) ∧
    5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) ∧
    (2 ^ padicValNat 2 n + 1) * (1 + 5 ^ n.factorization 5) *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)), (p + 1) =
      2 ^ (padicValNat 2 n + 1) * 5 ^ n.factorization 5 *
        ∏ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)), p := by
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [← Nat.factorization_def n Nat.prime_two]
  exact ⟨hP, by simp, E⟩

theorem mod_of_dvd_odd {d m : ℕ} (hd : d ∣ m) (hm : m % 2 = 1) : m % (2 * d) = d := by
  obtain ⟨k, rfl⟩ := hd
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    have : d * (j + j) = 2 * (d * j) := by ring
    omega
  · have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0; simp at hm
      · exact h0
    rw [show d * (2 * j + 1) = d + 2 * d * j by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

theorem mod_of_dvd_two_mod_four {d m : ℕ} (hd : d ∣ m) (hd2 : d % 2 = 1) (hm : m % 4 = 2) :
    m % (2 * (2 * d)) = 2 * d := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k % 4 = 2 := by
    have h1 := Nat.mul_mod d k 4
    have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
    have hk4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rcases hd4 with h | h <;> interval_cases hkk : k % 4 <;> simp_all
  have hd0 : 0 < d := by omega
  have hk' : k = 4 * (k / 4) + 2 := by omega
  rw [hk', show d * (4 * (k / 4) + 2) = 2 * d + 2 * (2 * d) * (k / 4) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem e2_class_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 3 ∣ 2 ^ m + 1) : False := by
  exact kill_sq hP E hD (F := ∅) (Finset.empty_subset P) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 5 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 5).trans hD)
  have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (by simp) ((by norm_num : 11 ∣ 1 + 2 ^ 5).trans hD)
  exact kill_sq hP E hD (F := {3, 11}) (by simp [Finset.insert_subset_iff, g3, g11]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 7 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 7).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (by simp) ((by norm_num : 43 ∣ 1 + 2 ^ 7).trans hD)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (by simp) 43 g43 (by norm_num)
  exact kill_sq hP E hD (F := {3, 13, 7, 43, 11}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g43, g11]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 11 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 11).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (by simp) ((by norm_num : 683 ∣ 1 + 2 ^ 11).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 683}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g683]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_13 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 13 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 13).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (by simp) ((by norm_num : 2731 ∣ 1 + 2 ^ 13).trans hD)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (by simp) 2731 g2731 (by norm_num)
  exact kill_sq hP E hD (F := {3, 13, 7, 2731, 683}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g2731, g683]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 17 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 17).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (by simp) ((by norm_num : 43691 ∣ 1 + 2 ^ 17).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 43691}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g43691]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 19 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 19).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (by simp) ((by norm_num : 174763 ∣ 1 + 2 ^ 19).trans hD)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (by simp) 174763 g174763 (by norm_num)
  exact kill_sq hP E hD (F := {3, 13, 7, 174763, 43691}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g174763, g43691]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 23 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 23).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (by simp) ((by norm_num : 2796203 ∣ 1 + 2 ^ 23).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 2796203}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g2796203]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_29 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 29 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 29).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g59 : 59 ∈ P := S2 59 (by norm_num) (by norm_num) (by simp) ((by norm_num : 59 ∣ 1 + 2 ^ 29).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 59}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g59]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

set_option maxRecDepth 100000 in
theorem e2_class_31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 31 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 31).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g715827883 : 715827883 ∈ P := S2 715827883 (by norm_num) (by norm_num) (by simp) ((by norm_num : 715827883 ∣ 1 + 2 ^ 31).trans hD)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (by simp) 715827883 g715827883 (by norm_num)
  exact kill_sq hP E hD (F := {3, 13, 7, 715827883, 59}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g715827883, g59]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_37 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 37 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 37).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g1777 : 1777 ∈ P := S2 1777 (by norm_num) (by norm_num) (by simp) ((by norm_num : 1777 ∣ 1 + 2 ^ 37).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 1777}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g1777]) (c := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_41 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 41 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g3 : 3 ∈ P := S2 3 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3 ∣ 1 + 2 ^ 41).trans hD)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g83 : 83 ∈ P := S2 83 (by norm_num) (by norm_num) (by simp) ((by norm_num : 83 ∣ 1 + 2 ^ 41).trans hD)
  exact kill_sq hP E hD (F := {3, 13, 7, 83}) (by simp [Finset.insert_subset_iff, g3, g13, g7, g83]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 6 ∣ 2 ^ m + 1) : False := by
  exact kill_sq hP E hD (F := ∅) (Finset.empty_subset P) (c := 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_10 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 10 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g41 : 41 ∈ P := S2 41 (by norm_num) (by norm_num) (by simp) ((by norm_num : 41 ∣ 1 + 2 ^ 10).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 41}) (by simp [Finset.insert_subset_iff, g13, g7, g41]) (c := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_14 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 14 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g29 : 29 ∈ P := S2 29 (by norm_num) (by norm_num) (by simp) ((by norm_num : 29 ∣ 1 + 2 ^ 14).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 29 g29 (by norm_num)
  have g113 : 113 ∈ P := S2 113 (by norm_num) (by norm_num) (by simp) ((by norm_num : 113 ∣ 1 + 2 ^ 14).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 29, 3, 113}) (by simp [Finset.insert_subset_iff, g13, g7, g29, g3, g113]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_22 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 22 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g397 : 397 ∈ P := S2 397 (by norm_num) (by norm_num) (by simp) ((by norm_num : 397 ∣ 1 + 2 ^ 22).trans hD)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (by simp) 397 g397 (by norm_num)
  exact kill_v5 hP h5 E hD (F := {13, 7, 397, 199}) (by simp [Finset.insert_subset_iff, g13, g7, g397, g199]) (by norm_num)

theorem e2_class_26 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 26 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g53 : 53 ∈ P := S2 53 (by norm_num) (by norm_num) (by simp) ((by norm_num : 53 ∣ 1 + 2 ^ 26).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 53}) (by simp [Finset.insert_subset_iff, g13, g7, g53]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_34 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 34 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g137 : 137 ∈ P := S2 137 (by norm_num) (by norm_num) (by simp) ((by norm_num : 137 ∣ 1 + 2 ^ 34).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 137 g137 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (by simp) 137 g137 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 137, 3, 23}) (by simp [Finset.insert_subset_iff, g13, g7, g137, g3, g23]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_38 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 38 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g229 : 229 ∈ P := S2 229 (by norm_num) (by norm_num) (by simp) ((by norm_num : 229 ∣ 1 + 2 ^ 38).trans hD)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (by simp) 229 g229 (by norm_num)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 23 g23 (by norm_num)
  have g457 : 457 ∈ P := S2 457 (by norm_num) (by norm_num) (by simp) ((by norm_num : 457 ∣ 1 + 2 ^ 38).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 229, 23, 3, 457}) (by simp [Finset.insert_subset_iff, g13, g7, g229, g23, g3, g457]) (c := 229) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_46 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 46 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g277 : 277 ∈ P := S2 277 (by norm_num) (by norm_num) (by simp) ((by norm_num : 277 ∣ 1 + 2 ^ 46).trans hD)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (by simp) 277 g277 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 277, 139}) (by simp [Finset.insert_subset_iff, g13, g7, g277, g139]) (c := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

set_option maxRecDepth 100000 in
theorem e2_class_58 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 58 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g107367629 : 107367629 ∈ P := S2 107367629 (by norm_num) (by norm_num) (by simp) ((by norm_num : 107367629 ∣ 1 + 2 ^ 58).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 107367629 g107367629 (by norm_num)
  have g421 : 421 ∈ P := S1 421 (by norm_num) (by norm_num) (by simp) 107367629 g107367629 (by norm_num)
  have g211 : 211 ∈ P := S1 211 (by norm_num) (by norm_num) (by simp) 421 g421 (by norm_num)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (by simp) 211 g211 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 107367629, 3, 421, 211, 53}) (by simp [Finset.insert_subset_iff, g13, g7, g107367629, g3, g421, g211, g53]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_62 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 62 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g5581 : 5581 ∈ P := S2 5581 (by norm_num) (by norm_num) (by simp) ((by norm_num : 5581 ∣ 1 + 2 ^ 62).trans hD)
  have g2791 : 2791 ∈ P := S1 2791 (by norm_num) (by norm_num) (by simp) 5581 g5581 (by norm_num)
  have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (by simp) 2791 g2791 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 5581, 2791, 349}) (by simp [Finset.insert_subset_iff, g13, g7, g5581, g2791, g349]) (c := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_74 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 74 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g149 : 149 ∈ P := S2 149 (by norm_num) (by norm_num) (by simp) ((by norm_num : 149 ∣ 1 + 2 ^ 74).trans hD)
  exact kill_v5 hP h5 E hD (F := {13, 7, 149}) (by simp [Finset.insert_subset_iff, g13, g7, g149]) (by norm_num)

theorem e2_class_82 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 82 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g10169 : 10169 ∈ P := S2 10169 (by norm_num) (by norm_num) (by simp) ((by norm_num : 10169 ∣ 1 + 2 ^ 82).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 10169}) (by simp [Finset.insert_subset_iff, g13, g7, g10169]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_86 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 86 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g173 : 173 ∈ P := S2 173 (by norm_num) (by norm_num) (by simp) ((by norm_num : 173 ∣ 1 + 2 ^ 86).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 173 g173 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (by simp) 173 g173 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 173, 3, 29}) (by simp [Finset.insert_subset_iff, g13, g7, g173, g3, g29]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_94 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 94 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g3761 : 3761 ∈ P := S2 3761 (by norm_num) (by norm_num) (by simp) ((by norm_num : 3761 ∣ 1 + 2 ^ 94).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 3761}) (by simp [Finset.insert_subset_iff, g13, g7, g3761]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_106 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 106 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g15358129 : 15358129 ∈ P := S2 15358129 (by norm_num) (by norm_num) (by simp) ((by norm_num : 15358129 ∣ 1 + 2 ^ 106).trans hD)
  have g1535813 : 1535813 ∈ P := S1 1535813 (by norm_num) (by norm_num) (by simp) 15358129 g15358129 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 15358129, 1535813}) (by simp [Finset.insert_subset_iff, g13, g7, g15358129, g1535813]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_118 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 118 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g1181 : 1181 ∈ P := S2 1181 (by norm_num) (by norm_num) (by simp) ((by norm_num : 1181 ∣ 1 + 2 ^ 118).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 1181 g1181 (by norm_num)
  have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (by simp) 1181 g1181 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 1181, 3, 197}) (by simp [Finset.insert_subset_iff, g13, g7, g1181, g3, g197]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_122 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 122 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g733 : 733 ∈ P := S2 733 (by norm_num) (by norm_num) (by simp) ((by norm_num : 733 ∣ 1 + 2 ^ 122).trans hD)
  have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (by simp) 733 g733 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (by simp) 367 g367 (by norm_num)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 23 g23 (by norm_num)
  have g1709 : 1709 ∈ P := S2 1709 (by norm_num) (by norm_num) (by simp) ((by norm_num : 1709 ∣ 1 + 2 ^ 122).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 733, 367, 23, 3, 1709}) (by simp [Finset.insert_subset_iff, g13, g7, g733, g367, g23, g3, g1709]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_134 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 134 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g269 : 269 ∈ P := S2 269 (by norm_num) (by norm_num) (by simp) ((by norm_num : 269 ∣ 1 + 2 ^ 134).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 269}) (by simp [Finset.insert_subset_iff, g13, g7, g269]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_142 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 142 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g569 : 569 ∈ P := S2 569 (by norm_num) (by norm_num) (by simp) ((by norm_num : 569 ∣ 1 + 2 ^ 142).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 569 g569 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (by simp) 569 g569 (by norm_num)
  exact kill_v5 hP h5 E hD (F := {13, 7, 569, 3, 19}) (by simp [Finset.insert_subset_iff, g13, g7, g569, g3, g19]) (by norm_num)

theorem e2_class_146 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 146 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g293 : 293 ∈ P := S2 293 (by norm_num) (by norm_num) (by simp) ((by norm_num : 293 ∣ 1 + 2 ^ 146).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 293}) (by simp [Finset.insert_subset_iff, g13, g7, g293]) (c := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_158 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 158 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g317 : 317 ∈ P := S2 317 (by norm_num) (by norm_num) (by simp) ((by norm_num : 317 ∣ 1 + 2 ^ 158).trans hD)
  have g3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (by simp) 317 g317 (by norm_num)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (by simp) 317 g317 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 317, 3, 53}) (by simp [Finset.insert_subset_iff, g13, g7, g317, g3, g53]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_166 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 166 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g997 : 997 ∈ P := S2 997 (by norm_num) (by norm_num) (by simp) ((by norm_num : 997 ∣ 1 + 2 ^ 166).trans hD)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (by simp) 997 g997 (by norm_num)
  exact kill_v5 hP h5 E hD (F := {13, 7, 997, 499}) (by simp [Finset.insert_subset_iff, g13, g7, g997, g499]) (by norm_num)

theorem e2_class_178 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 178 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g1069 : 1069 ∈ P := S2 1069 (by norm_num) (by norm_num) (by simp) ((by norm_num : 1069 ∣ 1 + 2 ^ 178).trans hD)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (by simp) 1069 g1069 (by norm_num)
  exact kill_sq hP E hD (F := {13, 7, 1069, 107}) (by simp [Finset.insert_subset_iff, g13, g7, g1069, g107]) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem e2_class_194 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hD : 1 + 2 ^ 194 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (by simp) (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (by simp) 13 g13 (by norm_num)
  have g389 : 389 ∈ P := S2 389 (by norm_num) (by norm_num) (by simp) ((by norm_num : 389 ∣ 1 + 2 ^ 194).trans hD)
  exact kill_sq hP E hD (F := {13, 7, 389}) (by simp [Finset.insert_subset_iff, g13, g7, g389]) (c := 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem five_two_odd_prime_factor {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) (he : n.factorization 5 = 2)
    (hodd : padicValNat 2 n % 2 = 1) {d : ℕ} (hd : d.Prime) (hda : d ∣ padicValNat 2 n) :
    43 ≤ d := by
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  generalize padicValNat 2 n = m at E hodd hda
  by_contra hlt
  push_neg at hlt
  have hD : 1 + 2 ^ d ∣ 2 ^ m + 1 := by
    rw [add_comm (2 ^ m)]
    exact one_add_pow_dvd_of_odd_mul (mod_of_dvd_odd hda hodd)
  interval_cases d
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · omega
  · exact e2_class_3 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_5 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_7 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_11 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_13 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_17 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_19 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_23 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_29 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_31 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_37 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_41 hP h5 E hD
  · exact absurd hd (by norm_num)
set_option maxHeartbeats 4000000 in

theorem five_two_two_mod_four_prime_factor {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) (he : n.factorization 5 = 2)
    (h4 : padicValNat 2 n % 4 = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    (hda : d ∣ padicValNat 2 n) : 101 ≤ d := by
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  generalize padicValNat 2 n = m at E h4 hda
  by_contra hlt
  push_neg at hlt
  have hdo : d % 2 = 1 := by
    rcases hd.eq_two_or_odd with h' | h'
    · exact absurd h' hd2
    · exact h'
  have hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1 := by
    rw [add_comm (2 ^ m)]
    exact one_add_pow_dvd_of_odd_mul (mod_of_dvd_two_mod_four hda hdo h4)
  interval_cases d
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd rfl hd2
  · exact e2_class_6 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_10 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_14 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_22 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_26 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_34 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_38 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_46 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_58 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_62 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_74 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_82 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_86 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_94 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_106 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_118 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_122 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_134 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_142 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact e2_class_146 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_158 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_166 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_178 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact e2_class_194 hP h5 E hD
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
set_option maxHeartbeats 4000000 in

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨A1 + A2 + A3 + A4 + 127, fun n h z hz hz5 hz2100 hS hmod h5 h7 => ?_⟩
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23⟩ := H2_two_adic_classes h hz hz5 hz2100 hS
  have c24 := H2_two_adic_r14 h hz hz5 hz2100 hS
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := H2_two_adic_high h hz hz5 hz2100 hS
  rcases Nat.lt_or_ge (padicValNat 2 n) 128 with hsmall | hbig
  · omega
  rcases eq_or_ne z 5 with rfl | hz5'
  · obtain ⟨he, hD⟩ := h5 rfl
    have e6 := c6 (by norm_num)
    have e7 := c7 (by norm_num) (by norm_num) (by norm_num)
    have e15 := c15 (by norm_num)
    have R : ∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
        padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num <;> omega
    rcases he with he | he | he
    · have := h1 n h hS he (by omega)
        (fun hodd _ hd hda => five_two_odd_prime_factor h hS he hodd hd hda)
        (fun h4 _ hd hd2 hda => five_two_two_mod_four_prime_factor h hS he h4 hd hd2 hda)
        (c3 (Or.inr rfl)) R
      omega
    · have := h2 n h hS he (five_four_two_adic_even h hS he) hbig R
      omega
    · have := h3 n h hS he (hmod (by norm_num)) hD c0 (c3 (Or.inr rfl)) (c1 (by norm_num))
        (c2 (by norm_num) (by norm_num)) R
      omega
  · have hz7 : 7 ≤ z := by
      rcases Nat.lt_or_ge z 7 with hlt | hge
      · interval_cases z
        · exact absurd rfl hz5'
        · exact absurd hz (by norm_num)
      · exact hge
    have R : ∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
        padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num <;> omega
    have := h4 n h z hz hz7 hz2100 hS hmod h7 c0 c1 c2 (fun h' => c3 (Or.inl h')) (c4 hz5')
      (c5 hz5') c6 c7 c15 R
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1
