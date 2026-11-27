import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1 (3 is the only repeated odd prime, its
-- exponent e is 5, 7, 11, 13, 19 or at least 41, and e is no odd multiple of the 25 values D3) by
-- the exponent e, with the round-6 results built in.  Proving the three H proves the step.
--
-- Notation: n unitary perfect with 3 the only repeated odd prime (every other odd prime divides n
-- exactly once), e = n.factorization 3, a = padicValNat 2 n.  A number x is an ODD MULTIPLE of d
-- when x mod 2d = d; then 3^d + 1 divides 3^e + 1 (for x = e) and 2^d + 1 divides 2^a + 1 (for x = a).
--
-- PROVED BELOW (round 6, no hypothesis needed; the lemmas of this file, the rest is imported from
-- the parent reduction):
--   41 <= e <= 200 is impossible: if 2 <= e <= 200 then n = 90 or e is 5, 7, 11, 13 or 19
--     (three_exponent_cases_200).
--   e is no odd multiple of any d in D100, the 100 values listed in H3 (three_exponent_residues_200).
--   For every e, a is no odd multiple of any d in DA, the 69 values listed in H2
--     (three_two_adic_residues).
--   e = 5 or 7: a is also no odd multiple of 15, 16, 17, 19 (three_e57_weight_residues, a weight
--     bound on the path products of the simple primes).
--   e = 11: a is no odd multiple of 4, 16; e = 13: of 2, 4, 16; e = 19: of 2, 8, 16
--     (core3e11_two_adic_shape, core3e13_two_adic_shape, core3e19_two_adic_shape).
-- Method: the primes forced by 3^d + 1 or 2^d + 1 give some odd prime two sources in the balance
-- equation (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p, or a weight bound below 2; witness
-- primes above 4.3 * 10^7 are certified by the Lucas test.  n = 90 (a = 1) is absorbed into the bound.
--
-- H1 (OPEN): e = 5 or 7, a no odd multiple of DA and of 15, 16, 17, 19.
-- H2 (OPEN): e = 11, 13 or 19, a no odd multiple of DA nor of the e-specific values above.
-- H3 (OPEN): e > 200, e no odd multiple of D100, a no odd multiple of DA.
-- No known unitary perfect number satisfies the hypotheses of H1, H2 or H3 (90 has e = 2).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 5 or 7, and a no odd multiple of any d in DA or of
-- 15, 16, 17, 19.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 5 ∨ n.factorization 3 = 7) →
    (∀ d ∈ ({10, 12, 14, 15, 16, 17, 18, 19, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38,
        39, 45, 46, 48, 51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82,
        83, 85, 86, 91, 94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133,
        134, 141, 142, 143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 11, 13 or 19, a no odd multiple of any d in DA (the
-- set listed), and a no odd multiple of 4, 16 (e = 11), of 2, 4, 16 (e = 13), of 2, 8, 16 (e = 19).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    (n.factorization 3 = 11 ∨ n.factorization 3 = 13 ∨ n.factorization 3 = 19) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 11 → ∀ d ∈ ({4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 13 → ∀ d ∈ ({2, 4, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (n.factorization 3 = 19 → ∀ d ∈ ({2, 8, 16} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H3: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 above 200, e no odd multiple of any d in D100 (the first set),
-- and a no odd multiple of any d in DA (the second set).
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    200 < n.factorization 3 →
    (∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37,
        38, 39, 41, 43, 44, 46, 47, 49, 52, 53, 55, 57, 58, 59, 61, 62, 64, 65, 67, 68, 71, 73,
        74, 76, 77, 79, 82, 83, 86, 89, 91, 92, 94, 95, 97, 101, 103, 106, 107, 109, 113, 116,
        118, 121, 122, 124, 127, 128, 131, 133, 134, 137, 139, 142, 143, 146, 148, 149, 151, 157,
        158, 163, 164, 166, 167, 169, 172, 173, 178, 179, 181, 188, 191, 193, 194, 197, 199} : Finset ℕ),
      n.factorization 3 % (2 * d) ≠ d) →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Lemmas of round 6 (Erdos1052OpenCore6.lean), only those used below that the parent reduction does
-- not already provide.

theorem prime_270547105429567 : Nat.Prime 270547105429567 := by
  refine lucas_primality 270547105429567 (7 : ZMod 270547105429567) ?_ (fun q hq hd => ?_)
  · rw [show 270547105429567 - 1 = 270547105429566 from by norm_num]
    reduce_mod_char
  · have e : 270547105429567 - 1 = [2 ^ 1, 3 ^ 3, 7 ^ 1, 29 ^ 1, 41 ^ 1, 307 ^ 1, 1960789 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 2 = 135273552714783 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 135273552714783 = ((270547105429566 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 3 = 90182368476522 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 90182368476522 = ((270541875252965 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 7 = 38649586489938 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 38649586489938 = ((80157258026317 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 29 = 9329210532054 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 9329210532054 = ((88557896077116 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 41 = 6598709888526 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 6598709888526 = ((270547091080660 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 307 = 881260929738 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 881260929738 = ((95607930504701 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (270547105429567 - 1) / 1960789 = 137978694 from by norm_num]
      have h2 : (7 : ZMod 270547105429567) ^ 137978694 = ((111261893091100 : ℕ) : ZMod 270547105429567) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_82064241848634269407 : Nat.Prime 82064241848634269407 := by
  refine lucas_primality 82064241848634269407 (5 : ZMod 82064241848634269407) ?_ (fun q hq hd => ?_)
  · rw [show 82064241848634269407 - 1 = 82064241848634269406 from by norm_num]
    reduce_mod_char
  · have e : 82064241848634269407 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 2, 13 ^ 1, 43 ^ 1, 547 ^ 1, 1093 ^ 1, 2269 ^ 1, 368089 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 2 = 41032120924317134703 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 41032120924317134703 = ((82064241848634269406 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 3 = 27354747282878089802 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 27354747282878089802 = ((15690529804 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 7 = 11723463121233467058 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 11723463121233467058 = ((61823764431200552234 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 13 = 6312633988356482262 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 6312633988356482262 = ((31532669365773659493 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 43 = 1908470740665913242 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 1908470740665913242 = ((82064241838173916204 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 547 = 150026036286351498 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 150026036286351498 = ((15448144425154548508 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 1093 = 75081648534889542 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 75081648534889542 = ((6089947427447763611 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 2269 = 36167581246643574 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 36167581246643574 = ((73085596738274239313 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82064241848634269407 - 1) / 368089 = 222946738013454 from by norm_num]
      have h2 : (5 : ZMod 82064241848634269407) ^ 222946738013454 = ((70589833169166972125 : ℕ) : ZMod 82064241848634269407) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_857643277 : Nat.Prime 857643277 := by
  refine lucas_primality 857643277 (2 : ZMod 857643277) ?_ (fun q hq hd => ?_)
  · rw [show 857643277 - 1 = 857643276 from by norm_num]
    reduce_mod_char
  · have e : 857643277 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 2, 37 ^ 1, 79 ^ 1, 499 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 2 = 428821638 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 428821638 = ((857643276 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 3 = 285881092 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 285881092 = ((31474116 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 7 = 122520468 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 122520468 = ((4782969 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 37 = 23179548 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 23179548 = ((818376875 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 79 = 10856244 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 10856244 = ((822883834 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (857643277 - 1) / 499 = 1718724 from by norm_num]
      have h2 : (2 : ZMod 857643277) ^ 1718724 = ((664752073 : ℕ) : ZMod 857643277) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_428821639 : Nat.Prime 428821639 := by
  refine lucas_primality 428821639 (3 : ZMod 428821639) ?_ (fun q hq hd => ?_)
  · rw [show 428821639 - 1 = 428821638 from by norm_num]
    reduce_mod_char
  · have e : 428821639 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 2, 37 ^ 1, 79 ^ 1, 499 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 2 = 214410819 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 214410819 = ((428821638 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 3 = 142940546 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 142940546 = ((251432710 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 7 = 61260234 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 61260234 = ((116403606 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 37 = 11589774 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 11589774 = ((420947835 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 79 = 5428122 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 5428122 = ((360175623 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (428821639 - 1) / 499 = 859362 from by norm_num]
      have h2 : (3 : ZMod 428821639) ^ 859362 = ((129479544 : ℕ) : ZMod 428821639) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2093124281 : Nat.Prime 2093124281 := by
  refine lucas_primality 2093124281 (6 : ZMod 2093124281) ?_ (fun q hq hd => ?_)
  · rw [show 2093124281 - 1 = 2093124280 from by norm_num]
    reduce_mod_char
  · have e : 2093124281 - 1 = [2 ^ 3, 5 ^ 1, 13 ^ 1, 4025239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2093124281 - 1) / 2 = 1046562140 from by norm_num]
      have h2 : (6 : ZMod 2093124281) ^ 1046562140 = ((2093124280 : ℕ) : ZMod 2093124281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2093124281 - 1) / 5 = 418624856 from by norm_num]
      have h2 : (6 : ZMod 2093124281) ^ 418624856 = ((1214631782 : ℕ) : ZMod 2093124281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2093124281 - 1) / 13 = 161009560 from by norm_num]
      have h2 : (6 : ZMod 2093124281) ^ 161009560 = ((832982652 : ℕ) : ZMod 2093124281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2093124281 - 1) / 4025239 = 520 from by norm_num]
      have h2 : (6 : ZMod 2093124281) ^ 520 = ((558062302 : ℕ) : ZMod 2093124281) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_348854047 : Nat.Prime 348854047 := by
  refine lucas_primality 348854047 (3 : ZMod 348854047) ?_ (fun q hq hd => ?_)
  · rw [show 348854047 - 1 = 348854046 from by norm_num]
    reduce_mod_char
  · have e : 348854047 - 1 = [2 ^ 1, 3 ^ 1, 79 ^ 1, 735979 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (348854047 - 1) / 2 = 174427023 from by norm_num]
      have h2 : (3 : ZMod 348854047) ^ 174427023 = ((348854046 : ℕ) : ZMod 348854047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (348854047 - 1) / 3 = 116284682 from by norm_num]
      have h2 : (3 : ZMod 348854047) ^ 116284682 = ((271633256 : ℕ) : ZMod 348854047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (348854047 - 1) / 79 = 4415874 from by norm_num]
      have h2 : (3 : ZMod 348854047) ^ 4415874 = ((103828149 : ℕ) : ZMod 348854047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (348854047 - 1) / 735979 = 474 from by norm_num]
      have h2 : (3 : ZMod 348854047) ^ 474 = ((73979470 : ℕ) : ZMod 348854047) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_78719947 : Nat.Prime 78719947 := by
  refine lucas_primality 78719947 (2 : ZMod 78719947) ?_ (fun q hq hd => ?_)
  · rw [show 78719947 - 1 = 78719946 from by norm_num]
    reduce_mod_char
  · have e : 78719947 - 1 = [2 ^ 1, 3 ^ 1, 53 ^ 1, 247547 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78719947 - 1) / 2 = 39359973 from by norm_num]
      have h2 : (2 : ZMod 78719947) ^ 39359973 = ((78719946 : ℕ) : ZMod 78719947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78719947 - 1) / 3 = 26239982 from by norm_num]
      have h2 : (2 : ZMod 78719947) ^ 26239982 = ((76829495 : ℕ) : ZMod 78719947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78719947 - 1) / 53 = 1485282 from by norm_num]
      have h2 : (2 : ZMod 78719947) ^ 1485282 = ((9399748 : ℕ) : ZMod 78719947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78719947 - 1) / 247547 = 318 from by norm_num]
      have h2 : (2 : ZMod 78719947) ^ 318 = ((39017877 : ℕ) : ZMod 78719947) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_597046729 : Nat.Prime 597046729 := by
  refine lucas_primality 597046729 (7 : ZMod 597046729) ?_ (fun q hq hd => ?_)
  · rw [show 597046729 - 1 = 597046728 from by norm_num]
    reduce_mod_char
  · have e : 597046729 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 1, 1309313 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597046729 - 1) / 2 = 298523364 from by norm_num]
      have h2 : (7 : ZMod 597046729) ^ 298523364 = ((597046728 : ℕ) : ZMod 597046729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597046729 - 1) / 3 = 199015576 from by norm_num]
      have h2 : (7 : ZMod 597046729) ^ 199015576 = ((530458295 : ℕ) : ZMod 597046729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597046729 - 1) / 19 = 31423512 from by norm_num]
      have h2 : (7 : ZMod 597046729) ^ 31423512 = ((68547618 : ℕ) : ZMod 597046729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (597046729 - 1) / 1309313 = 456 from by norm_num]
      have h2 : (7 : ZMod 597046729) ^ 456 = ((219643320 : ℕ) : ZMod 597046729) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5970467291 : Nat.Prime 5970467291 := by
  refine lucas_primality 5970467291 (2 : ZMod 5970467291) ?_ (fun q hq hd => ?_)
  · rw [show 5970467291 - 1 = 5970467290 from by norm_num]
    reduce_mod_char
  · have e : 5970467291 - 1 = [2 ^ 1, 5 ^ 1, 597046729 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5970467291 - 1) / 2 = 2985233645 from by norm_num]
      have h2 : (2 : ZMod 5970467291) ^ 2985233645 = ((5970467290 : ℕ) : ZMod 5970467291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5970467291 - 1) / 5 = 1194093458 from by norm_num]
      have h2 : (2 : ZMod 5970467291) ^ 1194093458 = ((1764069450 : ℕ) : ZMod 5970467291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_597046729).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5970467291 - 1) / 597046729 = 10 from by norm_num]
      have h2 : (2 : ZMod 5970467291) ^ 10 = ((1024 : ℕ) : ZMod 5970467291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_226877757059 : Nat.Prime 226877757059 := by
  refine lucas_primality 226877757059 (2 : ZMod 226877757059) ?_ (fun q hq hd => ?_)
  · rw [show 226877757059 - 1 = 226877757058 from by norm_num]
    reduce_mod_char
  · have e : 226877757059 - 1 = [2 ^ 1, 19 ^ 1, 5970467291 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226877757059 - 1) / 2 = 113438878529 from by norm_num]
      have h2 : (2 : ZMod 226877757059) ^ 113438878529 = ((226877757058 : ℕ) : ZMod 226877757059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226877757059 - 1) / 19 = 11940934582 from by norm_num]
      have h2 : (2 : ZMod 226877757059) ^ 11940934582 = ((202101603194 : ℕ) : ZMod 226877757059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5970467291).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226877757059 - 1) / 5970467291 = 38 from by norm_num]
      have h2 : (2 : ZMod 226877757059) ^ 38 = ((48000149885 : ℕ) : ZMod 226877757059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1815022056473 : Nat.Prime 1815022056473 := by
  refine lucas_primality 1815022056473 (3 : ZMod 1815022056473) ?_ (fun q hq hd => ?_)
  · rw [show 1815022056473 - 1 = 1815022056472 from by norm_num]
    reduce_mod_char
  · have e : 1815022056473 - 1 = [2 ^ 3, 226877757059 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1815022056473 - 1) / 2 = 907511028236 from by norm_num]
      have h2 : (3 : ZMod 1815022056473) ^ 907511028236 = ((1815022056472 : ℕ) : ZMod 1815022056473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_226877757059).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1815022056473 - 1) / 226877757059 = 8 from by norm_num]
      have h2 : (3 : ZMod 1815022056473) ^ 8 = ((6561 : ℕ) : ZMod 1815022056473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_172514977 : Nat.Prime 172514977 := by
  refine lucas_primality 172514977 (7 : ZMod 172514977) ?_ (fun q hq hd => ?_)
  · rw [show 172514977 - 1 = 172514976 from by norm_num]
    reduce_mod_char
  · have e : 172514977 - 1 = [2 ^ 5, 3 ^ 1, 1797031 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172514977 - 1) / 2 = 86257488 from by norm_num]
      have h2 : (7 : ZMod 172514977) ^ 86257488 = ((172514976 : ℕ) : ZMod 172514977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172514977 - 1) / 3 = 57504992 from by norm_num]
      have h2 : (7 : ZMod 172514977) ^ 57504992 = ((47291971 : ℕ) : ZMod 172514977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (172514977 - 1) / 1797031 = 96 from by norm_num]
      have h2 : (7 : ZMod 172514977) ^ 96 = ((99437913 : ℕ) : ZMod 172514977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1108439448677340328268341 : Nat.Prime 1108439448677340328268341 := by
  refine lucas_primality 1108439448677340328268341 (7 : ZMod 1108439448677340328268341) ?_ (fun q hq hd => ?_)
  · rw [show 1108439448677340328268341 - 1 = 1108439448677340328268340 from by norm_num]
    reduce_mod_char
  · have e : 1108439448677340328268341 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 59 ^ 1, 172514977 ^ 1, 1815022056473 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 2 = 554219724338670164134170 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 554219724338670164134170 = ((1108439448677340328268340 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 3 = 369479816225780109422780 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 369479816225780109422780 = ((102945566047324 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 5 = 221687889735468065653668 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 221687889735468065653668 = ((899047937073127793710184 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 59 = 18787109299615937767260 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 18787109299615937767260 = ((1108439448677340328268338 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_172514977).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 172514977 = 6425178079914420 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 6425178079914420 = ((224376933890117903277432 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1815022056473).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1108439448677340328268341 - 1) / 1815022056473 = 610703018580 from by norm_num]
      have h2 : (7 : ZMod 1108439448677340328268341) ^ 610703018580 = ((947241778538990089345120 : ℕ) : ZMod 1108439448677340328268341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_85907447 : Nat.Prime 85907447 := by
  refine lucas_primality 85907447 (5 : ZMod 85907447) ?_ (fun q hq hd => ?_)
  · rw [show 85907447 - 1 = 85907446 from by norm_num]
    reduce_mod_char
  · have e : 85907447 - 1 = [2 ^ 1, 47 ^ 1, 443 ^ 1, 2063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85907447 - 1) / 2 = 42953723 from by norm_num]
      have h2 : (5 : ZMod 85907447) ^ 42953723 = ((85907446 : ℕ) : ZMod 85907447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85907447 - 1) / 47 = 1827818 from by norm_num]
      have h2 : (5 : ZMod 85907447) ^ 1827818 = ((18324396 : ℕ) : ZMod 85907447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85907447 - 1) / 443 = 193922 from by norm_num]
      have h2 : (5 : ZMod 85907447) ^ 193922 = ((17687642 : ℕ) : ZMod 85907447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85907447 - 1) / 2063 = 41642 from by norm_num]
      have h2 : (5 : ZMod 85907447) ^ 41642 = ((28519025 : ℕ) : ZMod 85907447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_76801257619 : Nat.Prime 76801257619 := by
  refine lucas_primality 76801257619 (2 : ZMod 76801257619) ?_ (fun q hq hd => ?_)
  · rw [show 76801257619 - 1 = 76801257618 from by norm_num]
    reduce_mod_char
  · have e : 76801257619 - 1 = [2 ^ 1, 3 ^ 1, 149 ^ 1, 85907447 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76801257619 - 1) / 2 = 38400628809 from by norm_num]
      have h2 : (2 : ZMod 76801257619) ^ 38400628809 = ((76801257618 : ℕ) : ZMod 76801257619) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76801257619 - 1) / 3 = 25600419206 from by norm_num]
      have h2 : (2 : ZMod 76801257619) ^ 25600419206 = ((39312876257 : ℕ) : ZMod 76801257619) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76801257619 - 1) / 149 = 515444682 from by norm_num]
      have h2 : (2 : ZMod 76801257619) ^ 515444682 = ((58536103313 : ℕ) : ZMod 76801257619) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_85907447).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (76801257619 - 1) / 85907447 = 894 from by norm_num]
      have h2 : (2 : ZMod 76801257619) ^ 894 = ((71798653939 : ℕ) : ZMod 76801257619) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_135477418439917 : Nat.Prime 135477418439917 := by
  refine lucas_primality 135477418439917 (2 : ZMod 135477418439917) ?_ (fun q hq hd => ?_)
  · rw [show 135477418439917 - 1 = 135477418439916 from by norm_num]
    reduce_mod_char
  · have e : 135477418439917 - 1 = [2 ^ 2, 3 ^ 2, 7 ^ 2, 76801257619 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (135477418439917 - 1) / 2 = 67738709219958 from by norm_num]
      have h2 : (2 : ZMod 135477418439917) ^ 67738709219958 = ((135477418439916 : ℕ) : ZMod 135477418439917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (135477418439917 - 1) / 3 = 45159139479972 from by norm_num]
      have h2 : (2 : ZMod 135477418439917) ^ 45159139479972 = ((69924369101110 : ℕ) : ZMod 135477418439917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (135477418439917 - 1) / 7 = 19353916919988 from by norm_num]
      have h2 : (2 : ZMod 135477418439917) ^ 19353916919988 = ((67049073845767 : ℕ) : ZMod 135477418439917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_76801257619).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (135477418439917 - 1) / 76801257619 = 1764 from by norm_num]
      have h2 : (2 : ZMod 135477418439917) ^ 1764 = ((69195707104838 : ℕ) : ZMod 135477418439917) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_582372997 : Nat.Prime 582372997 := by
  refine lucas_primality 582372997 (11 : ZMod 582372997) ?_ (fun q hq hd => ?_)
  · rw [show 582372997 - 1 = 582372996 from by norm_num]
    reduce_mod_char
  · have e : 582372997 - 1 = [2 ^ 2, 3 ^ 1, 3517 ^ 1, 13799 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582372997 - 1) / 2 = 291186498 from by norm_num]
      have h2 : (11 : ZMod 582372997) ^ 291186498 = ((582372996 : ℕ) : ZMod 582372997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582372997 - 1) / 3 = 194124332 from by norm_num]
      have h2 : (11 : ZMod 582372997) ^ 194124332 = ((164549020 : ℕ) : ZMod 582372997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582372997 - 1) / 3517 = 165588 from by norm_num]
      have h2 : (11 : ZMod 582372997) ^ 165588 = ((424827666 : ℕ) : ZMod 582372997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (582372997 - 1) / 13799 = 42204 from by norm_num]
      have h2 : (11 : ZMod 582372997) ^ 42204 = ((119852745 : ℕ) : ZMod 582372997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86630432442539925437931403 : Nat.Prime 86630432442539925437931403 := by
  refine lucas_primality 86630432442539925437931403 (5 : ZMod 86630432442539925437931403) ?_ (fun q hq hd => ?_)
  · rw [show 86630432442539925437931403 - 1 = 86630432442539925437931402 from by norm_num]
    reduce_mod_char
  · have e : 86630432442539925437931403 - 1 = [2 ^ 1, 3 ^ 2, 61 ^ 1, 582372997 ^ 1, 135477418439917 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86630432442539925437931403 - 1) / 2 = 43315216221269962718965701 from by norm_num]
      have h2 : (5 : ZMod 86630432442539925437931403) ^ 43315216221269962718965701 = ((86630432442539925437931402 : ℕ) : ZMod 86630432442539925437931403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86630432442539925437931403 - 1) / 3 = 28876810814179975145977134 from by norm_num]
      have h2 : (5 : ZMod 86630432442539925437931403) ^ 28876810814179975145977134 = ((86630432442231088739789429 : ℕ) : ZMod 86630432442539925437931403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86630432442539925437931403 - 1) / 61 = 1420171023648195498982482 from by norm_num]
      have h2 : (5 : ZMod 86630432442539925437931403) ^ 1420171023648195498982482 = ((58149737003040059690390169 : ℕ) : ZMod 86630432442539925437931403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_582372997).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86630432442539925437931403 - 1) / 582372997 = 148754205447028866 from by norm_num]
      have h2 : (5 : ZMod 86630432442539925437931403) ^ 148754205447028866 = ((55057547468083542414421686 : ℕ) : ZMod 86630432442539925437931403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_135477418439917).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86630432442539925437931403 - 1) / 135477418439917 = 639445550706 from by norm_num]
      have h2 : (5 : ZMod 86630432442539925437931403) ^ 639445550706 = ((61484199561994667359603394 : ℕ) : ZMod 86630432442539925437931403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1403808961 : Nat.Prime 1403808961 := by
  refine lucas_primality 1403808961 (17 : ZMod 1403808961) ?_ (fun q hq hd => ?_)
  · rw [show 1403808961 - 1 = 1403808960 from by norm_num]
    reduce_mod_char
  · have e : 1403808961 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 31 ^ 1, 43 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 2 = 701904480 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 701904480 = ((1403808960 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 3 = 467936320 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 467936320 = ((1377307878 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 5 = 280761792 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 280761792 = ((1072566639 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 31 = 45284160 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 45284160 = ((266630922 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 43 = 32646720 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 32646720 = ((1056622325 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1403808961 - 1) / 1097 = 1279680 from by norm_num]
      have h2 : (17 : ZMod 1403808961) ^ 1279680 = ((228703647 : ℕ) : ZMod 1403808961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_701904481 : Nat.Prime 701904481 := by
  refine lucas_primality 701904481 (7 : ZMod 701904481) ?_ (fun q hq hd => ?_)
  · rw [show 701904481 - 1 = 701904480 from by norm_num]
    reduce_mod_char
  · have e : 701904481 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 31 ^ 1, 43 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 2 = 350952240 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 350952240 = ((701904480 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 3 = 233968160 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 233968160 = ((424872191 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 5 = 140380896 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 140380896 = ((145278333 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 31 = 22642080 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 22642080 = ((115114690 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 43 = 16323360 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 16323360 = ((491198430 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (701904481 - 1) / 1097 = 639840 from by norm_num]
      have h2 : (7 : ZMod 701904481) ^ 639840 = ((342087531 : ℕ) : ZMod 701904481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_350952241 : Nat.Prime 350952241 := by
  refine lucas_primality 350952241 (14 : ZMod 350952241) ?_ (fun q hq hd => ?_)
  · rw [show 350952241 - 1 = 350952240 from by norm_num]
    reduce_mod_char
  · have e : 350952241 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 31 ^ 1, 43 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 2 = 175476120 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 175476120 = ((350952240 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 3 = 116984080 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 116984080 = ((1281720 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 5 = 70190448 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 70190448 = ((115937932 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 31 = 11321040 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 11321040 = ((298359213 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 43 = 8161680 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 8161680 = ((194702156 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (350952241 - 1) / 1097 = 319920 from by norm_num]
      have h2 : (14 : ZMod 350952241) ^ 319920 = ((345748556 : ℕ) : ZMod 350952241) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_175476121 : Nat.Prime 175476121 := by
  refine lucas_primality 175476121 (13 : ZMod 175476121) ?_ (fun q hq hd => ?_)
  · rw [show 175476121 - 1 = 175476120 from by norm_num]
    reduce_mod_char
  · have e : 175476121 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 31 ^ 1, 43 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 2 = 87738060 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 87738060 = ((175476120 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 3 = 58492040 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 58492040 = ((44569457 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 5 = 35095224 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 35095224 = ((95086275 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 31 = 5660520 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 5660520 = ((9805819 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 43 = 4080840 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 4080840 = ((93739099 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (175476121 - 1) / 1097 = 159960 from by norm_num]
      have h2 : (13 : ZMod 175476121) ^ 159960 = ((32349430 : ℕ) : ZMod 175476121) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1716841910146256242328924544641 : Nat.Prime 1716841910146256242328924544641 := by
  refine lucas_primality 1716841910146256242328924544641 (6 : ZMod 1716841910146256242328924544641) ?_ (fun q hq hd => ?_)
  · rw [show 1716841910146256242328924544641 - 1 = 1716841910146256242328924544640 from by norm_num]
    reduce_mod_char
  · have e : 1716841910146256242328924544641 - 1 = [2 ^ 7, 5 ^ 1, 17 ^ 1, 41 ^ 1, 193 ^ 1, 21523361 ^ 1, 926510094425921 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 2 = 858420955073128121164462272320 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 858420955073128121164462272320 = ((1716841910146256242328924544640 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 5 = 343368382029251248465784908928 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 343368382029251248465784908928 = ((231360542901637734452803223211 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 17 = 100990700596838602489936737920 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 100990700596838602489936737920 = ((847470467640508246167574957901 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 41 = 41874192930396493715339623040 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 41874192930396493715339623040 = ((833958094152435299132439167871 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 193 = 8895553938581638561289764480 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 8895553938581638561289764480 = ((1266132576511639632944893675844 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 21523361 = 79766441223852364058240 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 79766441223852364058240 = ((389460605339339089213337173213 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_926510094425921).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1716841910146256242328924544641 - 1) / 926510094425921 = 1853020188851840 from by norm_num]
      have h2 : (6 : ZMod 1716841910146256242328924544641) ^ 1853020188851840 = ((1310635564311658263532632555889 : ℕ) : ZMod 1716841910146256242328924544641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_105919308797935444986721 : Nat.Prime 105919308797935444986721 := by
  refine lucas_primality 105919308797935444986721 (11 : ZMod 105919308797935444986721) ?_ (fun q hq hd => ?_)
  · rw [show 105919308797935444986721 - 1 = 105919308797935444986720 from by norm_num]
    reduce_mod_char
  · have e : 105919308797935444986721 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 73 ^ 1, 277 ^ 1, 379 ^ 1, 683 ^ 1, 3187 ^ 1, 145361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 2 = 52959654398967722493360 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 52959654398967722493360 = ((105919308797935444986720 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 3 = 35306436265978481662240 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 35306436265978481662240 = ((2779530283277761 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 5 = 21183861759587088997344 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 21183861759587088997344 = ((2541865828329 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 7 = 15131329828276492140960 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 15131329828276492140960 = ((88261204394359795951197 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 13 = 8147639138302726537440 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 8147639138302726537440 = ((102964996091384611288078 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 73 = 1450949435588156780640 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 1450949435588156780640 = ((95332788877156429662013 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 277 = 382380176165831931360 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 382380176165831931360 = ((104104079993347480149761 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 379 = 279470471762362651680 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 279470471762362651680 = ((71179667822270177199813 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 683 = 155079515077504311840 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 155079515077504311840 = ((64175463057391539318096 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 3187 = 33234800375881846560 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 33234800375881846560 = ((80661122540255988102767 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105919308797935444986721 - 1) / 145361 = 728663869937159520 from by norm_num]
      have h2 : (11 : ZMod 105919308797935444986721) ^ 728663869937159520 = ((9374998767829688588336 : ℕ) : ZMod 105919308797935444986721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52959654398967722493361 : Nat.Prime 52959654398967722493361 := by
  refine lucas_primality 52959654398967722493361 (11 : ZMod 52959654398967722493361) ?_ (fun q hq hd => ?_)
  · rw [show 52959654398967722493361 - 1 = 52959654398967722493360 from by norm_num]
    reduce_mod_char
  · have e : 52959654398967722493361 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 1, 73 ^ 1, 277 ^ 1, 379 ^ 1, 683 ^ 1, 3187 ^ 1, 145361 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 2 = 26479827199483861246680 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 26479827199483861246680 = ((52959654398967722493360 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 3 = 17653218132989240831120 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 17653218132989240831120 = ((44975982554255621281798 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 5 = 10591930879793544498672 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 10591930879793544498672 = ((52534762050770992033699 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 7 = 7565664914138246070480 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 7565664914138246070480 = ((11451117582928057470074 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 13 = 4073819569151363268720 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 4073819569151363268720 = ((28753984598859460894463 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 73 = 725474717794078390320 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 725474717794078390320 = ((27540588871580057538150 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 277 = 191190088082915965680 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 191190088082915965680 = ((52742517834717055814854 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 379 = 139735235881181325840 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 139735235881181325840 = ((42735702142284321928593 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 683 = 77539757538752155920 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 77539757538752155920 = ((40268201724398371277268 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 3187 = 16617400187940923280 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 16617400187940923280 = ((22507224404767740797550 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52959654398967722493361 - 1) / 145361 = 364331934968579760 from by norm_num]
      have h2 : (11 : ZMod 52959654398967722493361) ^ 364331934968579760 = ((42504834306415356205966 : ℕ) : ZMod 52959654398967722493361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43968887 : Nat.Prime 43968887 := by
  refine lucas_primality 43968887 (5 : ZMod 43968887) ?_ (fun q hq hd => ?_)
  · rw [show 43968887 - 1 = 43968886 from by norm_num]
    reduce_mod_char
  · have e : 43968887 - 1 = [2 ^ 1, 13 ^ 1, 499 ^ 1, 3389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43968887 - 1) / 2 = 21984443 from by norm_num]
      have h2 : (5 : ZMod 43968887) ^ 21984443 = ((43968886 : ℕ) : ZMod 43968887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43968887 - 1) / 13 = 3382222 from by norm_num]
      have h2 : (5 : ZMod 43968887) ^ 3382222 = ((11619215 : ℕ) : ZMod 43968887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43968887 - 1) / 499 = 88114 from by norm_num]
      have h2 : (5 : ZMod 43968887) ^ 88114 = ((27645646 : ℕ) : ZMod 43968887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43968887 - 1) / 3389 = 12974 from by norm_num]
      have h2 : (5 : ZMod 43968887) ^ 12974 = ((35020893 : ℕ) : ZMod 43968887) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6458150122561 : Nat.Prime 6458150122561 := by
  refine lucas_primality 6458150122561 (13 : ZMod 6458150122561) ?_ (fun q hq hd => ?_)
  · rw [show 6458150122561 - 1 = 6458150122560 from by norm_num]
    reduce_mod_char
  · have e : 6458150122561 - 1 = [2 ^ 6, 3 ^ 3, 5 ^ 1, 17 ^ 1, 43968887 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6458150122561 - 1) / 2 = 3229075061280 from by norm_num]
      have h2 : (13 : ZMod 6458150122561) ^ 3229075061280 = ((6458150122560 : ℕ) : ZMod 6458150122561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6458150122561 - 1) / 3 = 2152716707520 from by norm_num]
      have h2 : (13 : ZMod 6458150122561) ^ 2152716707520 = ((658899146639 : ℕ) : ZMod 6458150122561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6458150122561 - 1) / 5 = 1291630024512 from by norm_num]
      have h2 : (13 : ZMod 6458150122561) ^ 1291630024512 = ((5044968100385 : ℕ) : ZMod 6458150122561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6458150122561 - 1) / 17 = 379891183680 from by norm_num]
      have h2 : (13 : ZMod 6458150122561) ^ 379891183680 = ((5633286564764 : ℕ) : ZMod 6458150122561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_43968887).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6458150122561 - 1) / 43968887 = 146880 from by norm_num]
      have h2 : (13 : ZMod 6458150122561) ^ 146880 = ((5073981674128 : ℕ) : ZMod 6458150122561) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_75094768867 : Nat.Prime 75094768867 := by
  refine lucas_primality 75094768867 (2 : ZMod 75094768867) ?_ (fun q hq hd => ?_)
  · rw [show 75094768867 - 1 = 75094768866 from by norm_num]
    reduce_mod_char
  · have e : 75094768867 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 2383 ^ 1, 404009 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75094768867 - 1) / 2 = 37547384433 from by norm_num]
      have h2 : (2 : ZMod 75094768867) ^ 37547384433 = ((75094768866 : ℕ) : ZMod 75094768867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75094768867 - 1) / 3 = 25031589622 from by norm_num]
      have h2 : (2 : ZMod 75094768867) ^ 25031589622 = ((73593797387 : ℕ) : ZMod 75094768867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75094768867 - 1) / 13 = 5776520682 from by norm_num]
      have h2 : (2 : ZMod 75094768867) ^ 5776520682 = ((42106102021 : ℕ) : ZMod 75094768867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75094768867 - 1) / 2383 = 31512702 from by norm_num]
      have h2 : (2 : ZMod 75094768867) ^ 31512702 = ((9187209326 : ℕ) : ZMod 75094768867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (75094768867 - 1) / 404009 = 185874 from by norm_num]
      have h2 : (2 : ZMod 75094768867) ^ 185874 = ((66310039140 : ℕ) : ZMod 75094768867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_69613356835181 : Nat.Prime 69613356835181 := by
  refine lucas_primality 69613356835181 (2 : ZMod 69613356835181) ?_ (fun q hq hd => ?_)
  · rw [show 69613356835181 - 1 = 69613356835180 from by norm_num]
    reduce_mod_char
  · have e : 69613356835181 - 1 = [2 ^ 2, 5 ^ 1, 71 ^ 1, 151 ^ 1, 449 ^ 1, 723071 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 2 = 34806678417590 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 34806678417590 = ((69613356835180 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 5 = 13922671367036 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 13922671367036 = ((34143901166727 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 71 = 980469814580 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 980469814580 = ((48234103861612 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 151 = 461015608180 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 461015608180 = ((63389464314001 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 449 = 155040883820 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 155040883820 = ((57701064104941 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (69613356835181 - 1) / 723071 = 96274580 from by norm_num]
      have h2 : (2 : ZMod 69613356835181) ^ 96274580 = ((68990563315132 : ℕ) : ZMod 69613356835181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2506080846066517 : Nat.Prime 2506080846066517 := by
  refine lucas_primality 2506080846066517 (2 : ZMod 2506080846066517) ?_ (fun q hq hd => ?_)
  · rw [show 2506080846066517 - 1 = 2506080846066516 from by norm_num]
    reduce_mod_char
  · have e : 2506080846066517 - 1 = [2 ^ 2, 3 ^ 2, 69613356835181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2506080846066517 - 1) / 2 = 1253040423033258 from by norm_num]
      have h2 : (2 : ZMod 2506080846066517) ^ 1253040423033258 = ((2506080846066516 : ℕ) : ZMod 2506080846066517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2506080846066517 - 1) / 3 = 835360282022172 from by norm_num]
      have h2 : (2 : ZMod 2506080846066517) ^ 835360282022172 = ((2326805839993694 : ℕ) : ZMod 2506080846066517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_69613356835181).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2506080846066517 - 1) / 69613356835181 = 36 from by norm_num]
      have h2 : (2 : ZMod 2506080846066517) ^ 36 = ((68719476736 : ℕ) : ZMod 2506080846066517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_38488154120055537150068589763279 : Nat.Prime 38488154120055537150068589763279 := by
  refine lucas_primality 38488154120055537150068589763279 (6 : ZMod 38488154120055537150068589763279) ?_ (fun q hq hd => ?_)
  · rw [show 38488154120055537150068589763279 - 1 = 38488154120055537150068589763278 from by norm_num]
    reduce_mod_char
  · have e : 38488154120055537150068589763279 - 1 = [2 ^ 1, 3 ^ 3, 73 ^ 1, 181 ^ 1, 23497 ^ 1, 916061 ^ 1, 2506080846066517 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 2 = 19244077060027768575034294881639 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 19244077060027768575034294881639 = ((38488154120055537150068589763278 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 3 = 12829384706685179050022863254426 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 12829384706685179050022863254426 = ((38488154120055312008115644264597 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 73 = 527234987945966262329706709086 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 527234987945966262329706709086 = ((717897987691852588770249 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 181 = 212641735469920094751760164438 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 212641735469920094751760164438 = ((8022218054275805435990112634677 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 23497 = 1638002899095864882753908574 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 1638002899095864882753908574 = ((8050896684799819030429218427580 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 916061 = 42014837570921081838511398 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 42014837570921081838511398 = ((14092890908597429742810725383087 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2506080846066517).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38488154120055537150068589763279 - 1) / 2506080846066517 = 15357906023050134 from by norm_num]
      have h2 : (6 : ZMod 38488154120055537150068589763279) ^ 15357906023050134 = ((16977918718127858211459195356360 : ℕ) : ZMod 38488154120055537150068589763279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56495392933101222275861053369 : Nat.Prime 56495392933101222275861053369 := by
  refine lucas_primality 56495392933101222275861053369 (19 : ZMod 56495392933101222275861053369) ?_ (fun q hq hd => ?_)
  · rw [show 56495392933101222275861053369 - 1 = 56495392933101222275861053368 from by norm_num]
    reduce_mod_char
  · have e : 56495392933101222275861053369 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 11 ^ 2, 13 ^ 1, 61 ^ 1, 6971 ^ 1, 209449 ^ 1, 295759 ^ 1, 8115847 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 2 = 28247696466550611137930526684 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 28247696466550611137930526684 = ((56495392933101222275861053368 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 3 = 18831797644367074091953684456 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 18831797644367074091953684456 = ((56495392931074944699351565235 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 7 = 8070770419014460325123007624 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 8070770419014460325123007624 = ((56495392933095663215294497846 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 11 = 5135944812100111115987368488 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 5135944812100111115987368488 = ((4782969 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 13 = 4345799456392401713527773336 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 4345799456392401713527773336 = ((17918990931060030453747294062 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 61 = 926153982509856102882968088 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 926153982509856102882968088 = ((8142940884179598961583438294 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 6971 = 8104345564926297844765608 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 8104345564926297844765608 = ((35371684139128053072428898505 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 209449 = 269733409723136526199032 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 269733409723136526199032 = ((56175066751296350493665372883 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 295759 = 191018339029754706622152 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 191018339029754706622152 = ((25264735716047872142997213569 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56495392933101222275861053369 - 1) / 8115847 = 6961120993668463966344 from by norm_num]
      have h2 : (19 : ZMod 56495392933101222275861053369) ^ 6961120993668463966344 = ((28317986516354367406191561556 : ℕ) : ZMod 56495392933101222275861053369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_327220181191 : Nat.Prime 327220181191 := by
  refine lucas_primality 327220181191 (7 : ZMod 327220181191) ?_ (fun q hq hd => ?_)
  · rw [show 327220181191 - 1 = 327220181190 from by norm_num]
    reduce_mod_char
  · have e : 327220181191 - 1 = [2 ^ 1, 3 ^ 3, 5 ^ 1, 7 ^ 1, 79 ^ 1, 2191549 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 2 = 163610090595 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 163610090595 = ((327220181190 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 3 = 109073393730 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 109073393730 = ((270048287537 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 5 = 65444036238 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 65444036238 = ((221442097933 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 7 = 46745740170 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 46745740170 = ((235930974084 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 79 = 4142027610 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 4142027610 = ((43046721 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (327220181191 - 1) / 2191549 = 149310 from by norm_num]
      have h2 : (7 : ZMod 327220181191) ^ 149310 = ((32894389260 : ℕ) : ZMod 327220181191) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1125706177 : Nat.Prime 1125706177 := by
  refine lucas_primality 1125706177 (10 : ZMod 1125706177) ?_ (fun q hq hd => ?_)
  · rw [show 1125706177 - 1 = 1125706176 from by norm_num]
    reduce_mod_char
  · have e : 1125706177 - 1 = [2 ^ 6, 3 ^ 2, 7 ^ 1, 89 ^ 1, 3137 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1125706177 - 1) / 2 = 562853088 from by norm_num]
      have h2 : (10 : ZMod 1125706177) ^ 562853088 = ((1125706176 : ℕ) : ZMod 1125706177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1125706177 - 1) / 3 = 375235392 from by norm_num]
      have h2 : (10 : ZMod 1125706177) ^ 375235392 = ((911688555 : ℕ) : ZMod 1125706177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1125706177 - 1) / 7 = 160815168 from by norm_num]
      have h2 : (10 : ZMod 1125706177) ^ 160815168 = ((453665957 : ℕ) : ZMod 1125706177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1125706177 - 1) / 89 = 12648384 from by norm_num]
      have h2 : (10 : ZMod 1125706177) ^ 12648384 = ((34863995 : ℕ) : ZMod 1125706177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1125706177 - 1) / 3137 = 358848 from by norm_num]
      have h2 : (10 : ZMod 1125706177) ^ 358848 = ((313770190 : ℕ) : ZMod 1125706177) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2200760251 : Nat.Prime 2200760251 := by
  refine lucas_primality 2200760251 (2 : ZMod 2200760251) ?_ (fun q hq hd => ?_)
  · rw [show 2200760251 - 1 = 2200760250 from by norm_num]
    reduce_mod_char
  · have e : 2200760251 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 3, 13 ^ 2, 97 ^ 1, 179 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 2 = 1100380125 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 1100380125 = ((2200760250 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 3 = 733586750 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 733586750 = ((908200371 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 5 = 440152050 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 440152050 = ((769284795 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 13 = 169289250 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 169289250 = ((12374972 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 97 = 22688250 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 22688250 = ((1570261110 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2200760251 - 1) / 179 = 12294750 from by norm_num]
      have h2 : (2 : ZMod 2200760251) ^ 12294750 = ((1295731123 : ℕ) : ZMod 2200760251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_109542057747661771571447 : Nat.Prime 109542057747661771571447 := by
  refine lucas_primality 109542057747661771571447 (5 : ZMod 109542057747661771571447) ?_ (fun q hq hd => ?_)
  · rw [show 109542057747661771571447 - 1 = 109542057747661771571446 from by norm_num]
    reduce_mod_char
  · have e : 109542057747661771571447 - 1 = [2 ^ 1, 17 ^ 1, 1601 ^ 1, 12323 ^ 1, 74203 ^ 1, 2200760251 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 2 = 54771028873830885785723 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 54771028873830885785723 = ((109542057747661771571446 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 17 = 6443650455744810092438 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 6443650455744810092438 = ((25939735679123105712564 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 1601 = 68421022952943017846 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 68421022952943017846 = ((44470066422172975369882 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 12323 = 8889236204468211602 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 8889236204468211602 = ((45345534227014179070639 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 74203 = 1476248369306655682 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 1476248369306655682 = ((31851180287530582818078 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2200760251).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (109542057747661771571447 - 1) / 2200760251 = 49774643874946 from by norm_num]
      have h2 : (5 : ZMod 109542057747661771571447) ^ 49774643874946 = ((30790663096069219003769 : ℕ) : ZMod 109542057747661771571447) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17307645124130559908288627 : Nat.Prime 17307645124130559908288627 := by
  refine lucas_primality 17307645124130559908288627 (2 : ZMod 17307645124130559908288627) ?_ (fun q hq hd => ?_)
  · rw [show 17307645124130559908288627 - 1 = 17307645124130559908288626 from by norm_num]
    reduce_mod_char
  · have e : 17307645124130559908288627 - 1 = [2 ^ 1, 79 ^ 1, 109542057747661771571447 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17307645124130559908288627 - 1) / 2 = 8653822562065279954144313 from by norm_num]
      have h2 : (2 : ZMod 17307645124130559908288627) ^ 8653822562065279954144313 = ((17307645124130559908288626 : ℕ) : ZMod 17307645124130559908288627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17307645124130559908288627 - 1) / 79 = 219084115495323543142894 from by norm_num]
      have h2 : (2 : ZMod 17307645124130559908288627) ^ 219084115495323543142894 = ((1797169453522417520850794 : ℕ) : ZMod 17307645124130559908288627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_109542057747661771571447).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17307645124130559908288627 - 1) / 109542057747661771571447 = 158 from by norm_num]
      have h2 : (2 : ZMod 17307645124130559908288627) ^ 158 = ((13097193745374503718182705 : ℕ) : ZMod 17307645124130559908288627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_743170846305411756447828504941347481129 : Nat.Prime 743170846305411756447828504941347481129 := by
  refine lucas_primality 743170846305411756447828504941347481129 (6 : ZMod 743170846305411756447828504941347481129) ?_ (fun q hq hd => ?_)
  · rw [show 743170846305411756447828504941347481129 - 1 = 743170846305411756447828504941347481128 from by norm_num]
    reduce_mod_char
  · have e : 743170846305411756447828504941347481129 - 1 = [2 ^ 3, 11 ^ 1, 23 ^ 1, 277 ^ 1, 2137 ^ 1, 35839 ^ 1, 17307645124130559908288627 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 2 = 371585423152705878223914252470673740564 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 371585423152705878223914252470673740564 = ((743170846305411756447828504941347481128 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 11 = 67560986027764705131620773176486134648 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 67560986027764705131620773176486134648 = ((157162450413176228511619378313499752569 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 23 = 32311775926322250280340369780058586136 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 32311775926322250280340369780058586136 = ((741346045942271683320469452963490897208 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 277 = 2682927242979825835551727454661904264 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 2682927242979825835551727454661904264 = ((568726567580422270296599809231810701965 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 2137 = 347763615491535683878253862864458344 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 347763615491535683878253862864458344 = ((241937434397576441989874160746459992873 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 35839 = 20736372284533936673674725995182552 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 20736372284533936673674725995182552 = ((16051159194596422124420999687094838836 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17307645124130559908288627).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (743170846305411756447828504941347481129 - 1) / 17307645124130559908288627 = 42938877067064 from by norm_num]
      have h2 : (6 : ZMod 743170846305411756447828504941347481129) ^ 42938877067064 = ((577995190856585125904392702550923287913 : ℕ) : ZMod 743170846305411756447828504941347481129) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_563838649753 : Nat.Prime 563838649753 := by
  refine lucas_primality 563838649753 (5 : ZMod 563838649753) ?_ (fun q hq hd => ?_)
  · rw [show 563838649753 - 1 = 563838649752 from by norm_num]
    reduce_mod_char
  · have e : 563838649753 - 1 = [2 ^ 3, 3 ^ 1, 7 ^ 1, 19 ^ 1, 47 ^ 1, 83 ^ 1, 45281 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 2 = 281919324876 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 281919324876 = ((563838649752 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 3 = 187946216584 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 187946216584 = ((85944183420 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 7 = 80548378536 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 80548378536 = ((287172394014 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 19 = 29675718408 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 29675718408 = ((295022900397 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 47 = 11996567016 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 11996567016 = ((386461038385 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 83 = 6793236744 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 6793236744 = ((391902672570 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563838649753 - 1) / 45281 = 12451992 from by norm_num]
      have h2 : (5 : ZMod 563838649753) ^ 12451992 = ((532958174159 : ℕ) : ZMod 563838649753) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_459991849 : Nat.Prime 459991849 := by
  refine lucas_primality 459991849 (13 : ZMod 459991849) ?_ (fun q hq hd => ?_)
  · rw [show 459991849 - 1 = 459991848 from by norm_num]
    reduce_mod_char
  · have e : 459991849 - 1 = [2 ^ 3, 3 ^ 1, 17 ^ 1, 59 ^ 1, 97 ^ 1, 197 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 2 = 229995924 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 229995924 = ((459991848 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 3 = 153330616 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 153330616 = ((39917141 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 17 = 27058344 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 27058344 = ((352077922 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 59 = 7796472 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 7796472 = ((139148828 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 97 = 4742184 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 4742184 = ((3457405 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (459991849 - 1) / 197 = 2334984 from by norm_num]
      have h2 : (13 : ZMod 459991849) ^ 2334984 = ((293319573 : ℕ) : ZMod 459991849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3661040653 : Nat.Prime 3661040653 := by
  refine lucas_primality 3661040653 (2 : ZMod 3661040653) ?_ (fun q hq hd => ?_)
  · rw [show 3661040653 - 1 = 3661040652 from by norm_num]
    reduce_mod_char
  · have e : 3661040653 - 1 = [2 ^ 2, 3 ^ 1, 103 ^ 1, 2962007 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3661040653 - 1) / 2 = 1830520326 from by norm_num]
      have h2 : (2 : ZMod 3661040653) ^ 1830520326 = ((3661040652 : ℕ) : ZMod 3661040653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3661040653 - 1) / 3 = 1220346884 from by norm_num]
      have h2 : (2 : ZMod 3661040653) ^ 1220346884 = ((2455360263 : ℕ) : ZMod 3661040653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3661040653 - 1) / 103 = 35544084 from by norm_num]
      have h2 : (2 : ZMod 3661040653) ^ 35544084 = ((416559958 : ℕ) : ZMod 3661040653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3661040653 - 1) / 2962007 = 1236 from by norm_num]
      have h2 : (2 : ZMod 3661040653) ^ 1236 = ((336019254 : ℕ) : ZMod 3661040653) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1992772009 : Nat.Prime 1992772009 := by
  refine lucas_primality 1992772009 (13 : ZMod 1992772009) ?_ (fun q hq hd => ?_)
  · rw [show 1992772009 - 1 = 1992772008 from by norm_num]
    reduce_mod_char
  · have e : 1992772009 - 1 = [2 ^ 3, 3 ^ 2, 31 ^ 1, 109 ^ 1, 8191 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1992772009 - 1) / 2 = 996386004 from by norm_num]
      have h2 : (13 : ZMod 1992772009) ^ 996386004 = ((1992772008 : ℕ) : ZMod 1992772009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1992772009 - 1) / 3 = 664257336 from by norm_num]
      have h2 : (13 : ZMod 1992772009) ^ 664257336 = ((308184270 : ℕ) : ZMod 1992772009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1992772009 - 1) / 31 = 64282968 from by norm_num]
      have h2 : (13 : ZMod 1992772009) ^ 64282968 = ((663616709 : ℕ) : ZMod 1992772009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1992772009 - 1) / 109 = 18282312 from by norm_num]
      have h2 : (13 : ZMod 1992772009) ^ 18282312 = ((1175580954 : ℕ) : ZMod 1992772009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1992772009 - 1) / 8191 = 243288 from by norm_num]
      have h2 : (13 : ZMod 1992772009) ^ 243288 = ((654507090 : ℕ) : ZMod 1992772009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_199277201 : Nat.Prime 199277201 := by
  refine lucas_primality 199277201 (3 : ZMod 199277201) ?_ (fun q hq hd => ?_)
  · rw [show 199277201 - 1 = 199277200 from by norm_num]
    reduce_mod_char
  · have e : 199277201 - 1 = [2 ^ 4, 5 ^ 2, 131 ^ 1, 3803 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (199277201 - 1) / 2 = 99638600 from by norm_num]
      have h2 : (3 : ZMod 199277201) ^ 99638600 = ((199277200 : ℕ) : ZMod 199277201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (199277201 - 1) / 5 = 39855440 from by norm_num]
      have h2 : (3 : ZMod 199277201) ^ 39855440 = ((86698767 : ℕ) : ZMod 199277201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (199277201 - 1) / 131 = 1521200 from by norm_num]
      have h2 : (3 : ZMod 199277201) ^ 1521200 = ((113761677 : ℕ) : ZMod 199277201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (199277201 - 1) / 3803 = 52400 from by norm_num]
      have h2 : (3 : ZMod 199277201) ^ 52400 = ((182049861 : ℕ) : ZMod 199277201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37945127666529000523013 : Nat.Prime 37945127666529000523013 := by
  refine lucas_primality 37945127666529000523013 (2 : ZMod 37945127666529000523013) ?_ (fun q hq hd => ?_)
  · rw [show 37945127666529000523013 - 1 = 37945127666529000523012 from by norm_num]
    reduce_mod_char
  · have e : 37945127666529000523013 - 1 = [2 ^ 2, 11 ^ 1, 29 ^ 1, 251 ^ 1, 182239 ^ 1, 341273 ^ 1, 1904971 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 2 = 18972563833264500261506 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 18972563833264500261506 = ((37945127666529000523012 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 11 = 3449557060593545502092 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 3449557060593545502092 = ((23841261475642174294899 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 29 = 1308452678156172431828 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 1308452678156172431828 = ((20143709748898111388760 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 251 = 151175807436370520012 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 151175807436370520012 = ((21984625557128295118489 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 182239 = 208216285572950908 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 208216285572950908 = ((27690422016412711958920 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 341273 = 111187019384859044 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 111187019384859044 = ((20160315057459293955109 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37945127666529000523013 - 1) / 1904971 = 19919005416108172 from by norm_num]
      have h2 : (2 : ZMod 37945127666529000523013) ^ 19919005416108172 = ((32172970739967193746424 : ℕ) : ZMod 37945127666529000523013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19966781110160346782368664772328944885905284750420567849 : Nat.Prime 19966781110160346782368664772328944885905284750420567849 := by
  refine lucas_primality 19966781110160346782368664772328944885905284750420567849 (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ?_ (fun q hq hd => ?_)
  · rw [show 19966781110160346782368664772328944885905284750420567849 - 1 = 19966781110160346782368664772328944885905284750420567848 from by norm_num]
    reduce_mod_char
  · have e : 19966781110160346782368664772328944885905284750420567849 - 1 = [2 ^ 3, 3 ^ 2, 59 ^ 1, 523 ^ 1, 6091 ^ 1, 12413 ^ 1, 28537 ^ 1, 5385997 ^ 1, 20381027 ^ 1, 37945127666529000523013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 2 = 9983390555080173391184332386164472442952642375210283924 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 9983390555080173391184332386164472442952642375210283924 = ((19966781110160346782368664772328944885905284750420567848 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 3 = 6655593703386782260789554924109648295301761583473522616 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 6655593703386782260789554924109648295301761583473522616 = ((11184349152189498154600305425577088632057477448795558462 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 59 = 338420018816277064107943470717439743828903131363060472 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 338420018816277064107943470717439743828903131363060472 = ((12157665459056928801 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 523 = 38177401740268349488276605683229340126013928777094776 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 38177401740268349488276605683229340126013928777094776 = ((18755990460444502243066589476244387592993394779320122109 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 6091 = 3278079315409677685498056931920693627631798514270328 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 3278079315409677685498056931920693627631798514270328 = ((9950470449796554721994454246203183251286711079728153351 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 12413 = 1608537912685116151000456358038261893652242387047496 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 1608537912685116151000456358038261893652242387047496 = ((9743258215586805635343884917615535418469223210459798403 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 28537 = 699680453802444082502318560897394431296397124800104 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 699680453802444082502318560897394431296397124800104 = ((12526995197919249863388281920645055400234313028368243534 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 5385997 = 3707165286233977995600195241907662571276085885384 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 3707165286233977995600195241907662571276085885384 = ((2837508917599992926234072561007420294832858606040540731 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 20381027 = 979674925613922536011981377205817198804814141624 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 979674925613922536011981377205817198804814141624 = ((14209516906408792648089560908174480209198386833758856937 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_37945127666529000523013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19966781110160346782368664772328944885905284750420567849 - 1) / 37945127666529000523013 = 526201447670258734222936799212296 from by norm_num]
      have h2 : (17 : ZMod 19966781110160346782368664772328944885905284750420567849) ^ 526201447670258734222936799212296 = ((1935230248476179475399253436201416943106465974473594189 : ℕ) : ZMod 19966781110160346782368664772328944885905284750420567849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_262199473 : Nat.Prime 262199473 := by
  refine lucas_primality 262199473 (5 : ZMod 262199473) ?_ (fun q hq hd => ?_)
  · rw [show 262199473 - 1 = 262199472 from by norm_num]
    reduce_mod_char
  · have e : 262199473 - 1 = [2 ^ 4, 3 ^ 1, 61 ^ 1, 149 ^ 1, 601 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262199473 - 1) / 2 = 131099736 from by norm_num]
      have h2 : (5 : ZMod 262199473) ^ 131099736 = ((262199472 : ℕ) : ZMod 262199473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262199473 - 1) / 3 = 87399824 from by norm_num]
      have h2 : (5 : ZMod 262199473) ^ 87399824 = ((58627825 : ℕ) : ZMod 262199473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262199473 - 1) / 61 = 4298352 from by norm_num]
      have h2 : (5 : ZMod 262199473) ^ 4298352 = ((14226949 : ℕ) : ZMod 262199473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262199473 - 1) / 149 = 1759728 from by norm_num]
      have h2 : (5 : ZMod 262199473) ^ 1759728 = ((252394714 : ℕ) : ZMod 262199473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (262199473 - 1) / 601 = 436272 from by norm_num]
      have h2 : (5 : ZMod 262199473) ^ 436272 = ((77120273 : ℕ) : ZMod 262199473) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17609368811 : Nat.Prime 17609368811 := by
  refine lucas_primality 17609368811 (6 : ZMod 17609368811) ?_ (fun q hq hd => ?_)
  · rw [show 17609368811 - 1 = 17609368810 from by norm_num]
    reduce_mod_char
  · have e : 17609368811 - 1 = [2 ^ 1, 5 ^ 1, 11 ^ 1, 83 ^ 1, 331 ^ 1, 5827 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 2 = 8804684405 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 8804684405 = ((17609368810 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 5 = 3521873762 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 3521873762 = ((7662513375 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 11 = 1600851710 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 1600851710 = ((5722932399 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 83 = 212161070 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 212161070 = ((11029591640 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 331 = 53200510 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 53200510 = ((6419338182 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17609368811 - 1) / 5827 = 3022030 from by norm_num]
      have h2 : (6 : ZMod 17609368811) ^ 3022030 = ((8932334522 : ℕ) : ZMod 17609368811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_81516726600079249 : Nat.Prime 81516726600079249 := by
  refine lucas_primality 81516726600079249 (7 : ZMod 81516726600079249) ?_ (fun q hq hd => ?_)
  · rw [show 81516726600079249 - 1 = 81516726600079248 from by norm_num]
    reduce_mod_char
  · have e : 81516726600079249 - 1 = [2 ^ 4, 3 ^ 2, 17 ^ 1, 31 ^ 1, 61 ^ 1, 17609368811 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 2 = 40758363300039624 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 40758363300039624 = ((81516726600079248 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 3 = 27172242200026416 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 27172242200026416 = ((43808573428028856 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 17 = 4795101564710544 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 4795101564710544 = ((9778557381481546 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 31 = 2629571825809008 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 2629571825809008 = ((4596237195734696 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 61 = 1336339780329168 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 1336339780329168 = ((25131811786217455 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17609368811).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (81516726600079249 - 1) / 17609368811 = 4629168 from by norm_num]
      have h2 : (7 : ZMod 81516726600079249) ^ 4629168 = ((21184724693805899 : ℕ) : ZMod 81516726600079249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52147471 : Nat.Prime 52147471 := by
  refine lucas_primality 52147471 (6 : ZMod 52147471) ?_ (fun q hq hd => ?_)
  · rw [show 52147471 - 1 = 52147470 from by norm_num]
    reduce_mod_char
  · have e : 52147471 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 127 ^ 1, 13687 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52147471 - 1) / 2 = 26073735 from by norm_num]
      have h2 : (6 : ZMod 52147471) ^ 26073735 = ((52147470 : ℕ) : ZMod 52147471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52147471 - 1) / 3 = 17382490 from by norm_num]
      have h2 : (6 : ZMod 52147471) ^ 17382490 = ((27816263 : ℕ) : ZMod 52147471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52147471 - 1) / 5 = 10429494 from by norm_num]
      have h2 : (6 : ZMod 52147471) ^ 10429494 = ((33100447 : ℕ) : ZMod 52147471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52147471 - 1) / 127 = 410610 from by norm_num]
      have h2 : (6 : ZMod 52147471) ^ 410610 = ((28260269 : ℕ) : ZMod 52147471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52147471 - 1) / 13687 = 3810 from by norm_num]
      have h2 : (6 : ZMod 52147471) ^ 3810 = ((18778844 : ℕ) : ZMod 52147471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_59002397 : Nat.Prime 59002397 := by
  refine lucas_primality 59002397 (2 : ZMod 59002397) ?_ (fun q hq hd => ?_)
  · rw [show 59002397 - 1 = 59002396 from by norm_num]
    reduce_mod_char
  · have e : 59002397 - 1 = [2 ^ 2, 73 ^ 1, 202063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59002397 - 1) / 2 = 29501198 from by norm_num]
      have h2 : (2 : ZMod 59002397) ^ 29501198 = ((59002396 : ℕ) : ZMod 59002397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59002397 - 1) / 73 = 808252 from by norm_num]
      have h2 : (2 : ZMod 59002397) ^ 808252 = ((23649042 : ℕ) : ZMod 59002397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59002397 - 1) / 202063 = 292 from by norm_num]
      have h2 : (2 : ZMod 59002397) ^ 292 = ((56514982 : ℕ) : ZMod 59002397) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_354014383 : Nat.Prime 354014383 := by
  refine lucas_primality 354014383 (3 : ZMod 354014383) ?_ (fun q hq hd => ?_)
  · rw [show 354014383 - 1 = 354014382 from by norm_num]
    reduce_mod_char
  · have e : 354014383 - 1 = [2 ^ 1, 3 ^ 1, 59002397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (354014383 - 1) / 2 = 177007191 from by norm_num]
      have h2 : (3 : ZMod 354014383) ^ 177007191 = ((354014382 : ℕ) : ZMod 354014383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (354014383 - 1) / 3 = 118004794 from by norm_num]
      have h2 : (3 : ZMod 354014383) ^ 118004794 = ((264994930 : ℕ) : ZMod 354014383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_59002397).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (354014383 - 1) / 59002397 = 6 from by norm_num]
      have h2 : (3 : ZMod 354014383) ^ 6 = ((729 : ℕ) : ZMod 354014383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_165681871 : Nat.Prime 165681871 := by
  refine lucas_primality 165681871 (3 : ZMod 165681871) ?_ (fun q hq hd => ?_)
  · rw [show 165681871 - 1 = 165681870 from by norm_num]
    reduce_mod_char
  · have e : 165681871 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 941 ^ 1, 5869 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165681871 - 1) / 2 = 82840935 from by norm_num]
      have h2 : (3 : ZMod 165681871) ^ 82840935 = ((165681870 : ℕ) : ZMod 165681871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165681871 - 1) / 3 = 55227290 from by norm_num]
      have h2 : (3 : ZMod 165681871) ^ 55227290 = ((32685157 : ℕ) : ZMod 165681871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165681871 - 1) / 5 = 33136374 from by norm_num]
      have h2 : (3 : ZMod 165681871) ^ 33136374 = ((152883740 : ℕ) : ZMod 165681871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165681871 - 1) / 941 = 176070 from by norm_num]
      have h2 : (3 : ZMod 165681871) ^ 176070 = ((57941737 : ℕ) : ZMod 165681871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165681871 - 1) / 5869 = 28230 from by norm_num]
      have h2 : (3 : ZMod 165681871) ^ 28230 = ((14459575 : ℕ) : ZMod 165681871) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_804143122761366630031 : Nat.Prime 804143122761366630031 := by
  refine lucas_primality 804143122761366630031 (3 : ZMod 804143122761366630031) ?_ (fun q hq hd => ?_)
  · rw [show 804143122761366630031 - 1 = 804143122761366630030 from by norm_num]
    reduce_mod_char
  · have e : 804143122761366630031 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 457 ^ 1, 165681871 ^ 1, 354014383 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 2 = 402071561380683315015 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 402071561380683315015 = ((804143122761366630030 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 3 = 268047707587122210010 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 268047707587122210010 = ((283045183443087060496 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 5 = 160828624552273326006 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 160828624552273326006 = ((188875807216316254624 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 457 = 1759612960090517790 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 1759612960090517790 = ((427100656525523883200 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_165681871).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 165681871 = 4853537190930 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 4853537190930 = ((512069089422081118553 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_354014383).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (804143122761366630031 - 1) / 354014383 = 2271498451410 from by norm_num]
      have h2 : (3 : ZMod 804143122761366630031) ^ 2271498451410 = ((681109259520593590282 : ℕ) : ZMod 804143122761366630031) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_114742271896804438572098194909 : Nat.Prime 114742271896804438572098194909 := by
  refine lucas_primality 114742271896804438572098194909 (2 : ZMod 114742271896804438572098194909) ?_ (fun q hq hd => ?_)
  · rw [show 114742271896804438572098194909 - 1 = 114742271896804438572098194908 from by norm_num]
    reduce_mod_char
  · have e : 114742271896804438572098194909 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 131 ^ 1, 12967 ^ 1, 804143122761366630031 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 2 = 57371135948402219286049097454 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 57371135948402219286049097454 = ((114742271896804438572098194908 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 3 = 38247423965601479524032731636 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 38247423965601479524032731636 = ((38629514752293026272935410950 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 7 = 16391753128114919796014027844 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 16391753128114919796014027844 = ((35591363267073506370993120880 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 131 = 875895205319117851695406068 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 875895205319117851695406068 = ((109418989131512359209 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 12967 = 8848790922866078396861124 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 8848790922866078396861124 = ((62117927762303871765091703110 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_804143122761366630031).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (114742271896804438572098194909 - 1) / 804143122761366630031 = 142688868 from by norm_num]
      have h2 : (2 : ZMod 114742271896804438572098194909) ^ 142688868 = ((110873536393449821327484616095 : ℕ) : ZMod 114742271896804438572098194909) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_278190961 : Nat.Prime 278190961 := by
  refine lucas_primality 278190961 (17 : ZMod 278190961) ?_ (fun q hq hd => ?_)
  · rw [show 278190961 - 1 = 278190960 from by norm_num]
    reduce_mod_char
  · have e : 278190961 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 127 ^ 1, 9127 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278190961 - 1) / 2 = 139095480 from by norm_num]
      have h2 : (17 : ZMod 278190961) ^ 139095480 = ((278190960 : ℕ) : ZMod 278190961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278190961 - 1) / 3 = 92730320 from by norm_num]
      have h2 : (17 : ZMod 278190961) ^ 92730320 = ((193951926 : ℕ) : ZMod 278190961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278190961 - 1) / 5 = 55638192 from by norm_num]
      have h2 : (17 : ZMod 278190961) ^ 55638192 = ((196154356 : ℕ) : ZMod 278190961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278190961 - 1) / 127 = 2190480 from by norm_num]
      have h2 : (17 : ZMod 278190961) ^ 2190480 = ((40650748 : ℕ) : ZMod 278190961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (278190961 - 1) / 9127 = 30480 from by norm_num]
      have h2 : (17 : ZMod 278190961) ^ 30480 = ((138357337 : ℕ) : ZMod 278190961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_82093596209179 : Nat.Prime 82093596209179 := by
  refine lucas_primality 82093596209179 (2 : ZMod 82093596209179) ?_ (fun q hq hd => ?_)
  · rw [show 82093596209179 - 1 = 82093596209178 from by norm_num]
    reduce_mod_char
  · have e : 82093596209179 - 1 = [2 ^ 1, 3 ^ 1, 137 ^ 1, 359 ^ 1, 278190961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82093596209179 - 1) / 2 = 41046798104589 from by norm_num]
      have h2 : (2 : ZMod 82093596209179) ^ 41046798104589 = ((82093596209178 : ℕ) : ZMod 82093596209179) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82093596209179 - 1) / 3 = 27364532069726 from by norm_num]
      have h2 : (2 : ZMod 82093596209179) ^ 27364532069726 = ((36927128127993 : ℕ) : ZMod 82093596209179) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82093596209179 - 1) / 137 = 599223329994 from by norm_num]
      have h2 : (2 : ZMod 82093596209179) ^ 599223329994 = ((38422288054810 : ℕ) : ZMod 82093596209179) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82093596209179 - 1) / 359 = 228672969942 from by norm_num]
      have h2 : (2 : ZMod 82093596209179) ^ 228672969942 = ((16199239036856 : ℕ) : ZMod 82093596209179) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_278190961).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82093596209179 - 1) / 278190961 = 295098 from by norm_num]
      have h2 : (2 : ZMod 82093596209179) ^ 295098 = ((71103356048994 : ℕ) : ZMod 82093596209179) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_26436515641 : Nat.Prime 26436515641 := by
  refine lucas_primality 26436515641 (11 : ZMod 26436515641) ?_ (fun q hq hd => ?_)
  · rw [show 26436515641 - 1 = 26436515640 from by norm_num]
    reduce_mod_char
  · have e : 26436515641 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 19 ^ 1, 139 ^ 1, 83417 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 2 = 13218257820 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 13218257820 = ((26436515640 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 3 = 8812171880 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 8812171880 = ((4258493625 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 5 = 5287303128 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 5287303128 = ((13217787471 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 19 = 1391395560 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 1391395560 = ((5116553542 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 139 = 190190760 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 190190760 = ((3069691263 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26436515641 - 1) / 83417 = 316920 from by norm_num]
      have h2 : (11 : ZMod 26436515641) ^ 316920 = ((2132490846 : ℕ) : ZMod 26436515641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3672239816477 : Nat.Prime 3672239816477 := by
  refine lucas_primality 3672239816477 (2 : ZMod 3672239816477) ?_ (fun q hq hd => ?_)
  · rw [show 3672239816477 - 1 = 3672239816476 from by norm_num]
    reduce_mod_char
  · have e : 3672239816477 - 1 = [2 ^ 2, 7 ^ 3, 11 ^ 1, 71 ^ 1, 3427093 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3672239816477 - 1) / 2 = 1836119908238 from by norm_num]
      have h2 : (2 : ZMod 3672239816477) ^ 1836119908238 = ((3672239816476 : ℕ) : ZMod 3672239816477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3672239816477 - 1) / 7 = 524605688068 from by norm_num]
      have h2 : (2 : ZMod 3672239816477) ^ 524605688068 = ((3583448808326 : ℕ) : ZMod 3672239816477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3672239816477 - 1) / 11 = 333839983316 from by norm_num]
      have h2 : (2 : ZMod 3672239816477) ^ 333839983316 = ((1230674813009 : ℕ) : ZMod 3672239816477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3672239816477 - 1) / 71 = 51721687556 from by norm_num]
      have h2 : (2 : ZMod 3672239816477) ^ 51721687556 = ((1695265938718 : ℕ) : ZMod 3672239816477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3672239816477 - 1) / 3427093 = 1071532 from by norm_num]
      have h2 : (2 : ZMod 3672239816477) ^ 1071532 = ((1218980867620 : ℕ) : ZMod 3672239816477) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3905597993153 : Nat.Prime 3905597993153 := by
  refine lucas_primality 3905597993153 (3 : ZMod 3905597993153) ?_ (fun q hq hd => ?_)
  · rw [show 3905597993153 - 1 = 3905597993152 from by norm_num]
    reduce_mod_char
  · have e : 3905597993153 - 1 = [2 ^ 6, 6469 ^ 1, 9433447 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3905597993153 - 1) / 2 = 1952798996576 from by norm_num]
      have h2 : (3 : ZMod 3905597993153) ^ 1952798996576 = ((3905597993152 : ℕ) : ZMod 3905597993153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3905597993153 - 1) / 6469 = 603740608 from by norm_num]
      have h2 : (3 : ZMod 3905597993153) ^ 603740608 = ((543781280615 : ℕ) : ZMod 3905597993153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3905597993153 - 1) / 9433447 = 414016 from by norm_num]
      have h2 : (3 : ZMod 3905597993153) ^ 414016 = ((2273706139588 : ℕ) : ZMod 3905597993153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_65543745521093647 : Nat.Prime 65543745521093647 := by
  refine lucas_primality 65543745521093647 (3 : ZMod 65543745521093647) ?_ (fun q hq hd => ?_)
  · rw [show 65543745521093647 - 1 = 65543745521093646 from by norm_num]
    reduce_mod_char
  · have e : 65543745521093647 - 1 = [2 ^ 1, 3 ^ 1, 2797 ^ 1, 3905597993153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65543745521093647 - 1) / 2 = 32771872760546823 from by norm_num]
      have h2 : (3 : ZMod 65543745521093647) ^ 32771872760546823 = ((65543745521093646 : ℕ) : ZMod 65543745521093647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65543745521093647 - 1) / 3 = 21847915173697882 from by norm_num]
      have h2 : (3 : ZMod 65543745521093647) ^ 21847915173697882 = ((21421921881672813 : ℕ) : ZMod 65543745521093647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65543745521093647 - 1) / 2797 = 23433587958918 from by norm_num]
      have h2 : (3 : ZMod 65543745521093647) ^ 23433587958918 = ((53574467747838201 : ℕ) : ZMod 65543745521093647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3905597993153).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (65543745521093647 - 1) / 3905597993153 = 16782 from by norm_num]
      have h2 : (3 : ZMod 65543745521093647) ^ 16782 = ((39152021658247128 : ℕ) : ZMod 65543745521093647) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4482722618976860674653013440107317 : Nat.Prime 4482722618976860674653013440107317 := by
  refine lucas_primality 4482722618976860674653013440107317 (2 : ZMod 4482722618976860674653013440107317) ?_ (fun q hq hd => ?_)
  · rw [show 4482722618976860674653013440107317 - 1 = 4482722618976860674653013440107316 from by norm_num]
    reduce_mod_char
  · have e : 4482722618976860674653013440107317 - 1 = [2 ^ 2, 3 ^ 1, 149 ^ 1, 421 ^ 1, 3593 ^ 1, 25287377 ^ 1, 65543745521093647 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 2 = 2241361309488430337326506720053658 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 2241361309488430337326506720053658 = ((4482722618976860674653013440107316 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 3 = 1494240872992286891551004480035772 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 1494240872992286891551004480035772 = ((3790978385229189358090095822240414 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 149 = 30085386704542689091630962685284 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 30085386704542689091630962685284 = ((2924290301468845425447766873541639 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 421 = 10647797194719384025304069928996 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 10647797194719384025304069928996 = ((1313056047983678772839060249000108 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 3593 = 1247626668237367290468414539412 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 1247626668237367290468414539412 = ((4296162945822728239285712849852249 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 25287377 = 177271158609169336726897908 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 177271158609169336726897908 = ((499716340551319990297446279203297 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_65543745521093647).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4482722618976860674653013440107317 - 1) / 65543745521093647 = 68392835705951628 from by norm_num]
      have h2 : (2 : ZMod 4482722618976860674653013440107317) ^ 68392835705951628 = ((834665781119675636574791354186328 : ℕ) : ZMod 4482722618976860674653013440107317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6309134551 : Nat.Prime 6309134551 := by
  refine lucas_primality 6309134551 (3 : ZMod 6309134551) ?_ (fun q hq hd => ?_)
  · rw [show 6309134551 - 1 = 6309134550 from by norm_num]
    reduce_mod_char
  · have e : 6309134551 - 1 = [2 ^ 1, 3 ^ 4, 5 ^ 2, 37 ^ 1, 71 ^ 1, 593 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 2 = 3154567275 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 3154567275 = ((6309134550 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 3 = 2103044850 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 2103044850 = ((1041037548 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 5 = 1261826910 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 1261826910 = ((5782567821 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 37 = 170517150 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 170517150 = ((813494293 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 71 = 88861050 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 88861050 = ((1237474797 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6309134551 - 1) / 593 = 10639350 from by norm_num]
      have h2 : (3 : ZMod 6309134551) ^ 10639350 = ((5440349587 : ℕ) : ZMod 6309134551) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_159420524134654609 : Nat.Prime 159420524134654609 := by
  refine lucas_primality 159420524134654609 (11 : ZMod 159420524134654609) ?_ (fun q hq hd => ?_)
  · rw [show 159420524134654609 - 1 = 159420524134654608 from by norm_num]
    reduce_mod_char
  · have e : 159420524134654609 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 157 ^ 1, 479 ^ 1, 6309134551 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 2 = 79710262067327304 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 79710262067327304 = ((159420524134654608 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 3 = 53140174711551536 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 53140174711551536 = ((25277548955605459 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 7 = 22774360590664944 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 22774360590664944 = ((113289396828498706 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 157 = 1015417351176144 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 1015417351176144 = ((147180471612131250 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 479 = 332819465834352 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 332819465834352 = ((98997385323955042 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6309134551).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (159420524134654609 - 1) / 6309134551 = 25268208 from by norm_num]
      have h2 : (11 : ZMod 159420524134654609) ^ 25268208 = ((143975536017752882 : ℕ) : ZMod 159420524134654609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43117687 : Nat.Prime 43117687 := by
  refine lucas_primality 43117687 (3 : ZMod 43117687) ?_ (fun q hq hd => ?_)
  · rw [show 43117687 - 1 = 43117686 from by norm_num]
    reduce_mod_char
  · have e : 43117687 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 104149 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43117687 - 1) / 2 = 21558843 from by norm_num]
      have h2 : (3 : ZMod 43117687) ^ 21558843 = ((43117686 : ℕ) : ZMod 43117687) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43117687 - 1) / 3 = 14372562 from by norm_num]
      have h2 : (3 : ZMod 43117687) ^ 14372562 = ((20816251 : ℕ) : ZMod 43117687) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43117687 - 1) / 23 = 1874682 from by norm_num]
      have h2 : (3 : ZMod 43117687) ^ 1874682 = ((39007719 : ℕ) : ZMod 43117687) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43117687 - 1) / 104149 = 414 from by norm_num]
      have h2 : (3 : ZMod 43117687) ^ 414 = ((24983002 : ℕ) : ZMod 43117687) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10520715629 : Nat.Prime 10520715629 := by
  refine lucas_primality 10520715629 (2 : ZMod 10520715629) ?_ (fun q hq hd => ?_)
  · rw [show 10520715629 - 1 = 10520715628 from by norm_num]
    reduce_mod_char
  · have e : 10520715629 - 1 = [2 ^ 2, 61 ^ 1, 43117687 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10520715629 - 1) / 2 = 5260357814 from by norm_num]
      have h2 : (2 : ZMod 10520715629) ^ 5260357814 = ((10520715628 : ℕ) : ZMod 10520715629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10520715629 - 1) / 61 = 172470748 from by norm_num]
      have h2 : (2 : ZMod 10520715629) ^ 172470748 = ((7914101019 : ℕ) : ZMod 10520715629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_43117687).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10520715629 - 1) / 43117687 = 244 from by norm_num]
      have h2 : (2 : ZMod 10520715629) ^ 244 = ((6856101104 : ℕ) : ZMod 10520715629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_555622958557692863 : Nat.Prime 555622958557692863 := by
  refine lucas_primality 555622958557692863 (5 : ZMod 555622958557692863) ?_ (fun q hq hd => ?_)
  · rw [show 555622958557692863 - 1 = 555622958557692862 from by norm_num]
    reduce_mod_char
  · have e : 555622958557692863 - 1 = [2 ^ 1, 23 ^ 1, 449 ^ 1, 2557 ^ 1, 10520715629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (555622958557692863 - 1) / 2 = 277811479278846431 from by norm_num]
      have h2 : (5 : ZMod 555622958557692863) ^ 277811479278846431 = ((555622958557692862 : ℕ) : ZMod 555622958557692863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (555622958557692863 - 1) / 23 = 24157519937290994 from by norm_num]
      have h2 : (5 : ZMod 555622958557692863) ^ 24157519937290994 = ((252832273151175454 : ℕ) : ZMod 555622958557692863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (555622958557692863 - 1) / 449 = 1237467613714238 from by norm_num]
      have h2 : (5 : ZMod 555622958557692863) ^ 1237467613714238 = ((161408667158521600 : ℕ) : ZMod 555622958557692863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (555622958557692863 - 1) / 2557 = 217294860601366 from by norm_num]
      have h2 : (5 : ZMod 555622958557692863) ^ 217294860601366 = ((495970963803360282 : ℕ) : ZMod 555622958557692863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_10520715629).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (555622958557692863 - 1) / 10520715629 = 52812278 from by norm_num]
      have h2 : (5 : ZMod 555622958557692863) ^ 52812278 = ((175579665036358089 : ℕ) : ZMod 555622958557692863) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2000882747 : Nat.Prime 2000882747 := by
  refine lucas_primality 2000882747 (2 : ZMod 2000882747) ?_ (fun q hq hd => ?_)
  · rw [show 2000882747 - 1 = 2000882746 from by norm_num]
    reduce_mod_char
  · have e : 2000882747 - 1 = [2 ^ 1, 23 ^ 1, 379 ^ 1, 114769 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2000882747 - 1) / 2 = 1000441373 from by norm_num]
      have h2 : (2 : ZMod 2000882747) ^ 1000441373 = ((2000882746 : ℕ) : ZMod 2000882747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2000882747 - 1) / 23 = 86994902 from by norm_num]
      have h2 : (2 : ZMod 2000882747) ^ 86994902 = ((614933521 : ℕ) : ZMod 2000882747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2000882747 - 1) / 379 = 5279374 from by norm_num]
      have h2 : (2 : ZMod 2000882747) ^ 5279374 = ((450531222 : ℕ) : ZMod 2000882747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2000882747 - 1) / 114769 = 17434 from by norm_num]
      have h2 : (2 : ZMod 2000882747) ^ 17434 = ((598329095 : ℕ) : ZMod 2000882747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10393819190815276250780568850989337 : Nat.Prime 10393819190815276250780568850989337 := by
  refine lucas_primality 10393819190815276250780568850989337 (5 : ZMod 10393819190815276250780568850989337) ?_ (fun q hq hd => ?_)
  · rw [show 10393819190815276250780568850989337 - 1 = 10393819190815276250780568850989336 from by norm_num]
    reduce_mod_char
  · have e : 10393819190815276250780568850989337 - 1 = [2 ^ 3, 3 ^ 1, 79 ^ 1, 4931 ^ 1, 2000882747 ^ 1, 555622958557692863 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 2 = 5196909595407638125390284425494668 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 5196909595407638125390284425494668 = ((10393819190815276250780568850989336 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 3 = 3464606396938425416926856283663112 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 3464606396938425416926856283663112 = ((1085373793566002952521612872086230 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 79 = 131567331529307294313678086721384 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 131567331529307294313678086721384 = ((6282319334550424771613483766637701 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 4931 = 2107852198502388207418488917256 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 2107852198502388207418488917256 = ((657852489815562020903346852532068 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2000882747).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 2000882747 = 5194616829196576730130888 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 5194616829196576730130888 = ((3493287765551823090747163448741785 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_555622958557692863).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10393819190815276250780568850989337 - 1) / 555622958557692863 = 18706604957066472 from by norm_num]
      have h2 : (5 : ZMod 10393819190815276250780568850989337) ^ 18706604957066472 = ((10165451832824120789504743531530178 : ℕ) : ZMod 10393819190815276250780568850989337) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8483499631 : Nat.Prime 8483499631 := by
  refine lucas_primality 8483499631 (6 : ZMod 8483499631) ?_ (fun q hq hd => ?_)
  · rw [show 8483499631 - 1 = 8483499630 from by norm_num]
    reduce_mod_char
  · have e : 8483499631 - 1 = [2 ^ 1, 3 ^ 3, 5 ^ 1, 17 ^ 2, 23 ^ 1, 29 ^ 1, 163 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 2 = 4241749815 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 4241749815 = ((8483499630 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 3 = 2827833210 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 2827833210 = ((6574475690 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 5 = 1696699926 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 1696699926 = ((3168632066 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 17 = 499029390 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 499029390 = ((3668504249 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 23 = 368847810 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 368847810 = ((3192785157 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 29 = 292534470 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 292534470 = ((5981526859 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8483499631 - 1) / 163 = 52046010 from by norm_num]
      have h2 : (6 : ZMod 8483499631) ^ 52046010 = ((6913671566 : ℕ) : ZMod 8483499631) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_530218727 : Nat.Prime 530218727 := by
  refine lucas_primality 530218727 (5 : ZMod 530218727) ?_ (fun q hq hd => ?_)
  · rw [show 530218727 - 1 = 530218726 from by norm_num]
    reduce_mod_char
  · have e : 530218727 - 1 = [2 ^ 1, 379 ^ 1, 443 ^ 1, 1579 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (530218727 - 1) / 2 = 265109363 from by norm_num]
      have h2 : (5 : ZMod 530218727) ^ 265109363 = ((530218726 : ℕ) : ZMod 530218727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (530218727 - 1) / 379 = 1398994 from by norm_num]
      have h2 : (5 : ZMod 530218727) ^ 1398994 = ((471267185 : ℕ) : ZMod 530218727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (530218727 - 1) / 443 = 1196882 from by norm_num]
      have h2 : (5 : ZMod 530218727) ^ 1196882 = ((77577286 : ℕ) : ZMod 530218727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (530218727 - 1) / 1579 = 335794 from by norm_num]
      have h2 : (5 : ZMod 530218727) ^ 335794 = ((197830632 : ℕ) : ZMod 530218727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_41332144291 : Nat.Prime 41332144291 := by
  refine lucas_primality 41332144291 (2 : ZMod 41332144291) ?_ (fun q hq hd => ?_)
  · rw [show 41332144291 - 1 = 41332144290 from by norm_num]
    reduce_mod_char
  · have e : 41332144291 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 167 ^ 1, 1483 ^ 1, 5563 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 2 = 20666072145 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 20666072145 = ((41332144290 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 3 = 13777381430 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 13777381430 = ((928309824 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 5 = 8266428858 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 8266428858 = ((7076933841 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 167 = 247497870 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 247497870 = ((6531048668 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 1483 = 27870630 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 27870630 = ((9557088519 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (41332144291 - 1) / 5563 = 7429830 from by norm_num]
      have h2 : (2 : ZMod 41332144291) ^ 7429830 = ((20419183484 : ℕ) : ZMod 41332144291) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_226519873 : Nat.Prime 226519873 := by
  refine lucas_primality 226519873 (5 : ZMod 226519873) ?_ (fun q hq hd => ?_)
  · rw [show 226519873 - 1 = 226519872 from by norm_num]
    reduce_mod_char
  · have e : 226519873 - 1 = [2 ^ 6, 3 ^ 1, 43 ^ 1, 27437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226519873 - 1) / 2 = 113259936 from by norm_num]
      have h2 : (5 : ZMod 226519873) ^ 113259936 = ((226519872 : ℕ) : ZMod 226519873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226519873 - 1) / 3 = 75506624 from by norm_num]
      have h2 : (5 : ZMod 226519873) ^ 75506624 = ((111670496 : ℕ) : ZMod 226519873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226519873 - 1) / 43 = 5267904 from by norm_num]
      have h2 : (5 : ZMod 226519873) ^ 5267904 = ((188426655 : ℕ) : ZMod 226519873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (226519873 - 1) / 27437 = 8256 from by norm_num]
      have h2 : (5 : ZMod 226519873) ^ 8256 = ((147106458 : ℕ) : ZMod 226519873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37377454391 : Nat.Prime 37377454391 := by
  refine lucas_primality 37377454391 (7 : ZMod 37377454391) ?_ (fun q hq hd => ?_)
  · rw [show 37377454391 - 1 = 37377454390 from by norm_num]
    reduce_mod_char
  · have e : 37377454391 - 1 = [2 ^ 1, 5 ^ 1, 37 ^ 1, 7867 ^ 1, 12841 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37377454391 - 1) / 2 = 18688727195 from by norm_num]
      have h2 : (7 : ZMod 37377454391) ^ 18688727195 = ((37377454390 : ℕ) : ZMod 37377454391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37377454391 - 1) / 5 = 7475490878 from by norm_num]
      have h2 : (7 : ZMod 37377454391) ^ 7475490878 = ((31344616873 : ℕ) : ZMod 37377454391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37377454391 - 1) / 37 = 1010201470 from by norm_num]
      have h2 : (7 : ZMod 37377454391) ^ 1010201470 = ((30611053704 : ℕ) : ZMod 37377454391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37377454391 - 1) / 7867 = 4751170 from by norm_num]
      have h2 : (7 : ZMod 37377454391) ^ 4751170 = ((28946601146 : ℕ) : ZMod 37377454391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37377454391 - 1) / 12841 = 2910790 from by norm_num]
      have h2 : (7 : ZMod 37377454391) ^ 2910790 = ((27821943470 : ℕ) : ZMod 37377454391) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2317402172243 : Nat.Prime 2317402172243 := by
  refine lucas_primality 2317402172243 (2 : ZMod 2317402172243) ?_ (fun q hq hd => ?_)
  · rw [show 2317402172243 - 1 = 2317402172242 from by norm_num]
    reduce_mod_char
  · have e : 2317402172243 - 1 = [2 ^ 1, 31 ^ 1, 37377454391 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2317402172243 - 1) / 2 = 1158701086121 from by norm_num]
      have h2 : (2 : ZMod 2317402172243) ^ 1158701086121 = ((2317402172242 : ℕ) : ZMod 2317402172243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2317402172243 - 1) / 31 = 74754908782 from by norm_num]
      have h2 : (2 : ZMod 2317402172243) ^ 74754908782 = ((1704842330814 : ℕ) : ZMod 2317402172243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_37377454391).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2317402172243 - 1) / 37377454391 = 62 from by norm_num]
      have h2 : (2 : ZMod 2317402172243) ^ 62 = ((78011684072 : ℕ) : ZMod 2317402172243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1192464167514295068582330293 : Nat.Prime 1192464167514295068582330293 := by
  refine lucas_primality 1192464167514295068582330293 (2 : ZMod 1192464167514295068582330293) ?_ (fun q hq hd => ?_)
  · rw [show 1192464167514295068582330293 - 1 = 1192464167514295068582330292 from by norm_num]
    reduce_mod_char
  · have e : 1192464167514295068582330293 - 1 = [2 ^ 2, 67 ^ 1, 73 ^ 1, 89 ^ 1, 211 ^ 1, 1400599 ^ 1, 2317402172243 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 2 = 596232083757147534291165146 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 596232083757147534291165146 = ((1192464167514295068582330292 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 67 = 17797972649467090575855676 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 17797972649467090575855676 = ((1174923562558730414024231679 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 73 = 16335125582387603679210004 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 16335125582387603679210004 = ((645983843219933461790226403 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 89 = 13398473792295450208790228 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 13398473792295450208790228 = ((244143874555076386841272460 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 211 = 5651488945565379471954172 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 5651488945565379471954172 = ((1177183881631926012150217180 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 1400599 = 851395843859873574508 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 851395843859873574508 = ((1156911921064485321616570216 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2317402172243).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1192464167514295068582330293 - 1) / 2317402172243 = 514569366421244 from by norm_num]
      have h2 : (2 : ZMod 1192464167514295068582330293) ^ 514569366421244 = ((924474987332948612269127002 : ℕ) : ZMod 1192464167514295068582330293) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13634250449 : Nat.Prime 13634250449 := by
  refine lucas_primality 13634250449 (6 : ZMod 13634250449) ?_ (fun q hq hd => ?_)
  · rw [show 13634250449 - 1 = 13634250448 from by norm_num]
    reduce_mod_char
  · have e : 13634250449 - 1 = [2 ^ 4, 7 ^ 1, 13 ^ 1, 9364183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13634250449 - 1) / 2 = 6817125224 from by norm_num]
      have h2 : (6 : ZMod 13634250449) ^ 6817125224 = ((13634250448 : ℕ) : ZMod 13634250449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13634250449 - 1) / 7 = 1947750064 from by norm_num]
      have h2 : (6 : ZMod 13634250449) ^ 1947750064 = ((10788779366 : ℕ) : ZMod 13634250449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13634250449 - 1) / 13 = 1048788496 from by norm_num]
      have h2 : (6 : ZMod 13634250449) ^ 1048788496 = ((4917637132 : ℕ) : ZMod 13634250449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13634250449 - 1) / 9364183 = 1456 from by norm_num]
      have h2 : (6 : ZMod 13634250449) ^ 1456 = ((10319517865 : ℕ) : ZMod 13634250449) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_427133798066273 : Nat.Prime 427133798066273 := by
  refine lucas_primality 427133798066273 (3 : ZMod 427133798066273) ?_ (fun q hq hd => ?_)
  · rw [show 427133798066273 - 1 = 427133798066272 from by norm_num]
    reduce_mod_char
  · have e : 427133798066273 - 1 = [2 ^ 5, 11 ^ 1, 89 ^ 1, 13634250449 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (427133798066273 - 1) / 2 = 213566899033136 from by norm_num]
      have h2 : (3 : ZMod 427133798066273) ^ 213566899033136 = ((427133798066272 : ℕ) : ZMod 427133798066273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (427133798066273 - 1) / 11 = 38830345278752 from by norm_num]
      have h2 : (3 : ZMod 427133798066273) ^ 38830345278752 = ((161083543438178 : ℕ) : ZMod 427133798066273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (427133798066273 - 1) / 89 = 4799256158048 from by norm_num]
      have h2 : (3 : ZMod 427133798066273) ^ 4799256158048 = ((240977921278064 : ℕ) : ZMod 427133798066273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13634250449).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (427133798066273 - 1) / 13634250449 = 31328 from by norm_num]
      have h2 : (3 : ZMod 427133798066273) ^ 31328 = ((383546083009825 : ℕ) : ZMod 427133798066273) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17202806882978376014633 : Nat.Prime 17202806882978376014633 := by
  refine lucas_primality 17202806882978376014633 (3 : ZMod 17202806882978376014633) ?_ (fun q hq hd => ?_)
  · rw [show 17202806882978376014633 - 1 = 17202806882978376014632 from by norm_num]
    reduce_mod_char
  · have e : 17202806882978376014633 - 1 = [2 ^ 3, 19 ^ 1, 257 ^ 1, 1031 ^ 1, 427133798066273 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17202806882978376014633 - 1) / 2 = 8601403441489188007316 from by norm_num]
      have h2 : (3 : ZMod 17202806882978376014633) ^ 8601403441489188007316 = ((17202806882978376014632 : ℕ) : ZMod 17202806882978376014633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17202806882978376014633 - 1) / 19 = 905410888577809263928 from by norm_num]
      have h2 : (3 : ZMod 17202806882978376014633) ^ 905410888577809263928 = ((8968291708102088968120 : ℕ) : ZMod 17202806882978376014633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17202806882978376014633 - 1) / 257 = 66936991762561774376 from by norm_num]
      have h2 : (3 : ZMod 17202806882978376014633) ^ 66936991762561774376 = ((2834410095512496865225 : ℕ) : ZMod 17202806882978376014633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17202806882978376014633 - 1) / 1031 = 16685554687660888472 from by norm_num]
      have h2 : (3 : ZMod 17202806882978376014633) ^ 16685554687660888472 = ((12624008667655683171803 : ℕ) : ZMod 17202806882978376014633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_427133798066273).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17202806882978376014633 - 1) / 427133798066273 = 40274984 from by norm_num]
      have h2 : (3 : ZMod 17202806882978376014633) ^ 40274984 = ((3926947764222648411922 : ℕ) : ZMod 17202806882978376014633) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_138375299 : Nat.Prime 138375299 := by
  refine lucas_primality 138375299 (2 : ZMod 138375299) ?_ (fun q hq hd => ?_)
  · rw [show 138375299 - 1 = 138375298 from by norm_num]
    reduce_mod_char
  · have e : 138375299 - 1 = [2 ^ 1, 29 ^ 1, 191 ^ 1, 12491 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138375299 - 1) / 2 = 69187649 from by norm_num]
      have h2 : (2 : ZMod 138375299) ^ 69187649 = ((138375298 : ℕ) : ZMod 138375299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138375299 - 1) / 29 = 4771562 from by norm_num]
      have h2 : (2 : ZMod 138375299) ^ 4771562 = ((66316830 : ℕ) : ZMod 138375299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138375299 - 1) / 191 = 724478 from by norm_num]
      have h2 : (2 : ZMod 138375299) ^ 724478 = ((67838624 : ℕ) : ZMod 138375299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (138375299 - 1) / 12491 = 11078 from by norm_num]
      have h2 : (2 : ZMod 138375299) ^ 11078 = ((22825341 : ℕ) : ZMod 138375299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11623525117 : Nat.Prime 11623525117 := by
  refine lucas_primality 11623525117 (5 : ZMod 11623525117) ?_ (fun q hq hd => ?_)
  · rw [show 11623525117 - 1 = 11623525116 from by norm_num]
    reduce_mod_char
  · have e : 11623525117 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 138375299 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11623525117 - 1) / 2 = 5811762558 from by norm_num]
      have h2 : (5 : ZMod 11623525117) ^ 5811762558 = ((11623525116 : ℕ) : ZMod 11623525117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11623525117 - 1) / 3 = 3874508372 from by norm_num]
      have h2 : (5 : ZMod 11623525117) ^ 3874508372 = ((7861801425 : ℕ) : ZMod 11623525117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11623525117 - 1) / 7 = 1660503588 from by norm_num]
      have h2 : (5 : ZMod 11623525117) ^ 1660503588 = ((7558955525 : ℕ) : ZMod 11623525117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_138375299).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11623525117 - 1) / 138375299 = 84 from by norm_num]
      have h2 : (5 : ZMod 11623525117) ^ 84 = ((2470556800 : ℕ) : ZMod 11623525117) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_534682155383 : Nat.Prime 534682155383 := by
  refine lucas_primality 534682155383 (5 : ZMod 534682155383) ?_ (fun q hq hd => ?_)
  · rw [show 534682155383 - 1 = 534682155382 from by norm_num]
    reduce_mod_char
  · have e : 534682155383 - 1 = [2 ^ 1, 23 ^ 1, 11623525117 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534682155383 - 1) / 2 = 267341077691 from by norm_num]
      have h2 : (5 : ZMod 534682155383) ^ 267341077691 = ((534682155382 : ℕ) : ZMod 534682155383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534682155383 - 1) / 23 = 23247050234 from by norm_num]
      have h2 : (5 : ZMod 534682155383) ^ 23247050234 = ((368893746702 : ℕ) : ZMod 534682155383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11623525117).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (534682155383 - 1) / 11623525117 = 46 from by norm_num]
      have h2 : (5 : ZMod 534682155383) ^ 46 = ((140083716962 : ℕ) : ZMod 534682155383) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_46516486703 : Nat.Prime 46516486703 := by
  refine lucas_primality 46516486703 (5 : ZMod 46516486703) ?_ (fun q hq hd => ?_)
  · rw [show 46516486703 - 1 = 46516486702 from by norm_num]
    reduce_mod_char
  · have e : 46516486703 - 1 = [2 ^ 1, 7 ^ 1, 641 ^ 1, 5183473 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46516486703 - 1) / 2 = 23258243351 from by norm_num]
      have h2 : (5 : ZMod 46516486703) ^ 23258243351 = ((46516486702 : ℕ) : ZMod 46516486703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46516486703 - 1) / 7 = 6645212386 from by norm_num]
      have h2 : (5 : ZMod 46516486703) ^ 6645212386 = ((6511007914 : ℕ) : ZMod 46516486703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46516486703 - 1) / 641 = 72568622 from by norm_num]
      have h2 : (5 : ZMod 46516486703) ^ 72568622 = ((30060709117 : ℕ) : ZMod 46516486703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46516486703 - 1) / 5183473 = 8974 from by norm_num]
      have h2 : (5 : ZMod 46516486703) ^ 8974 = ((119905021 : ℕ) : ZMod 46516486703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_715722801240612811884999961 : Nat.Prime 715722801240612811884999961 := by
  refine lucas_primality 715722801240612811884999961 (13 : ZMod 715722801240612811884999961) ?_ (fun q hq hd => ?_)
  · rw [show 715722801240612811884999961 - 1 = 715722801240612811884999960 from by norm_num]
    reduce_mod_char
  · have e : 715722801240612811884999961 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 181 ^ 1, 293 ^ 1, 25127 ^ 1, 96221 ^ 1, 46516486703 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 2 = 357861400620306405942499980 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 357861400620306405942499980 = ((715722801240612811884999960 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 3 = 238574267080204270628333320 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 238574267080204270628333320 = ((463529849415279229284217236 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 5 = 143144560248122562376999992 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 143144560248122562376999992 = ((227574572774107874989032001 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 181 = 3954269620113882938591160 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 3954269620113882938591160 = ((346817378602747487257170830 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 293 = 2442739935974787753873720 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 2442739935974787753873720 = ((549481854631321497542980029 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 25127 = 28484212251387464157480 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 28484212251387464157480 = ((411522169066153601308992279 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 96221 = 7438322208671836832760 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 7438322208671836832760 = ((19539305436790304232288922 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_46516486703).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715722801240612811884999961 - 1) / 46516486703 = 15386432896585320 from by norm_num]
      have h2 : (13 : ZMod 715722801240612811884999961) ^ 15386432896585320 = ((122183501594385415975591979 : ℕ) : ZMod 715722801240612811884999961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_176349919 : Nat.Prime 176349919 := by
  refine lucas_primality 176349919 (15 : ZMod 176349919) ?_ (fun q hq hd => ?_)
  · rw [show 176349919 - 1 = 176349918 from by norm_num]
    reduce_mod_char
  · have e : 176349919 - 1 = [2 ^ 1, 3 ^ 1, 37 ^ 1, 191 ^ 1, 4159 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176349919 - 1) / 2 = 88174959 from by norm_num]
      have h2 : (15 : ZMod 176349919) ^ 88174959 = ((176349918 : ℕ) : ZMod 176349919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176349919 - 1) / 3 = 58783306 from by norm_num]
      have h2 : (15 : ZMod 176349919) ^ 58783306 = ((50657254 : ℕ) : ZMod 176349919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176349919 - 1) / 37 = 4766214 from by norm_num]
      have h2 : (15 : ZMod 176349919) ^ 4766214 = ((150381275 : ℕ) : ZMod 176349919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176349919 - 1) / 191 = 923298 from by norm_num]
      have h2 : (15 : ZMod 176349919) ^ 923298 = ((147450371 : ℕ) : ZMod 176349919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (176349919 - 1) / 4159 = 42402 from by norm_num]
      have h2 : (15 : ZMod 176349919) ^ 42402 = ((4719872 : ℕ) : ZMod 176349919) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8714655511 : Nat.Prime 8714655511 := by
  refine lucas_primality 8714655511 (6 : ZMod 8714655511) ?_ (fun q hq hd => ?_)
  · rw [show 8714655511 - 1 = 8714655510 from by norm_num]
    reduce_mod_char
  · have e : 8714655511 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 11 ^ 1, 37 ^ 1, 197 ^ 1, 3623 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 2 = 4357327755 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 4357327755 = ((8714655510 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 3 = 2904885170 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 2904885170 = ((4859644816 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 5 = 1742931102 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 1742931102 = ((3246248578 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 11 = 792241410 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 792241410 = ((8057741770 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 37 = 235531230 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 235531230 = ((7451329732 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 197 = 44236830 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 44236830 = ((6791403195 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8714655511 - 1) / 3623 = 2405370 from by norm_num]
      have h2 : (6 : ZMod 8714655511) ^ 2405370 = ((7242970787 : ℕ) : ZMod 8714655511) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem kill3_e41 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 41 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g33703 : 33703 ∈ P := S7 33703 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 33703 ∣ 1 + 3 ^ 41).trans hd)
  have g270547105429567 : 270547105429567 ∈ P := S7 270547105429567 prime_270547105429567 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 270547105429567 ∣ 1 + 3 ^ 41).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 33703 g33703 270547105429567 g270547105429567 (by norm_num) (by norm_num)
  omega

theorem kill3_e43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 43 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g82064241848634269407 : 82064241848634269407 ∈ P := S7 82064241848634269407 prime_82064241848634269407 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 82064241848634269407 ∣ 1 + 3 ^ 43).trans hd)
  have g5179 : 5179 ∈ P := S1 5179 (by norm_num) (by norm_num) (hnz (by norm_num)) 82064241848634269407 g82064241848634269407 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 5179 g5179 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5179 g5179 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e44 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 44 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 44).trans hd)
  have g2382953 : 2382953 ∈ P := S7 2382953 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2382953 ∣ 1 + 3 ^ 44).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 2382953 g2382953 (by norm_num) (by norm_num)
  omega

theorem kill3_e46 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 46 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12553493 : 12553493 ∈ P := S7 12553493 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 12553493 ∣ 1 + 3 ^ 46).trans hd)
  have g2092249 : 2092249 ∈ P := S1 2092249 (by norm_num) (by norm_num) (hnz (by norm_num)) 12553493 g12553493 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 46).trans hd) 2092249 g2092249 (by norm_num)

theorem kill3_e47 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 47 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g16921 : 16921 ∈ P := S7 16921 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 16921 ∣ 1 + 3 ^ 47).trans hd)
  have g8461 : 8461 ∈ P := S1 8461 (by norm_num) (by norm_num) (hnz (by norm_num)) 16921 g16921 (by norm_num)
  have g4231 : 4231 ∈ P := S1 4231 (by norm_num) (by norm_num) (hnz (by norm_num)) 8461 g8461 (by norm_num)
  exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 4231 g4231 (by norm_num)

theorem kill3_e49 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 49 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g857643277 : 857643277 ∈ P := S7 857643277 prime_857643277 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 857643277 ∣ 1 + 3 ^ 49).trans hd)
  have g428821639 : 428821639 ∈ P := S1 428821639 prime_428821639 (by norm_num) (hnz (by norm_num)) 857643277 g857643277 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 428821639 g428821639 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 428821639 g428821639 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e52 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 52 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2093124281 : 2093124281 ∈ P := S7 2093124281 prime_2093124281 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2093124281 ∣ 1 + 3 ^ 52).trans hd)
  have g348854047 : 348854047 ∈ P := S1 348854047 prime_348854047 (by norm_num) (hnz (by norm_num)) 2093124281 g2093124281 (by norm_num)
  have g83219 : 83219 ∈ P := S1 83219 (by norm_num) (by norm_num) (hnz (by norm_num)) 348854047 g348854047 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 83219 g83219 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 83219 g83219 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e53 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 53 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g78719947 : 78719947 ∈ P := S7 78719947 prime_78719947 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 78719947 ∣ 1 + 3 ^ 53).trans hd)
  have g19679987 : 19679987 ∈ P := S1 19679987 (by norm_num) (by norm_num) (hnz (by norm_num)) 78719947 g78719947 (by norm_num)
  have g1639999 : 1639999 ∈ P := S1 1639999 (by norm_num) (by norm_num) (hnz (by norm_num)) 19679987 g19679987 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1639999 g1639999 (by norm_num)

theorem kill3_e55 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 55 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g659671 : 659671 ∈ P := S7 659671 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 659671 ∣ 1 + 3 ^ 55).trans hd)
  have g6343 : 6343 ∈ P := S1 6343 (by norm_num) (by norm_num) (hnz (by norm_num)) 659671 g659671 (by norm_num)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 659671 g659671 6343 g6343 (by norm_num) (by norm_num)
  omega

theorem kill3_e57 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 57 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3079 : 3079 ∈ P := S7 3079 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3079 ∣ 1 + 3 ^ 57).trans hd)
  exact S8 7 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 7 ∣ 1 + 3 ^ 57).trans hd) 3079 g3079 (by norm_num)

theorem kill3_e58 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 58 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g12413 : 12413 ∈ P := S7 12413 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 12413 ∣ 1 + 3 ^ 58).trans hd)
  have g2069 : 2069 ∈ P := S1 2069 (by norm_num) (by norm_num) (hnz (by norm_num)) 12413 g12413 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 58).trans hd) 2069 g2069 (by norm_num)

theorem kill3_e59 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 59 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3187 : 3187 ∈ P := S7 3187 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3187 ∣ 1 + 3 ^ 59).trans hd)
  have g797 : 797 ∈ P := S1 797 (by norm_num) (by norm_num) (hnz (by norm_num)) 3187 g3187 (by norm_num)
  have g1108439448677340328268341 : 1108439448677340328268341 ∈ P := S7 1108439448677340328268341 prime_1108439448677340328268341 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1108439448677340328268341 ∣ 1 + 3 ^ 59).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 797 g797 1108439448677340328268341 g1108439448677340328268341 (by norm_num) (by norm_num)
  omega

theorem kill3_e61 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 61 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g86630432442539925437931403 : 86630432442539925437931403 ∈ P := S7 86630432442539925437931403 prime_86630432442539925437931403 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 86630432442539925437931403 ∣ 1 + 3 ^ 61).trans hd)
  have g346331 : 346331 ∈ P := S1 346331 (by norm_num) (by norm_num) (hnz (by norm_num)) 86630432442539925437931403 g86630432442539925437931403 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 346331 g346331 (by norm_num)

theorem kill3_e62 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 62 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1403808961 : 1403808961 ∈ P := S7 1403808961 prime_1403808961 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1403808961 ∣ 1 + 3 ^ 62).trans hd)
  have g701904481 : 701904481 ∈ P := S1 701904481 prime_701904481 (by norm_num) (hnz (by norm_num)) 1403808961 g1403808961 (by norm_num)
  have g350952241 : 350952241 ∈ P := S1 350952241 prime_350952241 (by norm_num) (hnz (by norm_num)) 701904481 g701904481 (by norm_num)
  have g175476121 : 175476121 ∈ P := S1 175476121 prime_175476121 (by norm_num) (hnz (by norm_num)) 350952241 g350952241 (by norm_num)
  have g2609 : 2609 ∈ P := S1 2609 (by norm_num) (by norm_num) (hnz (by norm_num)) 175476121 g175476121 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 62).trans hd) 2609 g2609 (by norm_num)

theorem kill3_e64 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 64 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1716841910146256242328924544641 : 1716841910146256242328924544641 ∈ P := S7 1716841910146256242328924544641 prime_1716841910146256242328924544641 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1716841910146256242328924544641 ∣ 1 + 3 ^ 64).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1716841910146256242328924544641 g1716841910146256242328924544641 (by norm_num)

theorem kill3_e65 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 65 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g105919308797935444986721 : 105919308797935444986721 ∈ P := S7 105919308797935444986721 prime_105919308797935444986721 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 105919308797935444986721 ∣ 1 + 3 ^ 65).trans hd)
  have g52959654398967722493361 : 52959654398967722493361 ∈ P := S1 52959654398967722493361 prime_52959654398967722493361 (by norm_num) (hnz (by norm_num)) 105919308797935444986721 g105919308797935444986721 (by norm_num)
  have g162739 : 162739 ∈ P := S1 162739 (by norm_num) (by norm_num) (hnz (by norm_num)) 52959654398967722493361 g52959654398967722493361 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 162739 g162739 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 162739 g162739 79 g79 (by norm_num) (by norm_num)
  omega

theorem kill3_e67 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 67 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5390821 : 5390821 ∈ P := S7 5390821 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5390821 ∣ 1 + 3 ^ 67).trans hd)
  have g2695411 : 2695411 ∈ P := S1 2695411 (by norm_num) (by norm_num) (hnz (by norm_num)) 5390821 g5390821 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2695411 g2695411 (by norm_num)
  have g15671 : 15671 ∈ P := S1 15671 (by norm_num) (by norm_num) (hnz (by norm_num)) 2695411 g2695411 (by norm_num)
  have g653 : 653 ∈ P := S1 653 (by norm_num) (by norm_num) (hnz (by norm_num)) 15671 g15671 (by norm_num)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 653 g653 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 109 g109 (by norm_num) (by norm_num)
  omega

theorem kill3_e68 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 68 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 68).trans hd)
  have g6458150122561 : 6458150122561 ∈ P := S7 6458150122561 prime_6458150122561 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6458150122561 ∣ 1 + 3 ^ 68).trans hd)
  have g75094768867 : 75094768867 ∈ P := S1 75094768867 prime_75094768867 (by norm_num) (hnz (by norm_num)) 6458150122561 g6458150122561 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 75094768867 g75094768867 (by norm_num) (by norm_num)
  omega

theorem kill3_e71 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 71 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2131 : 2131 ∈ P := S7 2131 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2131 ∣ 1 + 3 ^ 71).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2131 g2131 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 2131 g2131 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill3_e73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 73 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g439 : 439 ∈ P := S7 439 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 439 ∣ 1 + 3 ^ 73).trans hd)
  have g38488154120055537150068589763279 : 38488154120055537150068589763279 ∈ P := S7 38488154120055537150068589763279 prime_38488154120055537150068589763279 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 38488154120055537150068589763279 ∣ 1 + 3 ^ 73).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 439 g439 38488154120055537150068589763279 g38488154120055537150068589763279 (by norm_num) (by norm_num)
  omega

theorem kill3_e74 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 74 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g149 : 149 ∈ P := S7 149 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 149 ∣ 1 + 3 ^ 74).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 74).trans hd) 149 g149 (by norm_num)

theorem kill3_e76 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 76 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31769 : 31769 ∈ P := S7 31769 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 31769 ∣ 1 + 3 ^ 76).trans hd)
  have g353 : 353 ∈ P := S1 353 (by norm_num) (by norm_num) (hnz (by norm_num)) 31769 g31769 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 353 g353 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 31769 g31769 59 g59 (by norm_num) (by norm_num)
  omega

theorem kill3_e77 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 77 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56495392933101222275861053369 : 56495392933101222275861053369 ∈ P := S7 56495392933101222275861053369 prime_56495392933101222275861053369 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56495392933101222275861053369 ∣ 1 + 3 ^ 77).trans hd)
  have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 56495392933101222275861053369 g56495392933101222275861053369 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 56495392933101222275861053369 g56495392933101222275861053369 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e79 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 79 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g327220181191 : 327220181191 ∈ P := S7 327220181191 prime_327220181191 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 327220181191 ∣ 1 + 3 ^ 79).trans hd)
  have g12390949 : 12390949 ∈ P := S1 12390949 (by norm_num) (by norm_num) (hnz (by norm_num)) 327220181191 g327220181191 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 12390949 g12390949 (by norm_num)

theorem kill3_e82 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 82 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2088869 : 2088869 ∈ P := S7 2088869 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2088869 ∣ 1 + 3 ^ 82).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 82).trans hd) 2088869 g2088869 (by norm_num)

theorem kill3_e83 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 83 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g499 : 499 ∈ P := S7 499 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 499 ∣ 1 + 3 ^ 83).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

theorem kill3_e86 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 86 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g173 : 173 ∈ P := S7 173 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 173 ∣ 1 + 3 ^ 86).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 86).trans hd) 29 g29 (by norm_num)

theorem kill3_e89 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 89 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1125706177 : 1125706177 ∈ P := S7 1125706177 prime_1125706177 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1125706177 ∣ 1 + 3 ^ 89).trans hd)
  have g937 : 937 ∈ P := S1 937 (by norm_num) (by norm_num) (hnz (by norm_num)) 1125706177 g1125706177 (by norm_num)
  have g600697 : 600697 ∈ P := S1 600697 (by norm_num) (by norm_num) (hnz (by norm_num)) 1125706177 g1125706177 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 937 g937 600697 g600697 (by norm_num) (by norm_num)
  omega

theorem kill3_e91 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 91 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8737 : 8737 ∈ P := S7 8737 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8737 ∣ 1 + 3 ^ 91).trans hd)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 398581 ∣ 1 + 3 ^ 91).trans hd)
  have := S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 8737 g8737 398581 g398581 (by norm_num) (by norm_num)
  omega

theorem kill3_e92 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 92 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g743170846305411756447828504941347481129 : 743170846305411756447828504941347481129 ∈ P := S7 743170846305411756447828504941347481129 prime_743170846305411756447828504941347481129 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 743170846305411756447828504941347481129 ∣ 1 + 3 ^ 92).trans hd)
  exact S8 41 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 41 ∣ 1 + 3 ^ 92).trans hd) 743170846305411756447828504941347481129 g743170846305411756447828504941347481129 (by norm_num)

theorem kill3_e94 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 94 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g563838649753 : 563838649753 ∈ P := S7 563838649753 prime_563838649753 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 563838649753 ∣ 1 + 3 ^ 94).trans hd)
  have g31453679 : 31453679 ∈ P := S1 31453679 (by norm_num) (by norm_num) (hnz (by norm_num)) 563838649753 g563838649753 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 94).trans hd) 31453679 g31453679 (by norm_num)

theorem kill3_e95 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 95 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 61 ∣ 1 + 3 ^ 95).trans hd)
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2851 ∣ 1 + 3 ^ 95).trans hd)
  have := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 2851 g2851 (by norm_num) (by norm_num)
  omega

theorem kill3_e97 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 97 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g459991849 : 459991849 ∈ P := S7 459991849 prime_459991849 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 459991849 ∣ 1 + 3 ^ 97).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 459991849 g459991849 (by norm_num)

theorem kill3_e101 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 101 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g379963 : 379963 ∈ P := S7 379963 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 379963 ∣ 1 + 3 ^ 101).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 379963 g379963 (by norm_num)
  have g7307 : 7307 ∈ P := S1 7307 (by norm_num) (by norm_num) (hnz (by norm_num)) 379963 g379963 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 7307 g7307 (by norm_num) (by norm_num)
  omega

theorem kill3_e103 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 103 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3661040653 : 3661040653 ∈ P := S7 3661040653 prime_3661040653 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3661040653 ∣ 1 + 3 ^ 103).trans hd)
  have g38947241 : 38947241 ∈ P := S1 38947241 (by norm_num) (by norm_num) (hnz (by norm_num)) 3661040653 g3661040653 (by norm_num)
  have g6491207 : 6491207 ∈ P := S1 6491207 (by norm_num) (by norm_num) (hnz (by norm_num)) 38947241 g38947241 (by norm_num)
  have g881 : 881 ∈ P := S1 881 (by norm_num) (by norm_num) (hnz (by norm_num)) 6491207 g6491207 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 881 g881 (by norm_num)

theorem kill3_e106 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 106 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g90313 : 90313 ∈ P := S7 90313 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 90313 ∣ 1 + 3 ^ 106).trans hd)
  have g6451 : 6451 ∈ P := S1 6451 (by norm_num) (by norm_num) (hnz (by norm_num)) 90313 g90313 (by norm_num)
  have g1613 : 1613 ∈ P := S1 1613 (by norm_num) (by norm_num) (hnz (by norm_num)) 6451 g6451 (by norm_num)
  have g269 : 269 ∈ P := S1 269 (by norm_num) (by norm_num) (hnz (by norm_num)) 1613 g1613 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 106).trans hd) 269 g269 (by norm_num)

theorem kill3_e107 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 107 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g100153 : 100153 ∈ P := S7 100153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 100153 ∣ 1 + 3 ^ 107).trans hd)
  have g50077 : 50077 ∈ P := S1 50077 (by norm_num) (by norm_num) (hnz (by norm_num)) 100153 g100153 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 50077 g50077 (by norm_num)

theorem kill3_e109 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 109 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1992772009 : 1992772009 ∈ P := S7 1992772009 prime_1992772009 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1992772009 ∣ 1 + 3 ^ 109).trans hd)
  have g199277201 : 199277201 ∈ P := S1 199277201 prime_199277201 (by norm_num) (hnz (by norm_num)) 1992772009 g1992772009 (by norm_num)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 199277201 g199277201 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1992772009 g1992772009 439 g439 (by norm_num) (by norm_num)
  omega

theorem kill3_e113 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 113 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g362053 : 362053 ∈ P := S7 362053 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 362053 ∣ 1 + 3 ^ 113).trans hd)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (hnz (by norm_num)) 362053 g362053 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 362053 g362053 2351 g2351 (by norm_num) (by norm_num)
  omega

theorem kill3_e116 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 116 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 116).trans hd)
  have g233 : 233 ∈ P := S7 233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 233 ∣ 1 + 3 ^ 116).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 233 g233 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill3_e118 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 118 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19966781110160346782368664772328944885905284750420567849 : 19966781110160346782368664772328944885905284750420567849 ∈ P := S7 19966781110160346782368664772328944885905284750420567849 prime_19966781110160346782368664772328944885905284750420567849 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19966781110160346782368664772328944885905284750420567849 ∣ 1 + 3 ^ 118).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 118).trans hd) 19966781110160346782368664772328944885905284750420567849 g19966781110160346782368664772328944885905284750420567849 (by norm_num)

theorem kill3_e121 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 121 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g727 : 727 ∈ P := S7 727 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 727 ∣ 1 + 3 ^ 121).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 727 g727 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 727 g727 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill3_e122 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 122 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g262199473 : 262199473 ∈ P := S7 262199473 prime_262199473 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 262199473 ∣ 1 + 3 ^ 122).trans hd)
  have g418849 : 418849 ∈ P := S1 418849 (by norm_num) (by norm_num) (hnz (by norm_num)) 262199473 g262199473 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 122).trans hd) 418849 g418849 (by norm_num)

theorem kill3_e124 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 124 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g81516726600079249 : 81516726600079249 ∈ P := S7 81516726600079249 prime_81516726600079249 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 81516726600079249 ∣ 1 + 3 ^ 124).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 81516726600079249 g81516726600079249 (by norm_num)

theorem kill3_e127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 127 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g22861 : 22861 ∈ P := S7 22861 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 22861 ∣ 1 + 3 ^ 127).trans hd)
  have g52147471 : 52147471 ∈ P := S7 52147471 prime_52147471 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 52147471 ∣ 1 + 3 ^ 127).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 52147471 g52147471 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 22861 g22861 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill3_e128 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 128 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g275201 : 275201 ∈ P := S7 275201 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 275201 ∣ 1 + 3 ^ 128).trans hd)
  have g15289 : 15289 ∈ P := S1 15289 (by norm_num) (by norm_num) (hnz (by norm_num)) 275201 g275201 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 15289 g15289 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 15289 g15289 139 g139 (by norm_num) (by norm_num)
  omega

theorem kill3_e131 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 131 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g114742271896804438572098194909 : 114742271896804438572098194909 ∈ P := S7 114742271896804438572098194909 prime_114742271896804438572098194909 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 114742271896804438572098194909 ∣ 1 + 3 ^ 131).trans hd)
  have g18253 : 18253 ∈ P := S1 18253 (by norm_num) (by norm_num) (hnz (by norm_num)) 114742271896804438572098194909 g114742271896804438572098194909 (by norm_num)
  have g9127 : 9127 ∈ P := S1 9127 (by norm_num) (by norm_num) (hnz (by norm_num)) 18253 g18253 (by norm_num)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 9127 g9127 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 9127 g9127 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill3_e133 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 133 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 547 ∣ 1 + 3 ^ 133).trans hd)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g2851 : 2851 ∈ P := S7 2851 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2851 ∣ 1 + 3 ^ 133).trans hd)
  have := S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 2851 g2851 (by norm_num) (by norm_num)
  omega

theorem kill3_e134 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 134 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g269 : 269 ∈ P := S7 269 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 269 ∣ 1 + 3 ^ 134).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 134).trans hd) 269 g269 (by norm_num)

theorem kill3_e137 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 137 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g82093596209179 : 82093596209179 ∈ P := S7 82093596209179 prime_82093596209179 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 82093596209179 ∣ 1 + 3 ^ 137).trans hd)
  have g443 : 443 ∈ P := S1 443 (by norm_num) (by norm_num) (hnz (by norm_num)) 82093596209179 g82093596209179 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 443 g443 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 82093596209179 g82093596209179 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e139 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 139 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g26436515641 : 26436515641 ∈ P := S7 26436515641 prime_26436515641 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 26436515641 ∣ 1 + 3 ^ 139).trans hd)
  have g72907 : 72907 ∈ P := S1 72907 (by norm_num) (by norm_num) (hnz (by norm_num)) 26436515641 g26436515641 (by norm_num)
  have g181303 : 181303 ∈ P := S1 181303 (by norm_num) (by norm_num) (hnz (by norm_num)) 26436515641 g26436515641 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 181303 g181303 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 72907 g72907 131 g131 (by norm_num) (by norm_num)
  omega

theorem kill3_e142 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 142 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3672239816477 : 3672239816477 ∈ P := S7 3672239816477 prime_3672239816477 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3672239816477 ∣ 1 + 3 ^ 142).trans hd)
  have g6723719 : 6723719 ∈ P := S1 6723719 (by norm_num) (by norm_num) (hnz (by norm_num)) 3672239816477 g3672239816477 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 142).trans hd) 6723719 g6723719 (by norm_num)

theorem kill3_e143 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 143 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g53197 : 53197 ∈ P := S7 53197 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 53197 ∣ 1 + 3 ^ 143).trans hd)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 67 ∣ 1 + 3 ^ 143).trans hd) 53197 g53197 (by norm_num)

theorem kill3_e146 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 146 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g293 : 293 ∈ P := S7 293 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 293 ∣ 1 + 3 ^ 146).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)

theorem kill3_e148 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 148 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g410257 : 410257 ∈ P := S7 410257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 410257 ∣ 1 + 3 ^ 148).trans hd)
  have g205129 : 205129 ∈ P := S1 205129 (by norm_num) (by norm_num) (hnz (by norm_num)) 410257 g410257 (by norm_num)
  have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 205129 g205129 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 205129 g205129 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e149 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 149 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4482722618976860674653013440107317 : 4482722618976860674653013440107317 ∈ P := S7 4482722618976860674653013440107317 prime_4482722618976860674653013440107317 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4482722618976860674653013440107317 ∣ 1 + 3 ^ 149).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 4482722618976860674653013440107317 g4482722618976860674653013440107317 (by norm_num)
  have g525359 : 525359 ∈ P := S1 525359 (by norm_num) (by norm_num) (hnz (by norm_num)) 4482722618976860674653013440107317 g4482722618976860674653013440107317 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 525359 g525359 (by norm_num) (by norm_num)
  omega

theorem kill3_e151 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 151 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g472027 : 472027 ∈ P := S7 472027 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 472027 ∣ 1 + 3 ^ 151).trans hd)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 472027 g472027 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

theorem kill3_e157 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 157 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g252457 : 252457 ∈ P := S7 252457 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 252457 ∣ 1 + 3 ^ 157).trans hd)
  have g126229 : 126229 ∈ P := S1 126229 (by norm_num) (by norm_num) (hnz (by norm_num)) 252457 g252457 (by norm_num)
  have g159420524134654609 : 159420524134654609 ∈ P := S7 159420524134654609 prime_159420524134654609 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 159420524134654609 ∣ 1 + 3 ^ 157).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 126229 g126229 159420524134654609 g159420524134654609 (by norm_num) (by norm_num)
  omega

theorem kill3_e158 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 158 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g10393819190815276250780568850989337 : 10393819190815276250780568850989337 ∈ P := S7 10393819190815276250780568850989337 prime_10393819190815276250780568850989337 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 10393819190815276250780568850989337 ∣ 1 + 3 ^ 158).trans hd)
  exact S6 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 10393819190815276250780568850989337 g10393819190815276250780568850989337 (by norm_num)

theorem kill3_e163 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 163 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8483499631 : 8483499631 ∈ P := S7 8483499631 prime_8483499631 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8483499631 ∣ 1 + 3 ^ 163).trans hd)
  have g530218727 : 530218727 ∈ P := S1 530218727 prime_530218727 (by norm_num) (hnz (by norm_num)) 8483499631 g8483499631 (by norm_num)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 530218727 g530218727 (by norm_num)
  have g5197 : 5197 ∈ P := S1 5197 (by norm_num) (by norm_num) (hnz (by norm_num)) 530218727 g530218727 (by norm_num)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 5197 g5197 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 113 g113 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 109 g109 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e164 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 164 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S_sq hP hK E (c := 41) (by norm_num) (by norm_num) (hnz (by norm_num))
    ((((by norm_num : 41 * 41 ∣ 1 + 3 ^ 164).trans hd).mul_left _).mul_right _)

theorem kill3_e166 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 166 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2591261 : 2591261 ∈ P := S7 2591261 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2591261 ∣ 1 + 3 ^ 166).trans hd)
  have g359 : 359 ∈ P := S1 359 (by norm_num) (by norm_num) (hnz (by norm_num)) 2591261 g2591261 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 166).trans hd) 359 g359 (by norm_num)

theorem kill3_e167 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 167 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41332144291 : 41332144291 ∈ P := S7 41332144291 prime_41332144291 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41332144291 ∣ 1 + 3 ^ 167).trans hd)
  exact S6 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 41332144291 g41332144291 (by norm_num)

theorem kill3_e169 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 169 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4057 : 4057 ∈ P := S7 4057 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4057 ∣ 1 + 3 ^ 169).trans hd)
  have g2029 : 2029 ∈ P := S1 2029 (by norm_num) (by norm_num) (hnz (by norm_num)) 4057 g4057 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2029 g2029 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2029 g2029 29 g29 (by norm_num) (by norm_num)
  omega

theorem kill3_e172 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 172 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41 ∣ 1 + 3 ^ 172).trans hd)
  have g226519873 : 226519873 ∈ P := S7 226519873 prime_226519873 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 226519873 ∣ 1 + 3 ^ 172).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 226519873 g226519873 (by norm_num) (by norm_num)
  omega

theorem kill3_e173 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 173 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g993367 : 993367 ∈ P := S7 993367 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 993367 ∣ 1 + 3 ^ 173).trans hd)
  have g124171 : 124171 ∈ P := S1 124171 (by norm_num) (by norm_num) (hnz (by norm_num)) 993367 g993367 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 124171 g124171 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have g839 : 839 ∈ P := S1 839 (by norm_num) (by norm_num) (hnz (by norm_num)) 124171 g124171 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 839 g839 (by norm_num) (by norm_num)
  omega

theorem kill3_e178 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 178 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1192464167514295068582330293 : 1192464167514295068582330293 ∈ P := S7 1192464167514295068582330293 prime_1192464167514295068582330293 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1192464167514295068582330293 ∣ 1 + 3 ^ 178).trans hd)
  have g17202806882978376014633 : 17202806882978376014633 ∈ P := S1 17202806882978376014633 prime_17202806882978376014633 (by norm_num) (hnz (by norm_num)) 1192464167514295068582330293 g1192464167514295068582330293 (by norm_num)
  have g534682155383 : 534682155383 ∈ P := S1 534682155383 prime_534682155383 (by norm_num) (hnz (by norm_num)) 17202806882978376014633 g17202806882978376014633 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 534682155383 g534682155383 (by norm_num)

theorem kill3_e179 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 179 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3755779 : 3755779 ∈ P := S7 3755779 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3755779 ∣ 1 + 3 ^ 179).trans hd)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 3755779 g3755779 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3755779 g3755779 139 g139 (by norm_num) (by norm_num)
  omega

theorem kill3_e181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 181 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g715722801240612811884999961 : 715722801240612811884999961 ∈ P := S7 715722801240612811884999961 prime_715722801240612811884999961 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 715722801240612811884999961 ∣ 1 + 3 ^ 181).trans hd)
  have g34859507 : 34859507 ∈ P := S1 34859507 (by norm_num) (by norm_num) (hnz (by norm_num)) 715722801240612811884999961 g715722801240612811884999961 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 34859507 g34859507 (by norm_num)
  have g109 : 109 ∈ P := S1 109 (by norm_num) (by norm_num) (hnz (by norm_num)) 34859507 g34859507 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 109 g109 (by norm_num) (by norm_num)
  omega

theorem kill3_e188 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 188 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2563193 : 2563193 ∈ P := S7 2563193 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2563193 ∣ 1 + 3 ^ 188).trans hd)
  have g14731 : 14731 ∈ P := S1 14731 (by norm_num) (by norm_num) (hnz (by norm_num)) 2563193 g2563193 (by norm_num)
  have := S3 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2563193 g2563193 14731 g14731 (by norm_num) (by norm_num)
  omega

theorem kill3_e191 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 191 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g176349919 : 176349919 ∈ P := S7 176349919 prime_176349919 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 176349919 ∣ 1 + 3 ^ 191).trans hd)
  have g1102187 : 1102187 ∈ P := S1 1102187 (by norm_num) (by norm_num) (hnz (by norm_num)) 176349919 g176349919 (by norm_num)
  have g1733 : 1733 ∈ P := S1 1733 (by norm_num) (by norm_num) (hnz (by norm_num)) 1102187 g1102187 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 1733 g1733 (by norm_num)

theorem kill3_e193 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 193 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g167911 : 167911 ∈ P := S7 167911 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 167911 ∣ 1 + 3 ^ 193).trans hd)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 167911 g167911 (by norm_num)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 167911 g167911 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 139 g139 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill3_e194 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 194 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g389 : 389 ∈ P := S7 389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 389 ∣ 1 + 3 ^ 194).trans hd)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 1 + 3 ^ 194).trans hd) 389 g389 (by norm_num)

theorem kill3_e197 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 197 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8714655511 : 8714655511 ∈ P := S7 8714655511 prime_8714655511 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8714655511 ∣ 1 + 3 ^ 197).trans hd)
  have g9993871 : 9993871 ∈ P := S1 9993871 (by norm_num) (by norm_num) (hnz (by norm_num)) 8714655511 g8714655511 (by norm_num)
  have g89231 : 89231 ∈ P := S1 89231 (by norm_num) (by norm_num) (hnz (by norm_num)) 9993871 g9993871 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 89231 g89231 (by norm_num)

theorem kill3_e199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 199 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2389 : 2389 ∈ P := S7 2389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2389 ∣ 1 + 3 ^ 199).trans hd)
  have g239 : 239 ∈ P := S1 239 (by norm_num) (by norm_num) (hnz (by norm_num)) 2389 g2389 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2389 g2389 239 g239 (by norm_num) (by norm_num)
  omega

theorem core3_residues_200 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    e % 12 ≠ 6 ∧
    e % 16 ≠ 8 ∧
    e % 18 ≠ 9 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 28 ≠ 14 ∧
    e % 30 ≠ 15 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 40 ≠ 20 ∧
    e % 42 ≠ 21 ∧
    e % 44 ≠ 22 ∧
    e % 46 ≠ 23 ∧
    e % 50 ≠ 25 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 66 ≠ 33 ∧
    e % 68 ≠ 34 ∧
    e % 70 ≠ 35 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38 ∧
    e % 78 ≠ 39 ∧
    e % 82 ≠ 41 ∧
    e % 86 ≠ 43 ∧
    e % 88 ≠ 44 ∧
    e % 92 ≠ 46 ∧
    e % 94 ≠ 47 ∧
    e % 98 ≠ 49 ∧
    e % 104 ≠ 52 ∧
    e % 106 ≠ 53 ∧
    e % 110 ≠ 55 ∧
    e % 114 ≠ 57 ∧
    e % 116 ≠ 58 ∧
    e % 118 ≠ 59 ∧
    e % 122 ≠ 61 ∧
    e % 124 ≠ 62 ∧
    e % 128 ≠ 64 ∧
    e % 130 ≠ 65 ∧
    e % 134 ≠ 67 ∧
    e % 136 ≠ 68 ∧
    e % 142 ≠ 71 ∧
    e % 146 ≠ 73 ∧
    e % 148 ≠ 74 ∧
    e % 152 ≠ 76 ∧
    e % 154 ≠ 77 ∧
    e % 158 ≠ 79 ∧
    e % 164 ≠ 82 ∧
    e % 166 ≠ 83 ∧
    e % 172 ≠ 86 ∧
    e % 178 ≠ 89 ∧
    e % 182 ≠ 91 ∧
    e % 184 ≠ 92 ∧
    e % 188 ≠ 94 ∧
    e % 190 ≠ 95 ∧
    e % 194 ≠ 97 ∧
    e % 202 ≠ 101 ∧
    e % 206 ≠ 103 ∧
    e % 212 ≠ 106 ∧
    e % 214 ≠ 107 ∧
    e % 218 ≠ 109 ∧
    e % 226 ≠ 113 ∧
    e % 232 ≠ 116 ∧
    e % 236 ≠ 118 ∧
    e % 242 ≠ 121 ∧
    e % 244 ≠ 122 ∧
    e % 248 ≠ 124 ∧
    e % 254 ≠ 127 ∧
    e % 256 ≠ 128 ∧
    e % 262 ≠ 131 ∧
    e % 266 ≠ 133 ∧
    e % 268 ≠ 134 ∧
    e % 274 ≠ 137 ∧
    e % 278 ≠ 139 ∧
    e % 284 ≠ 142 ∧
    e % 286 ≠ 143 ∧
    e % 292 ≠ 146 ∧
    e % 296 ≠ 148 ∧
    e % 298 ≠ 149 ∧
    e % 302 ≠ 151 ∧
    e % 314 ≠ 157 ∧
    e % 316 ≠ 158 ∧
    e % 326 ≠ 163 ∧
    e % 328 ≠ 164 ∧
    e % 332 ≠ 166 ∧
    e % 334 ≠ 167 ∧
    e % 338 ≠ 169 ∧
    e % 344 ≠ 172 ∧
    e % 346 ≠ 173 ∧
    e % 356 ≠ 178 ∧
    e % 358 ≠ 179 ∧
    e % 362 ≠ 181 ∧
    e % 376 ≠ 188 ∧
    e % 382 ≠ 191 ∧
    e % 386 ≠ 193 ∧
    e % 388 ≠ 194 ∧
    e % 394 ≠ 197 ∧
    e % 398 ≠ 199 :=
  ⟨fun h => kill3_e6 hP E (one_add_pow_dvd_of_odd_mul (e0 := 6) (by omega)),
   fun h => kill3_e8 hP E (one_add_pow_dvd_of_odd_mul (e0 := 8) (by omega)),
   fun h => kill3_e9 hP E (one_add_pow_dvd_of_odd_mul (e0 := 9) (by omega)),
   fun h => kill3_e10 hP E (one_add_pow_dvd_of_odd_mul (e0 := 10) (by omega)),
   fun h => kill3_e12 hP E (one_add_pow_dvd_of_odd_mul (e0 := 12) (by omega)),
   fun h => kill3_e14 hP E (one_add_pow_dvd_of_odd_mul (e0 := 14) (by omega)),
   fun h => kill3_e15 hP E (one_add_pow_dvd_of_odd_mul (e0 := 15) (by omega)),
   fun h => kill3_e16 hP E (one_add_pow_dvd_of_odd_mul (e0 := 16) (by omega)),
   fun h => kill3_e17 hP E (one_add_pow_dvd_of_odd_mul (e0 := 17) (by omega)),
   fun h => kill3_e20 hP E (one_add_pow_dvd_of_odd_mul (e0 := 20) (by omega)),
   fun h => kill3_e21 hP E (one_add_pow_dvd_of_odd_mul (e0 := 21) (by omega)),
   fun h => kill3_e22 hP E (one_add_pow_dvd_of_odd_mul (e0 := 22) (by omega)),
   fun h => kill3_e23 hP E (one_add_pow_dvd_of_odd_mul (e0 := 23) (by omega)),
   fun h => kill3_e25 hP E (one_add_pow_dvd_of_odd_mul (e0 := 25) (by omega)),
   fun h => kill3_e26 hP E (one_add_pow_dvd_of_odd_mul (e0 := 26) (by omega)),
   fun h => kill3_e28 hP E (one_add_pow_dvd_of_odd_mul (e0 := 28) (by omega)),
   fun h => kill3_e29 hP E (one_add_pow_dvd_of_odd_mul (e0 := 29) (by omega)),
   fun h => kill3_e31 hP E (one_add_pow_dvd_of_odd_mul (e0 := 31) (by omega)),
   fun h => kill3_e32 hP E (one_add_pow_dvd_of_odd_mul (e0 := 32) (by omega)),
   fun h => kill3_e33 hP E (one_add_pow_dvd_of_odd_mul (e0 := 33) (by omega)),
   fun h => kill3_e34 hP E (one_add_pow_dvd_of_odd_mul (e0 := 34) (by omega)),
   fun h => kill3_e35 hP E (one_add_pow_dvd_of_odd_mul (e0 := 35) (by omega)),
   fun h => kill3_e37 hP E (one_add_pow_dvd_of_odd_mul (e0 := 37) (by omega)),
   fun h => kill3_e38 hP E (one_add_pow_dvd_of_odd_mul (e0 := 38) (by omega)),
   fun h => kill3_e39 hP E (one_add_pow_dvd_of_odd_mul (e0 := 39) (by omega)),
   fun h => kill3_e41 hP E (one_add_pow_dvd_of_odd_mul (e0 := 41) (by omega)),
   fun h => kill3_e43 hP E (one_add_pow_dvd_of_odd_mul (e0 := 43) (by omega)),
   fun h => kill3_e44 hP E (one_add_pow_dvd_of_odd_mul (e0 := 44) (by omega)),
   fun h => kill3_e46 hP E (one_add_pow_dvd_of_odd_mul (e0 := 46) (by omega)),
   fun h => kill3_e47 hP E (one_add_pow_dvd_of_odd_mul (e0 := 47) (by omega)),
   fun h => kill3_e49 hP E (one_add_pow_dvd_of_odd_mul (e0 := 49) (by omega)),
   fun h => kill3_e52 hP E (one_add_pow_dvd_of_odd_mul (e0 := 52) (by omega)),
   fun h => kill3_e53 hP E (one_add_pow_dvd_of_odd_mul (e0 := 53) (by omega)),
   fun h => kill3_e55 hP E (one_add_pow_dvd_of_odd_mul (e0 := 55) (by omega)),
   fun h => kill3_e57 hP E (one_add_pow_dvd_of_odd_mul (e0 := 57) (by omega)),
   fun h => kill3_e58 hP E (one_add_pow_dvd_of_odd_mul (e0 := 58) (by omega)),
   fun h => kill3_e59 hP E (one_add_pow_dvd_of_odd_mul (e0 := 59) (by omega)),
   fun h => kill3_e61 hP E (one_add_pow_dvd_of_odd_mul (e0 := 61) (by omega)),
   fun h => kill3_e62 hP E (one_add_pow_dvd_of_odd_mul (e0 := 62) (by omega)),
   fun h => kill3_e64 hP E (one_add_pow_dvd_of_odd_mul (e0 := 64) (by omega)),
   fun h => kill3_e65 hP E (one_add_pow_dvd_of_odd_mul (e0 := 65) (by omega)),
   fun h => kill3_e67 hP E (one_add_pow_dvd_of_odd_mul (e0 := 67) (by omega)),
   fun h => kill3_e68 hP E (one_add_pow_dvd_of_odd_mul (e0 := 68) (by omega)),
   fun h => kill3_e71 hP E (one_add_pow_dvd_of_odd_mul (e0 := 71) (by omega)),
   fun h => kill3_e73 hP E (one_add_pow_dvd_of_odd_mul (e0 := 73) (by omega)),
   fun h => kill3_e74 hP E (one_add_pow_dvd_of_odd_mul (e0 := 74) (by omega)),
   fun h => kill3_e76 hP E (one_add_pow_dvd_of_odd_mul (e0 := 76) (by omega)),
   fun h => kill3_e77 hP E (one_add_pow_dvd_of_odd_mul (e0 := 77) (by omega)),
   fun h => kill3_e79 hP E (one_add_pow_dvd_of_odd_mul (e0 := 79) (by omega)),
   fun h => kill3_e82 hP E (one_add_pow_dvd_of_odd_mul (e0 := 82) (by omega)),
   fun h => kill3_e83 hP E (one_add_pow_dvd_of_odd_mul (e0 := 83) (by omega)),
   fun h => kill3_e86 hP E (one_add_pow_dvd_of_odd_mul (e0 := 86) (by omega)),
   fun h => kill3_e89 hP E (one_add_pow_dvd_of_odd_mul (e0 := 89) (by omega)),
   fun h => kill3_e91 hP E (one_add_pow_dvd_of_odd_mul (e0 := 91) (by omega)),
   fun h => kill3_e92 hP E (one_add_pow_dvd_of_odd_mul (e0 := 92) (by omega)),
   fun h => kill3_e94 hP E (one_add_pow_dvd_of_odd_mul (e0 := 94) (by omega)),
   fun h => kill3_e95 hP E (one_add_pow_dvd_of_odd_mul (e0 := 95) (by omega)),
   fun h => kill3_e97 hP E (one_add_pow_dvd_of_odd_mul (e0 := 97) (by omega)),
   fun h => kill3_e101 hP E (one_add_pow_dvd_of_odd_mul (e0 := 101) (by omega)),
   fun h => kill3_e103 hP E (one_add_pow_dvd_of_odd_mul (e0 := 103) (by omega)),
   fun h => kill3_e106 hP E (one_add_pow_dvd_of_odd_mul (e0 := 106) (by omega)),
   fun h => kill3_e107 hP E (one_add_pow_dvd_of_odd_mul (e0 := 107) (by omega)),
   fun h => kill3_e109 hP E (one_add_pow_dvd_of_odd_mul (e0 := 109) (by omega)),
   fun h => kill3_e113 hP E (one_add_pow_dvd_of_odd_mul (e0 := 113) (by omega)),
   fun h => kill3_e116 hP E (one_add_pow_dvd_of_odd_mul (e0 := 116) (by omega)),
   fun h => kill3_e118 hP E (one_add_pow_dvd_of_odd_mul (e0 := 118) (by omega)),
   fun h => kill3_e121 hP E (one_add_pow_dvd_of_odd_mul (e0 := 121) (by omega)),
   fun h => kill3_e122 hP E (one_add_pow_dvd_of_odd_mul (e0 := 122) (by omega)),
   fun h => kill3_e124 hP E (one_add_pow_dvd_of_odd_mul (e0 := 124) (by omega)),
   fun h => kill3_e127 hP E (one_add_pow_dvd_of_odd_mul (e0 := 127) (by omega)),
   fun h => kill3_e128 hP E (one_add_pow_dvd_of_odd_mul (e0 := 128) (by omega)),
   fun h => kill3_e131 hP E (one_add_pow_dvd_of_odd_mul (e0 := 131) (by omega)),
   fun h => kill3_e133 hP E (one_add_pow_dvd_of_odd_mul (e0 := 133) (by omega)),
   fun h => kill3_e134 hP E (one_add_pow_dvd_of_odd_mul (e0 := 134) (by omega)),
   fun h => kill3_e137 hP E (one_add_pow_dvd_of_odd_mul (e0 := 137) (by omega)),
   fun h => kill3_e139 hP E (one_add_pow_dvd_of_odd_mul (e0 := 139) (by omega)),
   fun h => kill3_e142 hP E (one_add_pow_dvd_of_odd_mul (e0 := 142) (by omega)),
   fun h => kill3_e143 hP E (one_add_pow_dvd_of_odd_mul (e0 := 143) (by omega)),
   fun h => kill3_e146 hP E (one_add_pow_dvd_of_odd_mul (e0 := 146) (by omega)),
   fun h => kill3_e148 hP E (one_add_pow_dvd_of_odd_mul (e0 := 148) (by omega)),
   fun h => kill3_e149 hP E (one_add_pow_dvd_of_odd_mul (e0 := 149) (by omega)),
   fun h => kill3_e151 hP E (one_add_pow_dvd_of_odd_mul (e0 := 151) (by omega)),
   fun h => kill3_e157 hP E (one_add_pow_dvd_of_odd_mul (e0 := 157) (by omega)),
   fun h => kill3_e158 hP E (one_add_pow_dvd_of_odd_mul (e0 := 158) (by omega)),
   fun h => kill3_e163 hP E (one_add_pow_dvd_of_odd_mul (e0 := 163) (by omega)),
   fun h => kill3_e164 hP E (one_add_pow_dvd_of_odd_mul (e0 := 164) (by omega)),
   fun h => kill3_e166 hP E (one_add_pow_dvd_of_odd_mul (e0 := 166) (by omega)),
   fun h => kill3_e167 hP E (one_add_pow_dvd_of_odd_mul (e0 := 167) (by omega)),
   fun h => kill3_e169 hP E (one_add_pow_dvd_of_odd_mul (e0 := 169) (by omega)),
   fun h => kill3_e172 hP E (one_add_pow_dvd_of_odd_mul (e0 := 172) (by omega)),
   fun h => kill3_e173 hP E (one_add_pow_dvd_of_odd_mul (e0 := 173) (by omega)),
   fun h => kill3_e178 hP E (one_add_pow_dvd_of_odd_mul (e0 := 178) (by omega)),
   fun h => kill3_e179 hP E (one_add_pow_dvd_of_odd_mul (e0 := 179) (by omega)),
   fun h => kill3_e181 hP E (one_add_pow_dvd_of_odd_mul (e0 := 181) (by omega)),
   fun h => kill3_e188 hP E (one_add_pow_dvd_of_odd_mul (e0 := 188) (by omega)),
   fun h => kill3_e191 hP E (one_add_pow_dvd_of_odd_mul (e0 := 191) (by omega)),
   fun h => kill3_e193 hP E (one_add_pow_dvd_of_odd_mul (e0 := 193) (by omega)),
   fun h => kill3_e194 hP E (one_add_pow_dvd_of_odd_mul (e0 := 194) (by omega)),
   fun h => kill3_e197 hP E (one_add_pow_dvd_of_odd_mul (e0 := 197) (by omega)),
   fun h => kill3_e199 hP E (one_add_pow_dvd_of_odd_mul (e0 := 199) (by omega))⟩

theorem three_exponent_residues_200 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h3 : 3 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n.factorization 3 % 12 ≠ 6 ∧
    n.factorization 3 % 16 ≠ 8 ∧
    n.factorization 3 % 18 ≠ 9 ∧
    n.factorization 3 % 20 ≠ 10 ∧
    n.factorization 3 % 24 ≠ 12 ∧
    n.factorization 3 % 28 ≠ 14 ∧
    n.factorization 3 % 30 ≠ 15 ∧
    n.factorization 3 % 32 ≠ 16 ∧
    n.factorization 3 % 34 ≠ 17 ∧
    n.factorization 3 % 40 ≠ 20 ∧
    n.factorization 3 % 42 ≠ 21 ∧
    n.factorization 3 % 44 ≠ 22 ∧
    n.factorization 3 % 46 ≠ 23 ∧
    n.factorization 3 % 50 ≠ 25 ∧
    n.factorization 3 % 52 ≠ 26 ∧
    n.factorization 3 % 56 ≠ 28 ∧
    n.factorization 3 % 58 ≠ 29 ∧
    n.factorization 3 % 62 ≠ 31 ∧
    n.factorization 3 % 64 ≠ 32 ∧
    n.factorization 3 % 66 ≠ 33 ∧
    n.factorization 3 % 68 ≠ 34 ∧
    n.factorization 3 % 70 ≠ 35 ∧
    n.factorization 3 % 74 ≠ 37 ∧
    n.factorization 3 % 76 ≠ 38 ∧
    n.factorization 3 % 78 ≠ 39 ∧
    n.factorization 3 % 82 ≠ 41 ∧
    n.factorization 3 % 86 ≠ 43 ∧
    n.factorization 3 % 88 ≠ 44 ∧
    n.factorization 3 % 92 ≠ 46 ∧
    n.factorization 3 % 94 ≠ 47 ∧
    n.factorization 3 % 98 ≠ 49 ∧
    n.factorization 3 % 104 ≠ 52 ∧
    n.factorization 3 % 106 ≠ 53 ∧
    n.factorization 3 % 110 ≠ 55 ∧
    n.factorization 3 % 114 ≠ 57 ∧
    n.factorization 3 % 116 ≠ 58 ∧
    n.factorization 3 % 118 ≠ 59 ∧
    n.factorization 3 % 122 ≠ 61 ∧
    n.factorization 3 % 124 ≠ 62 ∧
    n.factorization 3 % 128 ≠ 64 ∧
    n.factorization 3 % 130 ≠ 65 ∧
    n.factorization 3 % 134 ≠ 67 ∧
    n.factorization 3 % 136 ≠ 68 ∧
    n.factorization 3 % 142 ≠ 71 ∧
    n.factorization 3 % 146 ≠ 73 ∧
    n.factorization 3 % 148 ≠ 74 ∧
    n.factorization 3 % 152 ≠ 76 ∧
    n.factorization 3 % 154 ≠ 77 ∧
    n.factorization 3 % 158 ≠ 79 ∧
    n.factorization 3 % 164 ≠ 82 ∧
    n.factorization 3 % 166 ≠ 83 ∧
    n.factorization 3 % 172 ≠ 86 ∧
    n.factorization 3 % 178 ≠ 89 ∧
    n.factorization 3 % 182 ≠ 91 ∧
    n.factorization 3 % 184 ≠ 92 ∧
    n.factorization 3 % 188 ≠ 94 ∧
    n.factorization 3 % 190 ≠ 95 ∧
    n.factorization 3 % 194 ≠ 97 ∧
    n.factorization 3 % 202 ≠ 101 ∧
    n.factorization 3 % 206 ≠ 103 ∧
    n.factorization 3 % 212 ≠ 106 ∧
    n.factorization 3 % 214 ≠ 107 ∧
    n.factorization 3 % 218 ≠ 109 ∧
    n.factorization 3 % 226 ≠ 113 ∧
    n.factorization 3 % 232 ≠ 116 ∧
    n.factorization 3 % 236 ≠ 118 ∧
    n.factorization 3 % 242 ≠ 121 ∧
    n.factorization 3 % 244 ≠ 122 ∧
    n.factorization 3 % 248 ≠ 124 ∧
    n.factorization 3 % 254 ≠ 127 ∧
    n.factorization 3 % 256 ≠ 128 ∧
    n.factorization 3 % 262 ≠ 131 ∧
    n.factorization 3 % 266 ≠ 133 ∧
    n.factorization 3 % 268 ≠ 134 ∧
    n.factorization 3 % 274 ≠ 137 ∧
    n.factorization 3 % 278 ≠ 139 ∧
    n.factorization 3 % 284 ≠ 142 ∧
    n.factorization 3 % 286 ≠ 143 ∧
    n.factorization 3 % 292 ≠ 146 ∧
    n.factorization 3 % 296 ≠ 148 ∧
    n.factorization 3 % 298 ≠ 149 ∧
    n.factorization 3 % 302 ≠ 151 ∧
    n.factorization 3 % 314 ≠ 157 ∧
    n.factorization 3 % 316 ≠ 158 ∧
    n.factorization 3 % 326 ≠ 163 ∧
    n.factorization 3 % 328 ≠ 164 ∧
    n.factorization 3 % 332 ≠ 166 ∧
    n.factorization 3 % 334 ≠ 167 ∧
    n.factorization 3 % 338 ≠ 169 ∧
    n.factorization 3 % 344 ≠ 172 ∧
    n.factorization 3 % 346 ≠ 173 ∧
    n.factorization 3 % 356 ≠ 178 ∧
    n.factorization 3 % 358 ≠ 179 ∧
    n.factorization 3 % 362 ≠ 181 ∧
    n.factorization 3 % 376 ≠ 188 ∧
    n.factorization 3 % 382 ≠ 191 ∧
    n.factorization 3 % 386 ≠ 193 ∧
    n.factorization 3 % 388 ≠ 194 ∧
    n.factorization 3 % 394 ≠ 197 ∧
    n.factorization 3 % 398 ≠ 199 := by
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h3, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  exact core3_residues_200 hP E

theorem exponent_sieve_200 (e : ℕ) (lo : 41 ≤ e) (hi : e ≤ 200)
    (h : e % 12 ≠ 6 ∧
    e % 16 ≠ 8 ∧
    e % 18 ≠ 9 ∧
    e % 20 ≠ 10 ∧
    e % 24 ≠ 12 ∧
    e % 28 ≠ 14 ∧
    e % 30 ≠ 15 ∧
    e % 32 ≠ 16 ∧
    e % 34 ≠ 17 ∧
    e % 40 ≠ 20 ∧
    e % 42 ≠ 21 ∧
    e % 44 ≠ 22 ∧
    e % 46 ≠ 23 ∧
    e % 50 ≠ 25 ∧
    e % 52 ≠ 26 ∧
    e % 56 ≠ 28 ∧
    e % 58 ≠ 29 ∧
    e % 62 ≠ 31 ∧
    e % 64 ≠ 32 ∧
    e % 66 ≠ 33 ∧
    e % 68 ≠ 34 ∧
    e % 70 ≠ 35 ∧
    e % 74 ≠ 37 ∧
    e % 76 ≠ 38 ∧
    e % 78 ≠ 39 ∧
    e % 82 ≠ 41 ∧
    e % 86 ≠ 43 ∧
    e % 88 ≠ 44 ∧
    e % 92 ≠ 46 ∧
    e % 94 ≠ 47 ∧
    e % 98 ≠ 49 ∧
    e % 104 ≠ 52 ∧
    e % 106 ≠ 53 ∧
    e % 110 ≠ 55 ∧
    e % 114 ≠ 57 ∧
    e % 116 ≠ 58 ∧
    e % 118 ≠ 59 ∧
    e % 122 ≠ 61 ∧
    e % 124 ≠ 62 ∧
    e % 128 ≠ 64 ∧
    e % 130 ≠ 65 ∧
    e % 134 ≠ 67 ∧
    e % 136 ≠ 68 ∧
    e % 142 ≠ 71 ∧
    e % 146 ≠ 73 ∧
    e % 148 ≠ 74 ∧
    e % 152 ≠ 76 ∧
    e % 154 ≠ 77 ∧
    e % 158 ≠ 79 ∧
    e % 164 ≠ 82 ∧
    e % 166 ≠ 83 ∧
    e % 172 ≠ 86 ∧
    e % 178 ≠ 89 ∧
    e % 182 ≠ 91 ∧
    e % 184 ≠ 92 ∧
    e % 188 ≠ 94 ∧
    e % 190 ≠ 95 ∧
    e % 194 ≠ 97 ∧
    e % 202 ≠ 101 ∧
    e % 206 ≠ 103 ∧
    e % 212 ≠ 106 ∧
    e % 214 ≠ 107 ∧
    e % 218 ≠ 109 ∧
    e % 226 ≠ 113 ∧
    e % 232 ≠ 116 ∧
    e % 236 ≠ 118 ∧
    e % 242 ≠ 121 ∧
    e % 244 ≠ 122 ∧
    e % 248 ≠ 124 ∧
    e % 254 ≠ 127 ∧
    e % 256 ≠ 128 ∧
    e % 262 ≠ 131 ∧
    e % 266 ≠ 133 ∧
    e % 268 ≠ 134 ∧
    e % 274 ≠ 137 ∧
    e % 278 ≠ 139 ∧
    e % 284 ≠ 142 ∧
    e % 286 ≠ 143 ∧
    e % 292 ≠ 146 ∧
    e % 296 ≠ 148 ∧
    e % 298 ≠ 149 ∧
    e % 302 ≠ 151 ∧
    e % 314 ≠ 157 ∧
    e % 316 ≠ 158 ∧
    e % 326 ≠ 163 ∧
    e % 328 ≠ 164 ∧
    e % 332 ≠ 166 ∧
    e % 334 ≠ 167 ∧
    e % 338 ≠ 169 ∧
    e % 344 ≠ 172 ∧
    e % 346 ≠ 173 ∧
    e % 356 ≠ 178 ∧
    e % 358 ≠ 179 ∧
    e % 362 ≠ 181 ∧
    e % 376 ≠ 188 ∧
    e % 382 ≠ 191 ∧
    e % 386 ≠ 193 ∧
    e % 388 ≠ 194 ∧
    e % 394 ≠ 197 ∧
    e % 398 ≠ 199) :
    e = 5 ∨ e = 7 ∨ e = 11 ∨ e = 13 ∨ e = 19 := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99⟩ := h
  interval_cases e
  · exact absurd rfl r25
  · exact absurd rfl r0
  · exact absurd rfl r26
  · exact absurd rfl r27
  · exact absurd rfl r2
  · exact absurd rfl r28
  · exact absurd rfl r29
  · exact absurd rfl r7
  · exact absurd rfl r30
  · exact absurd rfl r3
  · exact absurd rfl r8
  · exact absurd rfl r31
  · exact absurd rfl r32
  · exact absurd rfl r0
  · exact absurd rfl r33
  · exact absurd rfl r1
  · exact absurd rfl r34
  · exact absurd rfl r35
  · exact absurd rfl r36
  · exact absurd rfl r4
  · exact absurd rfl r37
  · exact absurd rfl r38
  · exact absurd rfl r2
  · exact absurd rfl r39
  · exact absurd rfl r40
  · exact absurd rfl r0
  · exact absurd rfl r41
  · exact absurd rfl r42
  · exact absurd rfl r12
  · exact absurd rfl r3
  · exact absurd rfl r43
  · exact absurd rfl r1
  · exact absurd rfl r44
  · exact absurd rfl r45
  · exact absurd rfl r6
  · exact absurd rfl r46
  · exact absurd rfl r47
  · exact absurd rfl r0
  · exact absurd rfl r48
  · exact absurd rfl r7
  · exact absurd rfl r2
  · exact absurd rfl r49
  · exact absurd rfl r50
  · exact absurd rfl r4
  · exact absurd rfl r8
  · exact absurd rfl r51
  · exact absurd rfl r16
  · exact absurd rfl r1
  · exact absurd rfl r52
  · exact absurd rfl r0
  · exact absurd rfl r53
  · exact absurd rfl r54
  · exact absurd rfl r17
  · exact absurd rfl r55
  · exact absurd rfl r56
  · exact absurd rfl r18
  · exact absurd rfl r57
  · exact absurd rfl r5
  · exact absurd rfl r2
  · exact absurd rfl r9
  · exact absurd rfl r58
  · exact absurd rfl r0
  · exact absurd rfl r59
  · exact absurd rfl r1
  · exact absurd rfl r6
  · exact absurd rfl r60
  · exact absurd rfl r61
  · exact absurd rfl r4
  · exact absurd rfl r62
  · exact absurd rfl r3
  · exact absurd rfl r22
  · exact absurd rfl r7
  · exact absurd rfl r63
  · exact absurd rfl r0
  · exact absurd rfl r12
  · exact absurd rfl r64
  · exact absurd rfl r2
  · exact absurd rfl r65
  · exact absurd rfl r8
  · exact absurd rfl r1
  · exact absurd rfl r66
  · exact absurd rfl r67
  · exact absurd rfl r25
  · exact absurd rfl r68
  · exact absurd rfl r13
  · exact absurd rfl r0
  · exact absurd rfl r69
  · exact absurd rfl r70
  · exact absurd rfl r26
  · exact absurd rfl r3
  · exact absurd rfl r71
  · exact absurd rfl r4
  · exact absurd rfl r72
  · exact absurd rfl r73
  · exact absurd rfl r2
  · exact absurd rfl r1
  · exact absurd rfl r74
  · exact absurd rfl r0
  · exact absurd rfl r75
  · exact absurd rfl r9
  · exact absurd rfl r29
  · exact absurd rfl r76
  · exact absurd rfl r77
  · exact absurd rfl r7
  · exact absurd rfl r16
  · exact absurd rfl r78
  · exact absurd rfl r10
  · exact absurd rfl r79
  · exact absurd rfl r80
  · exact absurd rfl r0
  · exact absurd rfl r81
  · exact absurd rfl r1
  · exact absurd rfl r2
  · exact absurd rfl r5
  · exact absurd rfl r17
  · exact absurd rfl r4
  · exact absurd rfl r82
  · exact absurd rfl r83
  · exact absurd rfl r32
  · exact absurd rfl r18
  · exact absurd rfl r12
  · exact absurd rfl r0
  · exact absurd rfl r84
  · exact absurd rfl r85
  · exact absurd rfl r6
  · exact absurd rfl r86
  · exact absurd rfl r87
  · exact absurd rfl r1
  · exact absurd rfl r88
  · exact absurd rfl r3
  · exact absurd rfl r2
  · exact absurd rfl r89
  · exact absurd rfl r90
  · exact absurd rfl r0
  · exact absurd rfl r13
  · exact absurd rfl r7
  · exact absurd rfl r36
  · exact absurd rfl r91
  · exact absurd rfl r92
  · exact absurd rfl r4
  · exact absurd rfl r93
  · exact absurd rfl r5
  · exact absurd rfl r37
  · exact absurd rfl r1
  · exact absurd rfl r22
  · exact absurd rfl r0
  · exact absurd rfl r8
  · exact absurd rfl r94
  · exact absurd rfl r2
  · exact absurd rfl r3
  · exact absurd rfl r95
  · exact absurd rfl r39
  · exact absurd rfl r96
  · exact absurd rfl r97
  · exact absurd rfl r6
  · exact absurd rfl r15
  · exact absurd rfl r98
  · exact absurd rfl r0
  · exact absurd rfl r99
  · exact absurd rfl r1

theorem three_exponent_cases_200 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3lo : 2 ≤ n.factorization 3) (h3hi : n.factorization 3 ≤ 200)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n = 90 ∨ n.factorization 3 = 5 ∨ n.factorization 3 = 7 ∨ n.factorization 3 = 11 ∨ n.factorization 3 = 13 ∨ n.factorization 3 = 19 := by
  by_cases hle : n.factorization 3 ≤ 40
  · rcases three_exponent_cases_forty h h3lo hle hs with h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  · have h3 : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
    exact Or.inr (exponent_sieve_200 _ (by omega) h3hi (three_exponent_residues_200 h h3 hs))

theorem two_pow_add_one_dvd_of_odd_mul {d m : ℕ} (h : m % (2 * d) = d) : 2 ^ d + 1 ∣ 2 ^ m + 1 := by
  have h1 := one_add_pow_dvd_of_odd_mul (z := 2) (e0 := d) (e := m) h
  rwa [add_comm 1 (2 ^ d), add_comm 1 (2 ^ m)] at h1

theorem kill2_d10 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 10 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S5 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 * 5 ∣ 2 ^ 10 + 1).trans hd)

theorem kill2_d12 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 12 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g241 : 241 ∈ P := S2 241 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 241 ∣ 2 ^ 12 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 241 g241 (by norm_num)

theorem kill2_d14 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 14 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g29 : 29 ∈ P := S2 29 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 29 ∣ 2 ^ 14 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 14 + 1).trans hd) 29 g29 (by norm_num)

theorem kill2_d18 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 18 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37 : 37 ∈ P := S2 37 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 37 ∣ 2 ^ 18 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 18 + 1).trans hd) 19 g19 (by norm_num)

theorem kill2_d20 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 20 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61681 : 61681 ∈ P := S2 61681 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 61681 ∣ 2 ^ 20 + 1).trans hd)
  have g30841 : 30841 ∈ P := S1 30841 (by norm_num) (by norm_num) (hnz (by norm_num)) 61681 g61681 (by norm_num)
  have g2203 : 2203 ∈ P := S1 2203 (by norm_num) (by norm_num) (hnz (by norm_num)) 30841 g30841 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 2203 g2203 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

theorem kill2_d22 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 22 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g397 : 397 ∈ P := S2 397 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 397 ∣ 2 ^ 22 + 1).trans hd)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 397 g397 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 22 + 1).trans hd) 199 g199 (by norm_num)

theorem kill2_d24 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 24 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g97 : 97 ∈ P := S2 97 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 97 ∣ 2 ^ 24 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill2_d25 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 25 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4051 : 4051 ∈ P := S2 4051 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4051 ∣ 2 ^ 25 + 1).trans hd)
  have g1013 : 1013 ∈ P := S1 1013 (by norm_num) (by norm_num) (hnz (by norm_num)) 4051 g4051 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1013 g1013 (by norm_num)

theorem kill2_d26 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 26 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g157 : 157 ∈ P := S2 157 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 157 ∣ 2 ^ 26 + 1).trans hd)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 157 g157 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 26 + 1).trans hd) 79 g79 (by norm_num)

theorem kill2_d27 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 27 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19 : 19 ∈ P := S2 19 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19 ∣ 2 ^ 27 + 1).trans hd)
  have g87211 : 87211 ∈ P := S2 87211 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 87211 ∣ 2 ^ 27 + 1).trans hd)
  have g21803 : 21803 ∈ P := S1 21803 (by norm_num) (by norm_num) (hnz (by norm_num)) 87211 g87211 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 21803 g21803 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 79 g79 (by norm_num) (by norm_num)
  omega

theorem kill2_d28 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 28 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15790321 : 15790321 ∈ P := S2 15790321 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15790321 ∣ 2 ^ 28 + 1).trans hd)
  have g5801 : 5801 ∈ P := S1 5801 (by norm_num) (by norm_num) (hnz (by norm_num)) 15790321 g15790321 (by norm_num)
  have g967 : 967 ∈ P := S1 967 (by norm_num) (by norm_num) (hnz (by norm_num)) 5801 g5801 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 967 g967 (by norm_num)

theorem kill2_d29 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 29 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59 : 59 ∈ P := S2 59 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 59 ∣ 2 ^ 29 + 1).trans hd)
  have g3033169 : 3033169 ∈ P := S2 3033169 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3033169 ∣ 2 ^ 29 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 3033169 g3033169 (by norm_num) (by norm_num)
  omega

theorem kill2_d32 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 32 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6700417 : 6700417 ∈ P := S2 6700417 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6700417 ∣ 2 ^ 32 + 1).trans hd)
  have g3350209 : 3350209 ∈ P := S1 3350209 (by norm_num) (by norm_num) (hnz (by norm_num)) 6700417 g6700417 (by norm_num)
  have g335021 : 335021 ∈ P := S1 335021 (by norm_num) (by norm_num) (hnz (by norm_num)) 3350209 g3350209 (by norm_num)
  have g55837 : 55837 ∈ P := S1 55837 (by norm_num) (by norm_num) (hnz (by norm_num)) 335021 g335021 (by norm_num)
  have g27919 : 27919 ∈ P := S1 27919 (by norm_num) (by norm_num) (hnz (by norm_num)) 55837 g55837 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3350209 g3350209 27919 g27919 (by norm_num) (by norm_num)
  omega

theorem kill2_d33 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 33 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g20857 : 20857 ∈ P := S2 20857 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20857 ∣ 2 ^ 33 + 1).trans hd)
  have g10429 : 10429 ∈ P := S1 10429 (by norm_num) (by norm_num) (hnz (by norm_num)) 20857 g20857 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 10429 g10429 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 10429 g10429 149 g149 (by norm_num) (by norm_num)
  omega

theorem kill2_d34 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 34 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g26317 : 26317 ∈ P := S2 26317 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 26317 ∣ 2 ^ 34 + 1).trans hd)
  have g13159 : 13159 ∈ P := S1 13159 (by norm_num) (by norm_num) (hnz (by norm_num)) 26317 g26317 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 34 + 1).trans hd) 13159 g13159 (by norm_num)

theorem kill2_d35 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 35 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 35 + 1).trans hd)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 35 + 1).trans hd) 43 g43 (by norm_num)

theorem kill2_d37 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 37 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1777 : 1777 ∈ P := S2 1777 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1777 ∣ 2 ^ 37 + 1).trans hd)
  have g25781083 : 25781083 ∈ P := S2 25781083 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 25781083 ∣ 2 ^ 37 + 1).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1777 g1777 25781083 g25781083 (by norm_num) (by norm_num)
  omega

theorem kill2_d38 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 38 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g229 : 229 ∈ P := S2 229 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 229 ∣ 2 ^ 38 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 38 + 1).trans hd) 229 g229 (by norm_num)

theorem kill2_d39 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 39 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 2 ^ 39 + 1).trans hd)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
  have g22366891 : 22366891 ∈ P := S2 22366891 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 22366891 ∣ 2 ^ 39 + 1).trans hd)
  have g10039 : 10039 ∈ P := S1 10039 (by norm_num) (by norm_num) (hnz (by norm_num)) 22366891 g22366891 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 10039 g10039 (by norm_num) (by norm_num)
  omega

theorem kill2_d45 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 45 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18837001 : 18837001 ∈ P := S2 18837001 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18837001 ∣ 2 ^ 45 + 1).trans hd)
  have g67759 : 67759 ∈ P := S1 67759 (by norm_num) (by norm_num) (hnz (by norm_num)) 18837001 g18837001 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 45 + 1).trans hd) 67759 g67759 (by norm_num)

theorem kill2_d46 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 46 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g277 : 277 ∈ P := S2 277 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 277 ∣ 2 ^ 46 + 1).trans hd)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 277 g277 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 46 + 1).trans hd) 139 g139 (by norm_num)

theorem kill2_d48 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 48 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g193 : 193 ∈ P := S2 193 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 193 ∣ 2 ^ 48 + 1).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill2_d51 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 51 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g307 : 307 ∈ P := S2 307 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 307 ∣ 2 ^ 51 + 1).trans hd)
  have g2857 : 2857 ∈ P := S2 2857 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2857 ∣ 2 ^ 51 + 1).trans hd)
  have g1429 : 1429 ∈ P := S1 1429 (by norm_num) (by norm_num) (hnz (by norm_num)) 2857 g2857 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 307 g307 1429 g1429 (by norm_num) (by norm_num)
  omega

theorem kill2_d52 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 52 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g858001 : 858001 ∈ P := S2 858001 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 858001 ∣ 2 ^ 52 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 858001 g858001 (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 52 + 1).trans hd) 67 g67 (by norm_num)

theorem kill2_d55 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 55 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S5 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 * 11 ∣ 2 ^ 55 + 1).trans hd)

theorem kill2_d56 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 56 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 56 + 1).trans hd)
  have g5153 : 5153 ∈ P := S2 5153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5153 ∣ 2 ^ 56 + 1).trans hd)
  have g859 : 859 ∈ P := S1 859 (by norm_num) (by norm_num) (hnz (by norm_num)) 5153 g5153 (by norm_num)
  have := S3 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 859 g859 (by norm_num) (by norm_num)
  omega

theorem kill2_d57 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 57 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g571 : 571 ∈ P := S2 571 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 571 ∣ 2 ^ 57 + 1).trans hd)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 57 + 1).trans hd)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hnz (by norm_num)) 174763 g174763 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 571 g571 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kill2_d59 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 59 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37171 : 37171 ∈ P := S2 37171 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 37171 ∣ 2 ^ 59 + 1).trans hd)
  have g9293 : 9293 ∈ P := S1 9293 (by norm_num) (by norm_num) (hnz (by norm_num)) 37171 g37171 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 9293 g9293 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

theorem kill2_d62 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 62 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5581 : 5581 ∈ P := S2 5581 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5581 ∣ 2 ^ 62 + 1).trans hd)
  have g2791 : 2791 ∈ P := S1 2791 (by norm_num) (by norm_num) (hnz (by norm_num)) 5581 g5581 (by norm_num)
  have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 2791 g2791 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 62 + 1).trans hd) 349 g349 (by norm_num)

theorem kill2_d63 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 63 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g19 : 19 ∈ P := S2 19 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 19 ∣ 2 ^ 63 + 1).trans hd)
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 63 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 5419 g5419 (by norm_num) (by norm_num)
  omega

theorem kill2_d64 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 64 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g274177 : 274177 ∈ P := S2 274177 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 274177 ∣ 2 ^ 64 + 1).trans hd)
  have g137089 : 137089 ∈ P := S1 137089 (by norm_num) (by norm_num) (hnz (by norm_num)) 274177 g274177 (by norm_num)
  have g13709 : 13709 ∈ P := S1 13709 (by norm_num) (by norm_num) (hnz (by norm_num)) 137089 g137089 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 137089 g137089 13709 g13709 (by norm_num) (by norm_num)
  omega

theorem kill2_d65 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 65 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g131 : 131 ∈ P := S2 131 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 131 ∣ 2 ^ 65 + 1).trans hd)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 65 + 1).trans hd) 131 g131 (by norm_num)

theorem kill2_d67 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 67 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g7327657 : 7327657 ∈ P := S2 7327657 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 7327657 ∣ 2 ^ 67 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 7327657 g7327657 (by norm_num)
  have g281833 : 281833 ∈ P := S1 281833 (by norm_num) (by norm_num) (hnz (by norm_num)) 7327657 g7327657 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 281833 g281833 (by norm_num) (by norm_num)
  omega

theorem kill2_d68 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 68 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  exact S5 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 * 17 ∣ 2 ^ 68 + 1).trans hd)

theorem kill2_d69 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 69 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g139 : 139 ∈ P := S2 139 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 139 ∣ 2 ^ 69 + 1).trans hd)
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 2 ^ 69 + 1).trans hd)
  have g5419 : 5419 ∈ P := S1 5419 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 139 g139 5419 g5419 (by norm_num) (by norm_num)
  omega

theorem kill2_d74 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 74 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g149 : 149 ∈ P := S2 149 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 149 ∣ 2 ^ 74 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 74 + 1).trans hd) 149 g149 (by norm_num)

theorem kill2_d76 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 76 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1217 : 1217 ∈ P := S2 1217 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1217 ∣ 2 ^ 76 + 1).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1217 g1217 (by norm_num)
  have g148961 : 148961 ∈ P := S2 148961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 148961 ∣ 2 ^ 76 + 1).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 148961 g148961 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill2_d77 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 77 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g617 : 617 ∈ P := S2 617 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 617 ∣ 2 ^ 77 + 1).trans hd)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g78233 : 78233 ∈ P := S2 78233 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 78233 ∣ 2 ^ 77 + 1).trans hd)
  have := S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 78233 g78233 (by norm_num) (by norm_num)
  omega

theorem kill2_d80 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 80 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 80 + 1).trans hd)
  have g414721 : 414721 ∈ P := S2 414721 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 414721 ∣ 2 ^ 80 + 1).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 414721 g414721 (by norm_num) (by norm_num)
  omega

theorem kill2_d82 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 82 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g10169 : 10169 ∈ P := S2 10169 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 10169 ∣ 2 ^ 82 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 82 + 1).trans hd) 10169 g10169 (by norm_num)

theorem kill2_d83 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 83 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g499 : 499 ∈ P := S2 499 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 499 ∣ 2 ^ 83 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

theorem kill2_d85 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 85 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 85 + 1).trans hd)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 85 + 1).trans hd) 43691 g43691 (by norm_num)

theorem kill2_d86 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 86 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g173 : 173 ∈ P := S2 173 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 173 ∣ 2 ^ 86 + 1).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 173 g173 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 86 + 1).trans hd) 29 g29 (by norm_num)

theorem kill2_d91 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 91 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g224771 : 224771 ∈ P := S2 224771 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 224771 ∣ 2 ^ 91 + 1).trans hd)
  have g18731 : 18731 ∈ P := S1 18731 (by norm_num) (by norm_num) (hnz (by norm_num)) 224771 g224771 (by norm_num)
  have g223 : 223 ∈ P := S1 223 (by norm_num) (by norm_num) (hnz (by norm_num)) 18731 g18731 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 18731 g18731 223 g223 (by norm_num) (by norm_num)
  omega

theorem kill2_d94 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 94 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3761 : 3761 ∈ P := S2 3761 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3761 ∣ 2 ^ 94 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 3761 g3761 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 94 + 1).trans hd) 19 g19 (by norm_num)

theorem kill2_d95 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 95 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2281 : 2281 ∈ P := S2 2281 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2281 ∣ 2 ^ 95 + 1).trans hd)
  have g163 : 163 ∈ P := S1 163 (by norm_num) (by norm_num) (hnz (by norm_num)) 2281 g2281 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 163 g163 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2281 g2281 41 g41 (by norm_num) (by norm_num)
  omega

theorem kill2_d97 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 97 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1553 : 1553 ∈ P := S2 1553 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1553 ∣ 2 ^ 97 + 1).trans hd)
  have g31817 : 31817 ∈ P := S2 31817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 31817 ∣ 2 ^ 97 + 1).trans hd)
  have g5303 : 5303 ∈ P := S1 5303 (by norm_num) (by norm_num) (hnz (by norm_num)) 31817 g31817 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 5303 g5303 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 1553 g1553 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill2_d106 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 106 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15358129 : 15358129 ∈ P := S2 15358129 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15358129 ∣ 2 ^ 106 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 106 + 1).trans hd) 15358129 g15358129 (by norm_num)

theorem kill2_d112 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 112 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g449 : 449 ∈ P := S2 449 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 449 ∣ 2 ^ 112 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)

theorem kill2_d115 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 115 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 2 ^ 115 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  exact S4 11 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 11 ∣ 2 ^ 115 + 1).trans hd) 43 g43 (by norm_num)

theorem kill2_d116 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 116 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59393 : 59393 ∈ P := S2 59393 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 59393 ∣ 2 ^ 116 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 59393 g59393 (by norm_num)
  have g521 : 521 ∈ P := S1 521 (by norm_num) (by norm_num) (hnz (by norm_num)) 59393 g59393 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 521 g521 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 29 g29 (by norm_num) (by norm_num)
  omega

theorem kill2_d118 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 118 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1181 : 1181 ∈ P := S2 1181 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1181 ∣ 2 ^ 118 + 1).trans hd)
  have g197 : 197 ∈ P := S1 197 (by norm_num) (by norm_num) (hnz (by norm_num)) 1181 g1181 (by norm_num)
  have g3541 : 3541 ∈ P := S2 3541 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3541 ∣ 2 ^ 118 + 1).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 197 g197 3541 g3541 (by norm_num) (by norm_num)
  omega

theorem kill2_d119 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 119 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 119 + 1).trans hd)
  have g43691 : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 119 + 1).trans hd)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kill2_d121 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 121 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g683 : 683 ∈ P := S2 683 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 683 ∣ 2 ^ 121 + 1).trans hd)
  have g117371 : 117371 ∈ P := S2 117371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 117371 ∣ 2 ^ 121 + 1).trans hd)
  have g9781 : 9781 ∈ P := S1 9781 (by norm_num) (by norm_num) (hnz (by norm_num)) 117371 g117371 (by norm_num)
  have g73 : 73 ∈ P := S1 73 (by norm_num) (by norm_num) (hnz (by norm_num)) 9781 g9781 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 73 g73 (by norm_num)
  have := S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 37 g37 (by norm_num) (by norm_num)
  omega

theorem kill2_d122 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 122 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1709 : 1709 ∈ P := S2 1709 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1709 ∣ 2 ^ 122 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 122 + 1).trans hd) 1709 g1709 (by norm_num)

theorem kill2_d123 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 123 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g739 : 739 ∈ P := S2 739 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 739 ∣ 2 ^ 123 + 1).trans hd)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 739 g739 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 739 g739 19 g19 (by norm_num) (by norm_num)
  omega

theorem kill2_d124 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 124 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g290657 : 290657 ∈ P := S2 290657 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 290657 ∣ 2 ^ 124 + 1).trans hd)
  have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 290657 g290657 (by norm_num)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 193 g193 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)

theorem kill2_d131 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 131 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1049 : 1049 ∈ P := S2 1049 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1049 ∣ 2 ^ 131 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1049 g1049 (by norm_num)

theorem kill2_d133 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 133 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 133 + 1).trans hd)
  have g174763 : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 133 + 1).trans hd)
  have g43691 : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hnz (by norm_num)) 174763 g174763 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 43691 g43691 (by norm_num) (by norm_num)
  omega

theorem kill2_d134 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 134 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g269 : 269 ∈ P := S2 269 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 269 ∣ 2 ^ 134 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 134 + 1).trans hd) 269 g269 (by norm_num)

theorem kill2_d141 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 141 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1681003 : 1681003 ∈ P := S2 1681003 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1681003 ∣ 2 ^ 141 + 1).trans hd)
  have g32327 : 32327 ∈ P := S1 32327 (by norm_num) (by norm_num) (hnz (by norm_num)) 1681003 g1681003 (by norm_num)
  have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (hnz (by norm_num)) 32327 g32327 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 449 g449 (by norm_num)

theorem kill2_d142 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 142 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g569 : 569 ∈ P := S2 569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 569 ∣ 2 ^ 142 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 142 + 1).trans hd) 569 g569 (by norm_num)

theorem kill2_d143 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 143 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2731 ∣ 2 ^ 143 + 1).trans hd)
  exact S4 683 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 683 ∣ 2 ^ 143 + 1).trans hd) 2731 g2731 (by norm_num)

theorem kill2_d146 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 146 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g293 : 293 ∈ P := S2 293 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 293 ∣ 2 ^ 146 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 293 g293 (by norm_num)

theorem kill2_d147 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 147 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 147 + 1).trans hd)
  have g748819 : 748819 ∈ P := S2 748819 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 748819 ∣ 2 ^ 147 + 1).trans hd)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 748819 g748819 (by norm_num) (by norm_num)
  omega

theorem kill2_d149 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 149 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1193 : 1193 ∈ P := S2 1193 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1193 ∣ 2 ^ 149 + 1).trans hd)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 1193 g1193 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

theorem kill2_d152 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 152 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 152 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g27361 : 27361 ∈ P := S2 27361 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 27361 ∣ 2 ^ 152 + 1).trans hd)
  have g13681 : 13681 ∈ P := S1 13681 (by norm_num) (by norm_num) (hnz (by norm_num)) 27361 g27361 (by norm_num)
  have g6841 : 6841 ∈ P := S1 6841 (by norm_num) (by norm_num) (hnz (by norm_num)) 13681 g13681 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 6841 g6841 (by norm_num) (by norm_num)
  omega

theorem kill2_d155 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 155 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g11161 : 11161 ∈ P := S2 11161 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11161 ∣ 2 ^ 155 + 1).trans hd)
  have g5581 : 5581 ∈ P := S1 5581 (by norm_num) (by norm_num) (hnz (by norm_num)) 11161 g11161 (by norm_num)
  have g2791 : 2791 ∈ P := S1 2791 (by norm_num) (by norm_num) (hnz (by norm_num)) 5581 g5581 (by norm_num)
  have g349 : 349 ∈ P := S1 349 (by norm_num) (by norm_num) (hnz (by norm_num)) 2791 g2791 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 349 g349 (by norm_num)

theorem kill2_d157 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 157 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g15073 : 15073 ∈ P := S2 15073 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15073 ∣ 2 ^ 157 + 1).trans hd)
  have g7537 : 7537 ∈ P := S1 7537 (by norm_num) (by norm_num) (hnz (by norm_num)) 15073 g15073 (by norm_num)
  have g3769 : 3769 ∈ P := S1 3769 (by norm_num) (by norm_num) (hnz (by norm_num)) 7537 g7537 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 (by norm_num)
  have := S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 3769 g3769 29 g29 (by norm_num) (by norm_num)
  omega

theorem core3_two_adic_residues {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p) :
    m % 20 ≠ 10 ∧
    m % 24 ≠ 12 ∧
    m % 28 ≠ 14 ∧
    m % 36 ≠ 18 ∧
    m % 40 ≠ 20 ∧
    m % 44 ≠ 22 ∧
    m % 48 ≠ 24 ∧
    m % 50 ≠ 25 ∧
    m % 52 ≠ 26 ∧
    m % 54 ≠ 27 ∧
    m % 56 ≠ 28 ∧
    m % 58 ≠ 29 ∧
    m % 64 ≠ 32 ∧
    m % 66 ≠ 33 ∧
    m % 68 ≠ 34 ∧
    m % 70 ≠ 35 ∧
    m % 74 ≠ 37 ∧
    m % 76 ≠ 38 ∧
    m % 78 ≠ 39 ∧
    m % 90 ≠ 45 ∧
    m % 92 ≠ 46 ∧
    m % 96 ≠ 48 ∧
    m % 102 ≠ 51 ∧
    m % 104 ≠ 52 ∧
    m % 110 ≠ 55 ∧
    m % 112 ≠ 56 ∧
    m % 114 ≠ 57 ∧
    m % 118 ≠ 59 ∧
    m % 124 ≠ 62 ∧
    m % 126 ≠ 63 ∧
    m % 128 ≠ 64 ∧
    m % 130 ≠ 65 ∧
    m % 134 ≠ 67 ∧
    m % 136 ≠ 68 ∧
    m % 138 ≠ 69 ∧
    m % 148 ≠ 74 ∧
    m % 152 ≠ 76 ∧
    m % 154 ≠ 77 ∧
    m % 160 ≠ 80 ∧
    m % 164 ≠ 82 ∧
    m % 166 ≠ 83 ∧
    m % 170 ≠ 85 ∧
    m % 172 ≠ 86 ∧
    m % 182 ≠ 91 ∧
    m % 188 ≠ 94 ∧
    m % 190 ≠ 95 ∧
    m % 194 ≠ 97 ∧
    m % 212 ≠ 106 ∧
    m % 224 ≠ 112 ∧
    m % 230 ≠ 115 ∧
    m % 232 ≠ 116 ∧
    m % 236 ≠ 118 ∧
    m % 238 ≠ 119 ∧
    m % 242 ≠ 121 ∧
    m % 244 ≠ 122 ∧
    m % 246 ≠ 123 ∧
    m % 248 ≠ 124 ∧
    m % 262 ≠ 131 ∧
    m % 266 ≠ 133 ∧
    m % 268 ≠ 134 ∧
    m % 282 ≠ 141 ∧
    m % 284 ≠ 142 ∧
    m % 286 ≠ 143 ∧
    m % 292 ≠ 146 ∧
    m % 294 ≠ 147 ∧
    m % 298 ≠ 149 ∧
    m % 304 ≠ 152 ∧
    m % 310 ≠ 155 ∧
    m % 314 ≠ 157 :=
  ⟨fun h => kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega)),
   fun h => kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega)),
   fun h => kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega)),
   fun h => kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega)),
   fun h => kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega)),
   fun h => kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega)),
   fun h => kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega)),
   fun h => kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega)),
   fun h => kill2_d26 hP E (two_pow_add_one_dvd_of_odd_mul (d := 26) (by omega)),
   fun h => kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega)),
   fun h => kill2_d28 hP E (two_pow_add_one_dvd_of_odd_mul (d := 28) (by omega)),
   fun h => kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega)),
   fun h => kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega)),
   fun h => kill2_d33 hP E (two_pow_add_one_dvd_of_odd_mul (d := 33) (by omega)),
   fun h => kill2_d34 hP E (two_pow_add_one_dvd_of_odd_mul (d := 34) (by omega)),
   fun h => kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega)),
   fun h => kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega)),
   fun h => kill2_d38 hP E (two_pow_add_one_dvd_of_odd_mul (d := 38) (by omega)),
   fun h => kill2_d39 hP E (two_pow_add_one_dvd_of_odd_mul (d := 39) (by omega)),
   fun h => kill2_d45 hP E (two_pow_add_one_dvd_of_odd_mul (d := 45) (by omega)),
   fun h => kill2_d46 hP E (two_pow_add_one_dvd_of_odd_mul (d := 46) (by omega)),
   fun h => kill2_d48 hP E (two_pow_add_one_dvd_of_odd_mul (d := 48) (by omega)),
   fun h => kill2_d51 hP E (two_pow_add_one_dvd_of_odd_mul (d := 51) (by omega)),
   fun h => kill2_d52 hP E (two_pow_add_one_dvd_of_odd_mul (d := 52) (by omega)),
   fun h => kill2_d55 hP E (two_pow_add_one_dvd_of_odd_mul (d := 55) (by omega)),
   fun h => kill2_d56 hP E (two_pow_add_one_dvd_of_odd_mul (d := 56) (by omega)),
   fun h => kill2_d57 hP E (two_pow_add_one_dvd_of_odd_mul (d := 57) (by omega)),
   fun h => kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega)),
   fun h => kill2_d62 hP E (two_pow_add_one_dvd_of_odd_mul (d := 62) (by omega)),
   fun h => kill2_d63 hP E (two_pow_add_one_dvd_of_odd_mul (d := 63) (by omega)),
   fun h => kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega)),
   fun h => kill2_d65 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65) (by omega)),
   fun h => kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega)),
   fun h => kill2_d68 hP E (two_pow_add_one_dvd_of_odd_mul (d := 68) (by omega)),
   fun h => kill2_d69 hP E (two_pow_add_one_dvd_of_odd_mul (d := 69) (by omega)),
   fun h => kill2_d74 hP E (two_pow_add_one_dvd_of_odd_mul (d := 74) (by omega)),
   fun h => kill2_d76 hP E (two_pow_add_one_dvd_of_odd_mul (d := 76) (by omega)),
   fun h => kill2_d77 hP E (two_pow_add_one_dvd_of_odd_mul (d := 77) (by omega)),
   fun h => kill2_d80 hP E (two_pow_add_one_dvd_of_odd_mul (d := 80) (by omega)),
   fun h => kill2_d82 hP E (two_pow_add_one_dvd_of_odd_mul (d := 82) (by omega)),
   fun h => kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega)),
   fun h => kill2_d85 hP E (two_pow_add_one_dvd_of_odd_mul (d := 85) (by omega)),
   fun h => kill2_d86 hP E (two_pow_add_one_dvd_of_odd_mul (d := 86) (by omega)),
   fun h => kill2_d91 hP E (two_pow_add_one_dvd_of_odd_mul (d := 91) (by omega)),
   fun h => kill2_d94 hP E (two_pow_add_one_dvd_of_odd_mul (d := 94) (by omega)),
   fun h => kill2_d95 hP E (two_pow_add_one_dvd_of_odd_mul (d := 95) (by omega)),
   fun h => kill2_d97 hP E (two_pow_add_one_dvd_of_odd_mul (d := 97) (by omega)),
   fun h => kill2_d106 hP E (two_pow_add_one_dvd_of_odd_mul (d := 106) (by omega)),
   fun h => kill2_d112 hP E (two_pow_add_one_dvd_of_odd_mul (d := 112) (by omega)),
   fun h => kill2_d115 hP E (two_pow_add_one_dvd_of_odd_mul (d := 115) (by omega)),
   fun h => kill2_d116 hP E (two_pow_add_one_dvd_of_odd_mul (d := 116) (by omega)),
   fun h => kill2_d118 hP E (two_pow_add_one_dvd_of_odd_mul (d := 118) (by omega)),
   fun h => kill2_d119 hP E (two_pow_add_one_dvd_of_odd_mul (d := 119) (by omega)),
   fun h => kill2_d121 hP E (two_pow_add_one_dvd_of_odd_mul (d := 121) (by omega)),
   fun h => kill2_d122 hP E (two_pow_add_one_dvd_of_odd_mul (d := 122) (by omega)),
   fun h => kill2_d123 hP E (two_pow_add_one_dvd_of_odd_mul (d := 123) (by omega)),
   fun h => kill2_d124 hP E (two_pow_add_one_dvd_of_odd_mul (d := 124) (by omega)),
   fun h => kill2_d131 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131) (by omega)),
   fun h => kill2_d133 hP E (two_pow_add_one_dvd_of_odd_mul (d := 133) (by omega)),
   fun h => kill2_d134 hP E (two_pow_add_one_dvd_of_odd_mul (d := 134) (by omega)),
   fun h => kill2_d141 hP E (two_pow_add_one_dvd_of_odd_mul (d := 141) (by omega)),
   fun h => kill2_d142 hP E (two_pow_add_one_dvd_of_odd_mul (d := 142) (by omega)),
   fun h => kill2_d143 hP E (two_pow_add_one_dvd_of_odd_mul (d := 143) (by omega)),
   fun h => kill2_d146 hP E (two_pow_add_one_dvd_of_odd_mul (d := 146) (by omega)),
   fun h => kill2_d147 hP E (two_pow_add_one_dvd_of_odd_mul (d := 147) (by omega)),
   fun h => kill2_d149 hP E (two_pow_add_one_dvd_of_odd_mul (d := 149) (by omega)),
   fun h => kill2_d152 hP E (two_pow_add_one_dvd_of_odd_mul (d := 152) (by omega)),
   fun h => kill2_d155 hP E (two_pow_add_one_dvd_of_odd_mul (d := 155) (by omega)),
   fun h => kill2_d157 hP E (two_pow_add_one_dvd_of_odd_mul (d := 157) (by omega))⟩

theorem three_two_adic_residues {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h3 : 3 ∣ n)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n.factorization 2 % 20 ≠ 10 ∧
    n.factorization 2 % 24 ≠ 12 ∧
    n.factorization 2 % 28 ≠ 14 ∧
    n.factorization 2 % 36 ≠ 18 ∧
    n.factorization 2 % 40 ≠ 20 ∧
    n.factorization 2 % 44 ≠ 22 ∧
    n.factorization 2 % 48 ≠ 24 ∧
    n.factorization 2 % 50 ≠ 25 ∧
    n.factorization 2 % 52 ≠ 26 ∧
    n.factorization 2 % 54 ≠ 27 ∧
    n.factorization 2 % 56 ≠ 28 ∧
    n.factorization 2 % 58 ≠ 29 ∧
    n.factorization 2 % 64 ≠ 32 ∧
    n.factorization 2 % 66 ≠ 33 ∧
    n.factorization 2 % 68 ≠ 34 ∧
    n.factorization 2 % 70 ≠ 35 ∧
    n.factorization 2 % 74 ≠ 37 ∧
    n.factorization 2 % 76 ≠ 38 ∧
    n.factorization 2 % 78 ≠ 39 ∧
    n.factorization 2 % 90 ≠ 45 ∧
    n.factorization 2 % 92 ≠ 46 ∧
    n.factorization 2 % 96 ≠ 48 ∧
    n.factorization 2 % 102 ≠ 51 ∧
    n.factorization 2 % 104 ≠ 52 ∧
    n.factorization 2 % 110 ≠ 55 ∧
    n.factorization 2 % 112 ≠ 56 ∧
    n.factorization 2 % 114 ≠ 57 ∧
    n.factorization 2 % 118 ≠ 59 ∧
    n.factorization 2 % 124 ≠ 62 ∧
    n.factorization 2 % 126 ≠ 63 ∧
    n.factorization 2 % 128 ≠ 64 ∧
    n.factorization 2 % 130 ≠ 65 ∧
    n.factorization 2 % 134 ≠ 67 ∧
    n.factorization 2 % 136 ≠ 68 ∧
    n.factorization 2 % 138 ≠ 69 ∧
    n.factorization 2 % 148 ≠ 74 ∧
    n.factorization 2 % 152 ≠ 76 ∧
    n.factorization 2 % 154 ≠ 77 ∧
    n.factorization 2 % 160 ≠ 80 ∧
    n.factorization 2 % 164 ≠ 82 ∧
    n.factorization 2 % 166 ≠ 83 ∧
    n.factorization 2 % 170 ≠ 85 ∧
    n.factorization 2 % 172 ≠ 86 ∧
    n.factorization 2 % 182 ≠ 91 ∧
    n.factorization 2 % 188 ≠ 94 ∧
    n.factorization 2 % 190 ≠ 95 ∧
    n.factorization 2 % 194 ≠ 97 ∧
    n.factorization 2 % 212 ≠ 106 ∧
    n.factorization 2 % 224 ≠ 112 ∧
    n.factorization 2 % 230 ≠ 115 ∧
    n.factorization 2 % 232 ≠ 116 ∧
    n.factorization 2 % 236 ≠ 118 ∧
    n.factorization 2 % 238 ≠ 119 ∧
    n.factorization 2 % 242 ≠ 121 ∧
    n.factorization 2 % 244 ≠ 122 ∧
    n.factorization 2 % 246 ≠ 123 ∧
    n.factorization 2 % 248 ≠ 124 ∧
    n.factorization 2 % 262 ≠ 131 ∧
    n.factorization 2 % 266 ≠ 133 ∧
    n.factorization 2 % 268 ≠ 134 ∧
    n.factorization 2 % 282 ≠ 141 ∧
    n.factorization 2 % 284 ≠ 142 ∧
    n.factorization 2 % 286 ≠ 143 ∧
    n.factorization 2 % 292 ≠ 146 ∧
    n.factorization 2 % 294 ≠ 147 ∧
    n.factorization 2 % 298 ≠ 149 ∧
    n.factorization 2 % 304 ≠ 152 ∧
    n.factorization 2 % 310 ≠ 155 ∧
    n.factorization 2 % 314 ≠ 157 := by
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h3, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  exact core3_two_adic_residues hP E

theorem kill2e11_d4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 4 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 4 + 1).trans hd) 67 g67 (by norm_num)

theorem kill2e11_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have := S3 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 65537 g65537 (by norm_num) (by norm_num)
  omega

theorem kill2e13_d2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 2 + 1).trans hd) 19 g19 (by norm_num)

theorem kill2e13_d4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 4 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 4 + 1).trans hd) 398581 g398581 (by norm_num)

theorem kill2e13_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 13 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g398581 : 398581 ∈ P := S7 398581 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 398581 g398581 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 83 g83 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill2e19_d2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g389 : 389 ∈ P := S1 389 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 2 + 1).trans hd) 389 g389 (by norm_num)

theorem kill2e19_d8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 8 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 8 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 131 g131 (by norm_num) (by norm_num)
  omega

theorem kill2e19_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 19 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have g101917 : 101917 ∈ P := S7 101917 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 101917 g101917 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 131 g131 (by norm_num) (by norm_num)
  omega

theorem core3e11_two_adic_shape {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p) :
    m % 2 = 1 ∨ m % 4 = 2 ∨ m % 16 = 8 ∨ m % 128 = 0 := by
  have h4 : m % 8 ≠ 4 := (fun h => kill2e11_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega)))
  have h16 : m % 32 ≠ 16 := (fun h => kill2e11_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega)))
  have h32 : m % 64 ≠ 32 := (fun h => kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega)))
  have h64 : m % 128 ≠ 64 := (fun h => kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega)))
  omega

theorem core3e13_two_adic_shape {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 13) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 13 * ∏ p ∈ P, p) :
    m % 2 = 1 ∨ m % 16 = 8 ∨ m % 128 = 0 := by
  have h2 : m % 4 ≠ 2 := (fun h => kill2e13_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega)))
  have h4 : m % 8 ≠ 4 := (fun h => kill2e13_d4 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4) (by omega)))
  have h16 : m % 32 ≠ 16 := (fun h => kill2e13_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega)))
  have h32 : m % 64 ≠ 32 := (fun h => kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega)))
  have h64 : m % 128 ≠ 64 := (fun h => kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega)))
  omega

theorem core3e19_two_adic_shape {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 19) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 19 * ∏ p ∈ P, p) :
    m % 2 = 1 ∨ m % 8 = 4 ∨ m % 128 = 0 := by
  have h2 : m % 4 ≠ 2 := (fun h => kill2e19_d2 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2) (by omega)))
  have h8 : m % 16 ≠ 8 := (fun h => kill2e19_d8 hP E (two_pow_add_one_dvd_of_odd_mul (d := 8) (by omega)))
  have h16 : m % 32 ≠ 16 := (fun h => kill2e19_d16 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega)))
  have h32 : m % 64 ≠ 32 := (fun h => kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega)))
  have h64 : m % 128 ≠ 64 := (fun h => kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega)))
  omega

theorem budget_kernel3 {m e : ℕ} {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hS : S ⊆ P) (h : 3 ^ (e + 1) ∣ (2 ^ m + 1) * ∏ p ∈ S, (p + 1)) : False := by
  have h1 : (2 ^ m + 1) * ∏ p ∈ S, (p + 1) ∣ (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) := by
    have := mul_dvd_mul_left (2 ^ m + 1) (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) hS)
    exact this.trans ⟨1 + 3 ^ e, by ring⟩
  have h2 := h.trans h1
  rw [E, pow_succ] at h2
  have e1 : 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p = 3 ^ e * (2 ^ (m + 1) * ∏ p ∈ P, p) := by ring
  rw [e1] at h2
  exact three_not_dvd_rhs hP h3P (Nat.dvd_of_mul_dvd_mul_left (by positivity) h2)

theorem one_other_leaf3 {L : Finset ℕ} {β : ℕ → ℚ} (S : Finset ℕ)
    (hL : ∀ q ∈ L, q.Prime ∧ q ≠ 2 ∧ 3 ∣ q + 1)
    (hone : ∀ q ∈ L, ∀ q' ∈ L, q ∉ S → q' ∉ S → q = q')
    (hβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (hβ5 : β 5 ≤ 4 / 3) :
    ∏ q ∈ L.filter (fun q => q ∉ S), β q ≤ 4 / 3 := by
  have hc : (L.filter (fun q => q ∉ S)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hone a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]; norm_num
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
    rw [hq, Finset.prod_singleton]
    have hqL : q ∈ L := (Finset.mem_filter.mp (hq ▸ Finset.mem_singleton_self q)).1
    obtain ⟨hqp, hq2, hq3⟩ := hL q hqL
    by_cases h5 : q = 5
    · rw [h5]; exact hβ5
    · have h6 := leaf3_size hqp hq2 hq3
      have h11 : 11 ≤ q := by omega
      refine (hβ q hqL).2.trans ((B_anti (by norm_num) h11).trans ?_)
      norm_num

theorem two_leaves_budget {m e : ℕ} {P T : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (he : 1 ≤ e) (hT : T ⊆ P) (hTb : 3 ^ (e - 1) ∣ (2 ^ m + 1) * ∏ p ∈ T, (p + 1))
    {q q' : ℕ} (hq : q ∈ P) (hq' : q' ∈ P) (hqT : q ∉ T) (hqT' : q' ∉ T)
    (h3 : 3 ∣ q + 1) (h3' : 3 ∣ q' + 1) : q = q' := by
  by_contra hne
  have hS : insert q (insert q' T) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hq
    · exact hq'
    · exact hT hx
  refine budget_kernel3 hP h3P E hS ?_
  have hq1 : q ∉ insert q' T := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hne, hqT⟩
  rw [Finset.prod_insert hq1, Finset.prod_insert hqT']
  have e1 : (2 ^ m + 1) * ((q + 1) * ((q' + 1) * ∏ p ∈ T, (p + 1))) =
      ((q + 1) * (q' + 1)) * ((2 ^ m + 1) * ∏ p ∈ T, (p + 1)) := by ring
  have e2 : 3 ^ (e + 1) = (3 * 3) * 3 ^ (e - 1) := by
    rw [← pow_two, ← pow_add]; congr 1; omega
  rw [e1, e2]
  exact mul_dvd_mul (mul_dvd_mul h3 h3') hTb

theorem core3e5_eleven {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hm : 4 ≤ m) (h331P : 331 ∈ P)
    (h11par : ∀ p ∈ P, 11 ∣ p + 1 → 43691 ≤ p)
    (h331sib : ∀ p ∈ P, 331 ∣ p + 1 → 11 ∣ p + 1)
    (hone : ∀ q ∈ P, ∀ q' ∈ P, q ≠ 11 → q' ≠ 11 →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({3} : Finset ℕ)) →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q' + 1 → c ∈ ({3} : Finset ℕ)) →
      3 ∣ q + 1 → 3 ∣ q' + 1 → q = q') : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h61P : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h31P : 31 ∈ P := S1 31 (by norm_num) (by norm_num) (hn3 (by norm_num)) 61 h61P (by norm_num)
  have h83P : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 h331P (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) 83 h83P (by norm_num)
  let β : ℕ → ℚ := fun p => if p = 5 then 4 / 3 else if p = 7 then 8 / 7 * (84 / 83) * (332 / 331)
    else if p = 83 then 84 / 83 * (332 / 331) else if p = 331 then 332 / 331
    else if p = 11 then 12 / 11 * (43692 / 43690) else if p = 31 then 32 / 31 * (62 / 61)
    else if p = 61 then 62 / 61 else if p = 3 then 1 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have b5 : β 5 = 4 / 3 := by simp [β]
  have b7 : β 7 = 8 / 7 * (84 / 83) * (332 / 331) := by simp [β]
  have b83 : β 83 = 84 / 83 * (332 / 331) := by simp [β]
  have b331 : β 331 = 332 / 331 := by simp [β]
  have b11 : β 11 = 12 / 11 * (43692 / 43690) := by simp [β]
  have b31 : β 31 = 32 / 31 * (62 / 61) := by simp [β]
  have b61 : β 61 = 62 / 61 := by simp [β]
  have b3 : β 3 = 1 := by simp [β]
  have bB : ∀ p : ℕ, p ≠ 5 → p ≠ 7 → p ≠ 83 → p ≠ 331 → p ≠ 11 → p ≠ 31 → p ≠ 61 → p ≠ 3 →
      β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := fun p h1 h2 h3 h4 h5 h6 h7 h8 => by
    simp [β, h1, h2, h3, h4, h5, h6, h7, h8]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases c5 : p = 5
    · subst c5; rw [b5]; norm_num
    by_cases c7 : p = 7
    · subst c7; rw [b7]; norm_num
    by_cases c83 : p = 83
    · subst c83; rw [b83]; norm_num
    by_cases c331 : p = 331
    · subst c331; rw [b331]; norm_num
    by_cases c11 : p = 11
    · subst c11; rw [b11]; norm_num
    by_cases c31 : p = 31
    · subst c31; rw [b31]; norm_num
    by_cases c61 : p = 61
    · subst c61; rw [b61]; norm_num
    have c3 : p ≠ 3 := fun h => h3P (h ▸ hp)
    rw [bB p c5 c7 c83 c331 c11 c31 c61 c3]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen (N := {3}) hP hK (by norm_num) E β hB
    (fun p hp c hc hcp hleast hne => by
      have hpp := (hP p hp).1
      by_cases c5 : c = 5
      · subst c5
        have h19 : 19 ≤ p := by
          have hp9 : p ≠ 9 := by rintro rfl; norm_num at hpp
          have hodd : p % 2 = 1 := by
            rcases hpp.eq_two_or_odd with h | h
            · exact absurd h (hP p hp).2
            · exact h
          omega
        rw [b5]
        have := (hB p hp).2.trans (B_anti (by norm_num) h19)
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((5 : ℕ) : ℚ) := by norm_num
        have := mul_le_mul_of_nonneg_left this h0
        norm_num at this ⊢
        linarith
      by_cases c7 : c = 7
      · subst c7
        have : p = 83 := S3 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 83 h83P hcp
          (by norm_num)
        subst this
        rw [b83, b7]; norm_num
      by_cases c83 : c = 83
      · subst c83
        have : p = 331 := S3 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 331 h331P hcp
          (by norm_num)
        subst this
        rw [b331, b83]; norm_num
      by_cases c331 : c = 331
      · subst c331
        have := hleast 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) (h331sib p hp hcp)
        omega
      by_cases c11 : c = 11
      · subst c11
        have h43 := h11par p hp hcp
        rw [b11]
        have := (hB p hp).2.trans (B_anti (by norm_num) h43)
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((11 : ℕ) : ℚ) := by norm_num
        have := mul_le_mul_of_nonneg_left this h0
        norm_num at this ⊢
        linarith
      by_cases c31 : c = 31
      · subst c31
        have : p = 61 := S3 31 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 61 h61P hcp
          (by norm_num)
        subst this
        rw [b61, b31]; norm_num
      by_cases c61 : c = 61
      · subst c61
        exact absurd hcp (S8 61 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num) p hp)
      · exact absurd (bB c c5 c7 c83 c331 c11 c31 c61 (fun h => h3P (h ▸ hc))) hne)
  have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => 3 ∣ q + 1) β
  -- the 3-leaves: 11 and at most one more
  have hL3 : ∀ q ∈ L.filter (fun q => 3 ∣ q + 1), q.Prime ∧ q ≠ 2 ∧ 3 ∣ q + 1 := fun q hq =>
    ⟨(hP q (hLP (Finset.mem_filter.mp hq).1)).1, (hP q (hLP (Finset.mem_filter.mp hq).1)).2,
      (Finset.mem_filter.mp hq).2⟩
  have hother := one_other_leaf3 (L := L.filter (fun q => 3 ∣ q + 1)) (β := β) {11} hL3
    (fun q hq q' hq' h1 h2 => by
      obtain ⟨hqL, hq3⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL', hq3'⟩ := Finset.mem_filter.mp hq'
      exact hone q (hLP hqL) q' (hLP hqL') (fun h => h1 (Finset.mem_singleton.mpr h))
        (fun h => h2 (Finset.mem_singleton.mpr h)) (hLleaf q hqL) (hLleaf q' hqL') hq3 hq3')
    (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1, (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩)
    (le_of_eq b5)
  have h11part : ∏ q ∈ (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ q ∉ ({11} : Finset ℕ)), β q
      ≤ 12 / 11 * (43692 / 43690) := by
    have hsub : (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ q ∉ ({11} : Finset ℕ)) ⊆ {11} :=
      fun q hq => by simpa using (Finset.mem_filter.mp hq).2
    rcases Finset.subset_singleton_iff.mp hsub with h | h
    · rw [h, Finset.prod_empty]; norm_num
    · rw [h, Finset.prod_singleton, b11]
  have h3leaves : ∏ q ∈ L.filter (fun q => 3 ∣ q + 1), β q ≤ 12 / 11 * (43692 / 43690) * (4 / 3) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => 3 ∣ q + 1))
      (fun q => ¬ q ∉ ({11} : Finset ℕ))]
    have e1 : (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ ¬ q ∉ ({11} : Finset ℕ)) =
        (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => q ∉ ({11} : Finset ℕ)) := by
      simp only [not_not]
    rw [e1]
    exact mul_le_mul h11part hother (Finset.prod_nonneg fun q hq =>
      (hβpos q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).le) (by norm_num)
  have hmers : ∏ q ∈ L.filter (fun q => ¬ 3 ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
        (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
    · obtain ⟨hqL, h3⟩ := Finset.mem_filter.mp hq
      refine two_pow_of_no_odd_prime (fun c hc hc2 hcd => ?_)
      rw [Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)] at hcd
      exact h3 hcd
    · rw [b3, b7, b31, bB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)]
      norm_num
  have hvals : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) =
      (8 / 7 * (84 / 83) * (332 / 331)) * (32 / 31 * (62 / 61)) * (128 / 126) * (2048 / 2047) := by
    rw [b3, b7, b31, bB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [hvals] at hmers
  have hprod : ∏ q ∈ L, β q ≤ 12 / 11 * (43692 / 43690) * (4 / 3) *
      ((8 / 7 * (84 / 83) * (332 / 331)) * (32 / 31 * (62 / 61)) * (128 / 126) * (2048 / 2047)) := by
    rw [← hsplit]
    exact mul_le_mul h3leaves hmers
      (Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le) (by norm_num)
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 17 / 16 := by
    have h2 : (2 : ℚ) ^ 4 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 4 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hK' : (((1 + 3 ^ 5 : ℕ) : ℚ) / ((3 ^ 5 : ℕ) : ℚ)) = 244 / 243 := by norm_num
  rw [hK'] at hmain
  have hfin : (2 : ℚ) ≤ 17 / 16 * (244 / 243) * (12 / 11 * (43692 / 43690) * (4 / 3) *
      ((8 / 7 * (84 / 83) * (332 / 331)) * (32 / 31 * (62 / 61)) * (128 / 126) * (2048 / 2047))) :=
    hmain.trans (mul_le_mul (mul_le_mul_of_nonneg_right hT (by norm_num)) hprod
      (Finset.prod_nonneg fun q hq => (hβpos q hq).le) (by norm_num))
  norm_num at hfin

theorem kill3e5w_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 4 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have gR : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num at hd ⊢; exact hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 65537 gR (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 65537 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 65537} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (5 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 65537} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    exact Dvd.dvd.mul_left (by norm_num) _
  refine core3e5_eleven hP h3P E hm g331
    (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 65537 gR h (by norm_num)
      omega)
    (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 65537 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 →
          x ∉ ({11, 83, 65537} : Finset ℕ) := fun x hl h1 hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1) (nT q' hl' h2) h3 h3')

theorem kill3e5w_d15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 15 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 4 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have d11 : 11 ∣ 2 ^ m + 1 := (by norm_num : 11 ∣ 2 ^ 15 + 1).trans hd
  have d331 : 331 ∣ 2 ^ m + 1 := (by norm_num : 331 ∣ 2 ^ 15 + 1).trans hd
  have d9 : 9 ∣ 2 ^ m + 1 := (by norm_num : 9 ∣ 2 ^ 15 + 1).trans hd
  have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) d11
  have g331 : 331 ∈ P := S2 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) d331
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hTb : 3 ^ (5 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (5 - 1) = 9 * 9 by norm_num]
    exact (mul_dvd_mul d9 (by norm_num : 9 ∣ (11 + 1) * (83 + 1)))
  refine core3e5_eleven hP h3P E hm g331
    (fun p hp h => absurd h (S4 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) d11 p hp))
    (fun p hp h => absurd h (S4 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) d331 p hp))
    (fun q hq q' hq' h1 h2 hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 →
          x ∉ ({11, 83} : Finset ℕ) := fun x hl h1 hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1) (nT q' hl' h2) h3 h3')

theorem kill3e5w_d17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 17 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 4 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have d3 : 3 ∣ 2 ^ m + 1 := (by norm_num : 3 ∣ 2 ^ 17 + 1).trans hd
  have gR : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hn3 (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 17 + 1).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 43691} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (5 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 43691} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (5 - 1) = 3 * 27 by norm_num]
    exact (mul_dvd_mul d3 (by norm_num : 27 ∣ (11 + 1) * ((83 + 1) * (43691 + 1))))
  refine core3e5_eleven hP h3P E hm g331
    (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      omega)
    (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 →
          x ∉ ({11, 83, 43691} : Finset ℕ) := fun x hl h1 hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1) (nT q' hl' h2) h3 h3')

theorem kill3e5w_d19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 19 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 4 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have d3 : 3 ∣ 2 ^ m + 1 := (by norm_num : 3 ∣ 2 ^ 19 + 1).trans hd
  have gT : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hn3 (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 19 + 1).trans hd)
  have gR : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hn3 (by norm_num)) 174763 gT (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 43691} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (5 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 43691} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (5 - 1) = 3 * 27 by norm_num]
    exact (mul_dvd_mul d3 (by norm_num : 27 ∣ (11 + 1) * ((83 + 1) * (43691 + 1))))
  refine core3e5_eleven hP h3P E hm g331
    (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      omega)
    (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 →
          x ∉ ({11, 83, 43691} : Finset ℕ) := fun x hl h1 hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1) (nT q' hl' h2) h3 h3')

theorem core3e7_eleven {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hm : 15 ≤ m) (h331P : 331 ∈ P)
    (h11par : ∀ p ∈ P, 11 ∣ p + 1 → 43691 ≤ p)
    (h331sib : ∀ p ∈ P, 331 ∣ p + 1 → 11 ∣ p + 1)
    (hone : ∀ q ∈ P, ∀ q' ∈ P, q ≠ 11 → q' ≠ 11 → q ≠ 23 → q' ≠ 23 →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ ({3} : Finset ℕ)) →
      (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q' + 1 → c ∈ ({3} : Finset ℕ)) →
      3 ∣ q + 1 → 3 ∣ q' + 1 → q = q') : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have h547P : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have h137P : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) 547 h547P (by norm_num)
  have h83P : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 h331P (by norm_num)
  let β : ℕ → ℚ := fun p => if p = 5 then 4 / 3 else if p = 7 then 8 / 7 * (84 / 83) * (332 / 331)
    else if p = 83 then 84 / 83 * (332 / 331) else if p = 331 then 332 / 331
    else if p = 11 then 12 / 11 * (43692 / 43690) else if p = 23 then 24 / 23 * (138 / 137) * (548 / 547)
    else if p = 137 then 138 / 137 * (548 / 547) else if p = 547 then 548 / 547
    else if p = 3 then 1 else ((p : ℚ) + 1) / ((p : ℚ) - 1)
  have b5 : β 5 = 4 / 3 := by simp [β]
  have b7 : β 7 = 8 / 7 * (84 / 83) * (332 / 331) := by simp [β]
  have b83 : β 83 = 84 / 83 * (332 / 331) := by simp [β]
  have b331 : β 331 = 332 / 331 := by simp [β]
  have b11 : β 11 = 12 / 11 * (43692 / 43690) := by simp [β]
  have b23 : β 23 = 24 / 23 * (138 / 137) * (548 / 547) := by simp [β]
  have b137 : β 137 = 138 / 137 * (548 / 547) := by simp [β]
  have b547 : β 547 = 548 / 547 := by simp [β]
  have b3 : β 3 = 1 := by simp [β]
  have bB : ∀ p : ℕ, p ≠ 5 → p ≠ 7 → p ≠ 83 → p ≠ 331 → p ≠ 11 → p ≠ 23 → p ≠ 137 → p ≠ 547 →
      p ≠ 3 → β p = ((p : ℚ) + 1) / ((p : ℚ) - 1) := fun p h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    simp [β, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases c5 : p = 5
    · subst c5; rw [b5]; norm_num
    by_cases c7 : p = 7
    · subst c7; rw [b7]; norm_num
    by_cases c83 : p = 83
    · subst c83; rw [b83]; norm_num
    by_cases c331 : p = 331
    · subst c331; rw [b331]; norm_num
    by_cases c11 : p = 11
    · subst c11; rw [b11]; norm_num
    by_cases c23 : p = 23
    · subst c23; rw [b23]; norm_num
    by_cases c137 : p = 137
    · subst c137; rw [b137]; norm_num
    by_cases c547 : p = 547
    · subst c547; rw [b547]; norm_num
    have c3 : p ≠ 3 := fun h => h3P (h ▸ hp)
    rw [bB p c5 c7 c83 c331 c11 c23 c137 c547 c3]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_rfl⟩
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen (N := {3}) hP hK (by norm_num) E β hB
    (fun p hp c hc hcp hleast hne => by
      have hpp := (hP p hp).1
      by_cases c5 : c = 5
      · subst c5
        have h19 : 19 ≤ p := by
          have hp9 : p ≠ 9 := by rintro rfl; norm_num at hpp
          have hodd : p % 2 = 1 := by
            rcases hpp.eq_two_or_odd with h | h
            · exact absurd h (hP p hp).2
            · exact h
          omega
        rw [b5]
        have := (hB p hp).2.trans (B_anti (by norm_num) h19)
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((5 : ℕ) : ℚ) := by norm_num
        have := mul_le_mul_of_nonneg_left this h0
        norm_num at this ⊢
        linarith
      by_cases c7 : c = 7
      · subst c7
        have : p = 83 := S3 7 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 83 h83P hcp
          (by norm_num)
        subst this
        rw [b83, b7]; norm_num
      by_cases c83 : c = 83
      · subst c83
        have : p = 331 := S3 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 331 h331P hcp
          (by norm_num)
        subst this
        rw [b331, b83]; norm_num
      by_cases c331 : c = 331
      · subst c331
        have := hleast 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) (h331sib p hp hcp)
        omega
      by_cases c11 : c = 11
      · subst c11
        have h43 := h11par p hp hcp
        rw [b11]
        have := (hB p hp).2.trans (B_anti (by norm_num) h43)
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((11 : ℕ) : ℚ) := by norm_num
        have := mul_le_mul_of_nonneg_left this h0
        norm_num at this ⊢
        linarith
      by_cases c23 : c = 23
      · subst c23
        have : p = 137 := S3 23 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 137 h137P hcp
          (by norm_num)
        subst this
        rw [b137, b23]; norm_num
      by_cases c137 : c = 137
      · subst c137
        have : p = 547 := S3 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 547 h547P hcp
          (by norm_num)
        subst this
        rw [b547, b137]; norm_num
      by_cases c547 : c = 547
      · subst c547
        exact absurd hcp (S8 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num) p hp)
      · exact absurd (bB c c5 c7 c83 c331 c11 c23 c137 c547 (fun h => h3P (h ▸ hc))) hne)
  have hβpos : ∀ q ∈ L, 0 < β q := fun q hq => by
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    linarith [(hB q (hLP hq)).1]
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => 3 ∣ q + 1) β
  have hL3 : ∀ q ∈ L.filter (fun q => 3 ∣ q + 1), q.Prime ∧ q ≠ 2 ∧ 3 ∣ q + 1 := fun q hq =>
    ⟨(hP q (hLP (Finset.mem_filter.mp hq).1)).1, (hP q (hLP (Finset.mem_filter.mp hq).1)).2,
      (Finset.mem_filter.mp hq).2⟩
  have hother := one_other_leaf3 (L := L.filter (fun q => 3 ∣ q + 1)) (β := β) {11, 23} hL3
    (fun q hq q' hq' h1 h2 => by
      obtain ⟨hqL, hq3⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL', hq3'⟩ := Finset.mem_filter.mp hq'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2
      exact hone q (hLP hqL) q' (hLP hqL') h1.1 h2.1 h1.2 h2.2 (hLleaf q hqL) (hLleaf q' hqL') hq3 hq3')
    (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1, (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩)
    (le_of_eq b5)
  have hpart : ∏ q ∈ (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ q ∉ ({11, 23} : Finset ℕ)), β q
      ≤ 12 / 11 * (43692 / 43690) * (24 / 23 * (138 / 137) * (548 / 547)) := by
    have hsub : (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ q ∉ ({11, 23} : Finset ℕ)) ⊆
        {11, 23} := fun q hq => by
      have := (Finset.mem_filter.mp hq).2
      simp only [not_not] at this
      exact this
    have hle : ∀ S : Finset ℕ, S ⊆ {11, 23} → ∏ q ∈ S, β q ≤
        12 / 11 * (43692 / 43690) * (24 / 23 * (138 / 137) * (548 / 547)) := by
      intro S hS
      have hpow : S ∈ ({11, 23} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
      have hps : ({11, 23} : Finset ℕ).powerset = {∅, {11}, {23}, {11, 23}} := by decide
      rw [hps] at hpow
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpow
      rcases hpow with rfl | rfl | rfl | rfl
      · rw [Finset.prod_empty]; norm_num
      · rw [Finset.prod_singleton, b11]; norm_num
      · rw [Finset.prod_singleton, b23]; norm_num
      · rw [Finset.prod_pair (by norm_num), b11, b23]
    exact hle _ hsub
  have h3leaves : ∏ q ∈ L.filter (fun q => 3 ∣ q + 1), β q ≤
      12 / 11 * (43692 / 43690) * (24 / 23 * (138 / 137) * (548 / 547)) * (4 / 3) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => 3 ∣ q + 1))
      (fun q => ¬ q ∉ ({11, 23} : Finset ℕ))]
    have e1 : (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => ¬ ¬ q ∉ ({11, 23} : Finset ℕ)) =
        (L.filter (fun q => 3 ∣ q + 1)).filter (fun q => q ∉ ({11, 23} : Finset ℕ)) := by
      simp only [not_not]
    rw [e1]
    exact mul_le_mul hpart hother (Finset.prod_nonneg fun q hq =>
      (hβpos q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).le) (by norm_num)
  have hmers : ∏ q ∈ L.filter (fun q => ¬ 3 ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (Finset.mem_filter.mp hq).1,
        (hB q (hLP (Finset.mem_filter.mp hq).1)).2⟩) ?_
    · obtain ⟨hqL, h3⟩ := Finset.mem_filter.mp hq
      refine two_pow_of_no_odd_prime (fun c hc hc2 hcd => ?_)
      rw [Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)] at hcd
      exact h3 hcd
    · rw [b3, b7, bB 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        bB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      norm_num
  have hvals : (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) =
      (8 / 7 * (84 / 83) * (332 / 331)) * (32 / 30) * (128 / 126) * (2048 / 2047) := by
    rw [b3, b7, bB 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      bB 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [hvals] at hmers
  have hprod : ∏ q ∈ L, β q ≤ 12 / 11 * (43692 / 43690) * (24 / 23 * (138 / 137) * (548 / 547)) *
      (4 / 3) * ((8 / 7 * (84 / 83) * (332 / 331)) * (32 / 30) * (128 / 126) * (2048 / 2047)) := by
    rw [← hsplit]
    exact mul_le_mul h3leaves hmers
      (Finset.prod_nonneg fun q hq => (hβpos q (Finset.mem_filter.mp hq).1).le) (by norm_num)
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 32769 / 32768 := by
    have h2 : (2 : ℚ) ^ 15 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 15 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hK' : (((1 + 3 ^ 7 : ℕ) : ℚ) / ((3 ^ 7 : ℕ) : ℚ)) = 2188 / 2187 := by norm_num
  rw [hK'] at hmain
  have hfin : (2 : ℚ) ≤ 32769 / 32768 * (2188 / 2187) *
      (12 / 11 * (43692 / 43690) * (24 / 23 * (138 / 137) * (548 / 547)) * (4 / 3) *
      ((8 / 7 * (84 / 83) * (332 / 331)) * (32 / 30) * (128 / 126) * (2048 / 2047))) :=
    hmain.trans (mul_le_mul (mul_le_mul_of_nonneg_right hT (by norm_num)) hprod
      (Finset.prod_nonneg fun q hq => (hβpos q hq).le) (by norm_num))
  norm_num at hfin

theorem kill3e7w_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 15 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hn3 (by norm_num)) 137 g137 (by norm_num)
  have gR : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num at hd ⊢; exact hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 65537 gR (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 65537 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 23, 137, 65537} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (7 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 23, 137, 65537} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (7 - 1) = 1 * 729 by norm_num]
    exact mul_dvd_mul (one_dvd _) (by norm_num)
  refine core3e7_eleven hP h3P E hm g331 (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 65537 gR h (by norm_num)
      omega) (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 65537 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 h1' h2' hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 → x ≠ 23 →
          x ∉ ({11, 83, 23, 137, 65537} : Finset ℕ) := fun x hl h1 h1' hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · exact h1' rfl
        · have := hl 23 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1 h1') (nT q' hl' h2 h2') h3 h3')

theorem kill3e7w_d15 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 15 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 15 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hn3 (by norm_num)) 137 g137 (by norm_num)
  have d11 : 11 ∣ 2 ^ m + 1 := (by norm_num : 11 ∣ 2 ^ 15 + 1).trans hd
  have d331 : 331 ∣ 2 ^ m + 1 := (by norm_num : 331 ∣ 2 ^ 15 + 1).trans hd
  have d9 : 9 ∣ 2 ^ m + 1 := (by norm_num : 9 ∣ 2 ^ 15 + 1).trans hd
  have g331 : 331 ∈ P := S2 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) d331
  have g11 : 11 ∈ P := S2 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) d11
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 23, 137} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (7 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 23, 137} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (7 - 1) = 9 * 81 by norm_num]
    exact mul_dvd_mul d9 (by norm_num)
  refine core3e7_eleven hP h3P E hm g331 (fun p hp h => absurd h (S4 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) d11 p hp)) (fun p hp h => absurd h (S4 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) d331 p hp))
    (fun q hq q' hq' h1 h2 h1' h2' hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 → x ≠ 23 →
          x ∉ ({11, 83, 23, 137} : Finset ℕ) := fun x hl h1 h1' hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · exact h1' rfl
        · have := hl 23 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1 h1') (nT q' hl' h2 h2') h3 h3')

theorem kill3e7w_d17 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 17 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 15 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hn3 (by norm_num)) 137 g137 (by norm_num)
  have d3 : 3 ∣ 2 ^ m + 1 := (by norm_num : 3 ∣ 2 ^ 17 + 1).trans hd
  have gR : 43691 ∈ P := S2 43691 (by norm_num) (by norm_num) (hn3 (by norm_num))
    ((by norm_num : 43691 ∣ 2 ^ 17 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 23, 137, 43691} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (7 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 23, 137, 43691} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (7 - 1) = 3 * 243 by norm_num]
    exact mul_dvd_mul d3 (by norm_num)
  refine core3e7_eleven hP h3P E hm g331 (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      omega) (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 h1' h2' hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 → x ≠ 23 →
          x ∉ ({11, 83, 23, 137, 43691} : Finset ℕ) := fun x hl h1 h1' hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · exact h1' rfl
        · have := hl 23 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1 h1') (nT q' hl' h2 h2') h3 h3')

theorem kill3e7w_d19 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 19 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) := prime_dvd_three_pow
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hn3 : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  have hm : 15 ≤ m := by
    by_contra hlt
    interval_cases m <;> norm_num at hd
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hn3 (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hn3 (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hn3 (by norm_num)) 137 g137 (by norm_num)
  have d3 : 3 ∣ 2 ^ m + 1 := (by norm_num : 3 ∣ 2 ^ 19 + 1).trans hd
  have gT : 174763 ∈ P := S2 174763 (by norm_num) (by norm_num) (hn3 (by norm_num))
    ((by norm_num : 174763 ∣ 2 ^ 19 + 1).trans hd)
  have gR : 43691 ∈ P := S1 43691 (by norm_num) (by norm_num) (hn3 (by norm_num)) 174763 gT (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) 43691 gR (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hn3 (by norm_num)) 331 g331 (by norm_num)
  have hT : ({11, 83, 23, 137, 43691} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hTb : 3 ^ (7 - 1) ∣ (2 ^ m + 1) * ∏ p ∈ ({11, 83, 23, 137, 43691} : Finset ℕ), (p + 1) := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num), Finset.prod_pair (by norm_num)]
    rw [show 3 ^ (7 - 1) = 3 * 243 by norm_num]
    exact mul_dvd_mul d3 (by norm_num)
  refine core3e7_eleven hP h3P E hm g331 (fun p hp h => by
      have := S3 11 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      omega) (fun p hp h => by
      have := S3 331 (by norm_num) (by norm_num) (hn3 (by norm_num)) p hp 43691 gR h (by norm_num)
      subst this; norm_num)
    (fun q hq q' hq' h1 h2 h1' h2' hl hl' h3 h3' => by
      have nT : ∀ x, (∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ x + 1 → c ∈ ({3} : Finset ℕ)) → x ≠ 11 → x ≠ 23 →
          x ∉ ({11, 83, 23, 137, 43691} : Finset ℕ) := fun x hl h1 h1' hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h1 rfl
        · have := hl 7 (by norm_num) (by norm_num) (by norm_num); simp at this
        · exact h1' rfl
        · have := hl 23 (by norm_num) (by norm_num) (by norm_num); simp at this
        · have := hl 11 (by norm_num) (by norm_num) (by norm_num); simp at this
      exact two_leaves_budget hP h3P E (by norm_num) hT hTb hq hq' (nT q hl h1 h1') (nT q' hl' h2 h2') h3 h3')

theorem three_e57_weight_residues {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (h3e : n.factorization 3 = 5 ∨ n.factorization 3 = 7)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1) :
    n.factorization 2 % 30 ≠ 15 ∧ n.factorization 2 % 32 ≠ 16 ∧
    n.factorization 2 % 34 ≠ 17 ∧ n.factorization 2 % 38 ≠ 19 := by
  have h3 : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h3, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rcases h3e with h1 | h1
  · rw [h1] at E
    exact ⟨fun h' => kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega)),
      fun h' => kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega)),
      fun h' => kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega)),
      fun h' => kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))⟩
  · rw [h1] at E
    exact ⟨fun h' => kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega)),
      fun h' => kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega)),
      fun h' => kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega)),
      fun h' => kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))⟩

-- Section 9. The step.

theorem odd_mul_two_general {e : ℕ}
    (h : e % 20 ≠ 10 ∧
      e % 24 ≠ 12 ∧
      e % 28 ≠ 14 ∧
      e % 36 ≠ 18 ∧
      e % 40 ≠ 20 ∧
      e % 44 ≠ 22 ∧
      e % 48 ≠ 24 ∧
      e % 50 ≠ 25 ∧
      e % 52 ≠ 26 ∧
      e % 54 ≠ 27 ∧
      e % 56 ≠ 28 ∧
      e % 58 ≠ 29 ∧
      e % 64 ≠ 32 ∧
      e % 66 ≠ 33 ∧
      e % 68 ≠ 34 ∧
      e % 70 ≠ 35 ∧
      e % 74 ≠ 37 ∧
      e % 76 ≠ 38 ∧
      e % 78 ≠ 39 ∧
      e % 90 ≠ 45 ∧
      e % 92 ≠ 46 ∧
      e % 96 ≠ 48 ∧
      e % 102 ≠ 51 ∧
      e % 104 ≠ 52 ∧
      e % 110 ≠ 55 ∧
      e % 112 ≠ 56 ∧
      e % 114 ≠ 57 ∧
      e % 118 ≠ 59 ∧
      e % 124 ≠ 62 ∧
      e % 126 ≠ 63 ∧
      e % 128 ≠ 64 ∧
      e % 130 ≠ 65 ∧
      e % 134 ≠ 67 ∧
      e % 136 ≠ 68 ∧
      e % 138 ≠ 69 ∧
      e % 148 ≠ 74 ∧
      e % 152 ≠ 76 ∧
      e % 154 ≠ 77 ∧
      e % 160 ≠ 80 ∧
      e % 164 ≠ 82 ∧
      e % 166 ≠ 83 ∧
      e % 170 ≠ 85 ∧
      e % 172 ≠ 86 ∧
      e % 182 ≠ 91 ∧
      e % 188 ≠ 94 ∧
      e % 190 ≠ 95 ∧
      e % 194 ≠ 97 ∧
      e % 212 ≠ 106 ∧
      e % 224 ≠ 112 ∧
      e % 230 ≠ 115 ∧
      e % 232 ≠ 116 ∧
      e % 236 ≠ 118 ∧
      e % 238 ≠ 119 ∧
      e % 242 ≠ 121 ∧
      e % 244 ≠ 122 ∧
      e % 246 ≠ 123 ∧
      e % 248 ≠ 124 ∧
      e % 262 ≠ 131 ∧
      e % 266 ≠ 133 ∧
      e % 268 ≠ 134 ∧
      e % 282 ≠ 141 ∧
      e % 284 ≠ 142 ∧
      e % 286 ≠ 143 ∧
      e % 292 ≠ 146 ∧
      e % 294 ≠ 147 ∧
      e % 298 ≠ 149 ∧
      e % 304 ≠ 152 ∧
      e % 310 ≠ 155 ∧
      e % 314 ≠ 157) :
    ∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
      51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
      94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
      143, 146, 147, 149, 152, 155, 157} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem odd_mul_three_200 {e : ℕ}
    (h : e % 12 ≠ 6 ∧
      e % 16 ≠ 8 ∧
      e % 18 ≠ 9 ∧
      e % 20 ≠ 10 ∧
      e % 24 ≠ 12 ∧
      e % 28 ≠ 14 ∧
      e % 30 ≠ 15 ∧
      e % 32 ≠ 16 ∧
      e % 34 ≠ 17 ∧
      e % 40 ≠ 20 ∧
      e % 42 ≠ 21 ∧
      e % 44 ≠ 22 ∧
      e % 46 ≠ 23 ∧
      e % 50 ≠ 25 ∧
      e % 52 ≠ 26 ∧
      e % 56 ≠ 28 ∧
      e % 58 ≠ 29 ∧
      e % 62 ≠ 31 ∧
      e % 64 ≠ 32 ∧
      e % 66 ≠ 33 ∧
      e % 68 ≠ 34 ∧
      e % 70 ≠ 35 ∧
      e % 74 ≠ 37 ∧
      e % 76 ≠ 38 ∧
      e % 78 ≠ 39 ∧
      e % 82 ≠ 41 ∧
      e % 86 ≠ 43 ∧
      e % 88 ≠ 44 ∧
      e % 92 ≠ 46 ∧
      e % 94 ≠ 47 ∧
      e % 98 ≠ 49 ∧
      e % 104 ≠ 52 ∧
      e % 106 ≠ 53 ∧
      e % 110 ≠ 55 ∧
      e % 114 ≠ 57 ∧
      e % 116 ≠ 58 ∧
      e % 118 ≠ 59 ∧
      e % 122 ≠ 61 ∧
      e % 124 ≠ 62 ∧
      e % 128 ≠ 64 ∧
      e % 130 ≠ 65 ∧
      e % 134 ≠ 67 ∧
      e % 136 ≠ 68 ∧
      e % 142 ≠ 71 ∧
      e % 146 ≠ 73 ∧
      e % 148 ≠ 74 ∧
      e % 152 ≠ 76 ∧
      e % 154 ≠ 77 ∧
      e % 158 ≠ 79 ∧
      e % 164 ≠ 82 ∧
      e % 166 ≠ 83 ∧
      e % 172 ≠ 86 ∧
      e % 178 ≠ 89 ∧
      e % 182 ≠ 91 ∧
      e % 184 ≠ 92 ∧
      e % 188 ≠ 94 ∧
      e % 190 ≠ 95 ∧
      e % 194 ≠ 97 ∧
      e % 202 ≠ 101 ∧
      e % 206 ≠ 103 ∧
      e % 212 ≠ 106 ∧
      e % 214 ≠ 107 ∧
      e % 218 ≠ 109 ∧
      e % 226 ≠ 113 ∧
      e % 232 ≠ 116 ∧
      e % 236 ≠ 118 ∧
      e % 242 ≠ 121 ∧
      e % 244 ≠ 122 ∧
      e % 248 ≠ 124 ∧
      e % 254 ≠ 127 ∧
      e % 256 ≠ 128 ∧
      e % 262 ≠ 131 ∧
      e % 266 ≠ 133 ∧
      e % 268 ≠ 134 ∧
      e % 274 ≠ 137 ∧
      e % 278 ≠ 139 ∧
      e % 284 ≠ 142 ∧
      e % 286 ≠ 143 ∧
      e % 292 ≠ 146 ∧
      e % 296 ≠ 148 ∧
      e % 298 ≠ 149 ∧
      e % 302 ≠ 151 ∧
      e % 314 ≠ 157 ∧
      e % 316 ≠ 158 ∧
      e % 326 ≠ 163 ∧
      e % 328 ≠ 164 ∧
      e % 332 ≠ 166 ∧
      e % 334 ≠ 167 ∧
      e % 338 ≠ 169 ∧
      e % 344 ≠ 172 ∧
      e % 346 ≠ 173 ∧
      e % 356 ≠ 178 ∧
      e % 358 ≠ 179 ∧
      e % 362 ≠ 181 ∧
      e % 376 ≠ 188 ∧
      e % 382 ≠ 191 ∧
      e % 386 ≠ 193 ∧
      e % 388 ≠ 194 ∧
      e % 394 ≠ 197 ∧
      e % 398 ≠ 199) :
    ∀ d ∈ ({6, 8, 9, 10, 12, 14, 15, 16, 17, 20, 21, 22, 23, 25, 26, 28, 29, 31, 32, 33, 34, 35, 37,
      38, 39, 41, 43, 44, 46, 47, 49, 52, 53, 55, 57, 58, 59, 61, 62, 64, 65, 67, 68, 71, 73,
      74, 76, 77, 79, 82, 83, 86, 89, 91, 92, 94, 95, 97, 101, 103, 106, 107, 109, 113, 116,
      118, 121, 122, 124, 127, 128, 131, 133, 134, 137, 139, 142, 143, 146, 148, 149, 151, 157,
      158, 163, 164, 166, 167, 169, 172, 173, 178, 179, 181, 188, 191, 193, 194, 197, 199} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79, r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95, r96, r97, r98, r99⟩ := h
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem odd_mul_two_e57 {e : ℕ}
    (h : e % 20 ≠ 10 ∧
      e % 24 ≠ 12 ∧
      e % 28 ≠ 14 ∧
      e % 36 ≠ 18 ∧
      e % 40 ≠ 20 ∧
      e % 44 ≠ 22 ∧
      e % 48 ≠ 24 ∧
      e % 50 ≠ 25 ∧
      e % 52 ≠ 26 ∧
      e % 54 ≠ 27 ∧
      e % 56 ≠ 28 ∧
      e % 58 ≠ 29 ∧
      e % 64 ≠ 32 ∧
      e % 66 ≠ 33 ∧
      e % 68 ≠ 34 ∧
      e % 70 ≠ 35 ∧
      e % 74 ≠ 37 ∧
      e % 76 ≠ 38 ∧
      e % 78 ≠ 39 ∧
      e % 90 ≠ 45 ∧
      e % 92 ≠ 46 ∧
      e % 96 ≠ 48 ∧
      e % 102 ≠ 51 ∧
      e % 104 ≠ 52 ∧
      e % 110 ≠ 55 ∧
      e % 112 ≠ 56 ∧
      e % 114 ≠ 57 ∧
      e % 118 ≠ 59 ∧
      e % 124 ≠ 62 ∧
      e % 126 ≠ 63 ∧
      e % 128 ≠ 64 ∧
      e % 130 ≠ 65 ∧
      e % 134 ≠ 67 ∧
      e % 136 ≠ 68 ∧
      e % 138 ≠ 69 ∧
      e % 148 ≠ 74 ∧
      e % 152 ≠ 76 ∧
      e % 154 ≠ 77 ∧
      e % 160 ≠ 80 ∧
      e % 164 ≠ 82 ∧
      e % 166 ≠ 83 ∧
      e % 170 ≠ 85 ∧
      e % 172 ≠ 86 ∧
      e % 182 ≠ 91 ∧
      e % 188 ≠ 94 ∧
      e % 190 ≠ 95 ∧
      e % 194 ≠ 97 ∧
      e % 212 ≠ 106 ∧
      e % 224 ≠ 112 ∧
      e % 230 ≠ 115 ∧
      e % 232 ≠ 116 ∧
      e % 236 ≠ 118 ∧
      e % 238 ≠ 119 ∧
      e % 242 ≠ 121 ∧
      e % 244 ≠ 122 ∧
      e % 246 ≠ 123 ∧
      e % 248 ≠ 124 ∧
      e % 262 ≠ 131 ∧
      e % 266 ≠ 133 ∧
      e % 268 ≠ 134 ∧
      e % 282 ≠ 141 ∧
      e % 284 ≠ 142 ∧
      e % 286 ≠ 143 ∧
      e % 292 ≠ 146 ∧
      e % 294 ≠ 147 ∧
      e % 298 ≠ 149 ∧
      e % 304 ≠ 152 ∧
      e % 310 ≠ 155 ∧
      e % 314 ≠ 157)
    (w : e % 30 ≠ 15 ∧ e % 32 ≠ 16 ∧ e % 34 ≠ 17 ∧ e % 38 ≠ 19) :
    ∀ d ∈ ({10, 12, 14, 15, 16, 17, 18, 19, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38,
      39, 45, 46, 48, 51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82,
      83, 85, 86, 91, 94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133,
      134, 141, 142, 143, 146, 147, 149, 152, 155, 157} : Finset ℕ), e % (2 * d) ≠ d := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68⟩ := h
  obtain ⟨w0, w1, w2, w3⟩ := w
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max (max A1 A2) (max A3 (padicValNat 2 90)), fun n h hiff _ _ => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have he2 : 2 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).mp h3sq.2.2
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  have hGc := three_two_adic_residues h h3n hs
  have hG := odd_mul_two_general hGc
  rw [ha] at hG
  rcases Nat.lt_or_ge 200 (n.factorization 3) with hbig | hle
  · exact (h3 n h hiff hbig (odd_mul_three_200 (three_exponent_residues_200 h h3n hs)) hG).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have b1 : ∀ x, x ≤ A1 → x ≤ max (max A1 A2) (max A3 (padicValNat 2 90)) :=
    fun x hx => hx.trans ((le_max_left _ _).trans (le_max_left _ _))
  have b2 : ∀ x, x ≤ A2 → x ≤ max (max A1 A2) (max A3 (padicValNat 2 90)) :=
    fun x hx => hx.trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases three_exponent_cases_200 h he2 hle hs with h90 | he | he | he | he | he
  · subst h90
    exact (le_max_right _ _).trans (le_max_right _ _)
  · have hw := odd_mul_two_e57 hGc (three_e57_weight_residues h (Or.inl he) hs)
    rw [ha] at hw
    exact b1 _ (h1 n h hiff (Or.inl he) hw)
  · have hw := odd_mul_two_e57 hGc (three_e57_weight_residues h (Or.inr he) hs)
    rw [ha] at hw
    exact b1 _ (h1 n h hiff (Or.inr he) hw)
  · rw [he] at E
    have hsh := core3e11_two_adic_shape hP E
    rw [ha] at hsh
    refine b2 _ (h2 n h hiff (Or.inl he) hG (fun _ d hd => ?_) (fun h' => by omega)
      (fun h' => by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> omega
  · rw [he] at E
    have hsh := core3e13_two_adic_shape hP E
    rw [ha] at hsh
    refine b2 _ (h2 n h hiff (Or.inr (Or.inl he)) hG (fun h' => by omega) (fun _ d hd => ?_)
      (fun h' => by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> omega
  · rw [he] at E
    have hsh := core3e19_two_adic_shape hP E
    rw [ha] at hsh
    refine b2 _ (h2 n h hiff (Or.inr (Or.inr he)) hG (fun h' => by omega) (fun h' => by omega)
      (fun _ d hd => ?_))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1
