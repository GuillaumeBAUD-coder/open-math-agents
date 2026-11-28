import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1
import Mathlib

-- Step Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2.R1.H1: hypothesis H1 of
-- reduction Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2.R1
-- Credit: @ivillar. Witness: the prime factors 2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519 of the
-- primary pseudoperfect number 8490421583559688410706771261086 (OEIS A054377); the three large
-- primes are certified with Lucas (Pratt) certificates.

/-! Eight primes forming a primary pseudoperfect set. -/

namespace P7E313H1

lemma prime_2 : Nat.Prime 2 := by norm_num

lemma prime_3 : Nat.Prime 3 := by norm_num

lemma prime_7 : Nat.Prime 7 := by norm_num

lemma prime_11 : Nat.Prime 11 := by norm_num

lemma prime_23 : Nat.Prime 23 := by norm_num

lemma prime_29 : Nat.Prime 29 := by norm_num

lemma prime_31 : Nat.Prime 31 := by norm_num

lemma prime_27583 : Nat.Prime 27583 := by norm_num

lemma prime_47059 : Nat.Prime 47059 := by norm_num

lemma prime_398323 : Nat.Prime 398323 := by norm_num

lemma prime_100788283 : Nat.Prime 100788283 := by
  apply lucas_primality 100788283 7
  · change (7 : ZMod 100788283) ^ 100788282 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (100788283 : ℕ) - 1 = 2 ^ 1 * (3 ^ 2 * (7 ^ 1 * (29 ^ 1 * (27583 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (7 : ZMod 100788283) ^ 50394141 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (7 : ZMod 100788283) ^ 33596094 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_7 h
      subst r
      change (7 : ZMod 100788283) ^ 14398326 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_29 h
      subst r
      change (7 : ZMod 100788283) ^ 3475458 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_27583 h
      subst r
      change (7 : ZMod 100788283) ^ 3654 ≠ 1
      reduce_mod_char
      decide

lemma prime_2217342227 : Nat.Prime 2217342227 := by
  apply lucas_primality 2217342227 2
  · change (2 : ZMod 2217342227) ^ 2217342226 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (2217342227 : ℕ) - 1 = 2 ^ 1 * (11 ^ 1 * (100788283 ^ 1)) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 2217342227) ^ 1108671113 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_11 h
      subst r
      change (2 : ZMod 2217342227) ^ 201576566 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_100788283 h
      subst r
      change (2 : ZMod 2217342227) ^ 22 ≠ 1
      reduce_mod_char
      decide

lemma prime_78595501069 : Nat.Prime 78595501069 := by
  apply lucas_primality 78595501069 2
  · change (2 : ZMod 78595501069) ^ 78595501068 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (78595501069 : ℕ) - 1 = 2 ^ 2 * (3 ^ 5 * (7 ^ 1 * (29 ^ 1 * (398323 ^ 1)))) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (2 : ZMod 78595501069) ^ 39297750534 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_3 h
      subst r
      change (2 : ZMod 78595501069) ^ 26198500356 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_7 h
      subst r
      change (2 : ZMod 78595501069) ^ 11227928724 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_29 h
      subst r
      change (2 : ZMod 78595501069) ^ 2710189692 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_398323 h
      subst r
      change (2 : ZMod 78595501069) ^ 197316 ≠ 1
      reduce_mod_char
      decide

lemma prime_1729101023519 : Nat.Prime 1729101023519 := by
  apply lucas_primality 1729101023519 11
  · change (11 : ZMod 1729101023519) ^ 1729101023518 = 1
    reduce_mod_char
  · intro r hr hd
    rw [show (1729101023519 : ℕ) - 1 = 2 ^ 1 * (11 ^ 1 * (78595501069 ^ 1)) by decide] at hd
    simp only [hr.dvd_mul] at hd
    rcases hd with h | h | h
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_2 h
      subst r
      change (11 : ZMod 1729101023519) ^ 864550511759 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_11 h
      subst r
      change (11 : ZMod 1729101023519) ^ 157191002138 ≠ 1
      reduce_mod_char
      decide
    · have heq := Nat.prime_eq_prime_of_dvd_pow hr prime_78595501069 h
      subst r
      change (11 : ZMod 1729101023519) ^ 22 ≠ 1
      reduce_mod_char
      decide

end P7E313H1

open P7E313H1

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H1
  refine ⟨{2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519}, by decide, ⟨2, by simp⟩, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_11
    · exact prime_23
    · exact prime_31
    · exact prime_47059
    · exact prime_2217342227
    · exact prime_1729101023519
  · decide
  · rw [← sub_pos]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

