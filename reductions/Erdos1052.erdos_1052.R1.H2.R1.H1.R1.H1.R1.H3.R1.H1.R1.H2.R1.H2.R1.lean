import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H1.R1.H2.R1.H2.R1
-- Credit: @heavydawson
-- Exploits the forced prime 41 | 1 + 3^764 (giving 7 | 41 + 1) to eliminate nine consecutive
-- 2-adic valuation layers of a = padicValNat 2 n (v2(a) in {4, 5, 6, 7, 8, 9, 10, 11, 12}, i.e.
-- Fermat powers d = 16, 32, 64, 128, 256, 512, 1024, 2048, 4096) together with d = 6, 36, 72.
-- Splits the remaining even-a case into four branches:
--   H1: a % 4 = 2 and a % 12 != 6
--   H2: a % 8 = 4 and a % 72 != 36
--   H3: a % 16 = 8 and a % 144 != 72
--   H4: 8192 | a (v2(a) >= 13)

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1 hiding H1 H2 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n % 12 ≠ 6 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 8 = 4 →
    padicValNat 2 n % 72 ≠ 36 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 16 = 8 →
    padicValNat 2 n % 144 ≠ 72 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 764 →
    padicValNat 2 n % 8192 = 0 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- Section 1: Lucas primality certificates for Fermat chain primes.

theorem prime_1896229 : Nat.Prime 1896229 := by
  refine lucas_primality 1896229 (2 : ZMod 1896229) ?_ (fun q hq hd => ?_)
  · rw [show 1896229 - 1 = 1896228 from by norm_num]
    reduce_mod_char
  · have e : 1896229 - 1 = [2 ^ 2, 3 ^ 2, 52673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1896229 - 1) / 2 = 948114 from by norm_num]
      have h2 : (2 : ZMod 1896229) ^ 948114 = ((1896228 : ℕ) : ZMod 1896229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1896229 - 1) / 3 = 632076 from by norm_num]
      have h2 : (2 : ZMod 1896229) ^ 632076 = ((1634291 : ℕ) : ZMod 1896229) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1896229 - 1) / 52673 = 36 from by norm_num]
      have h2 : (2 : ZMod 1896229) ^ 36 = ((137776 : ℕ) : ZMod 1896229) := by
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
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1896229).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 1896229 = 9774 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 9774 = ((16378712013 : ℕ) : ZMod 18533742247) := by
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

theorem prime_6487031809 : Nat.Prime 6487031809 := by
  refine lucas_primality 6487031809 (7 : ZMod 6487031809) ?_ (fun q hq hd => ?_)
  · rw [show 6487031809 - 1 = 6487031808 from by norm_num]
    reduce_mod_char
  · have e : 6487031809 - 1 = [2 ^ 14, 3 ^ 2, 29 ^ 1, 37 ^ 1, 41 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 2 = 3243515904 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 3243515904 = ((6487031808 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 3 = 2162343936 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 2162343936 = ((370700344 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 29 = 223690752 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 223690752 = ((1706837087 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 37 = 175325184 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 175325184 = ((2803872759 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 41 = 158220288 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 158220288 = ((2843121849 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2424833 : Nat.Prime 2424833 := by
  refine lucas_primality 2424833 (3 : ZMod 2424833) ?_ (fun q hq hd => ?_)
  · rw [show 2424833 - 1 = 2424832 from by norm_num]
    reduce_mod_char
  · have e : 2424833 - 1 = [2 ^ 16, 37 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2424833 - 1) / 2 = 1212416 from by norm_num]
      have h2 : (3 : ZMod 2424833) ^ 1212416 = ((2424832 : ℕ) : ZMod 2424833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2424833 - 1) / 37 = 65536 from by norm_num]
      have h2 : (3 : ZMod 2424833) ^ 65536 = ((2139377 : ℕ) : ZMod 2424833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_26017793 : Nat.Prime 26017793 := by
  refine lucas_primality 26017793 (3 : ZMod 26017793) ?_ (fun q hq hd => ?_)
  · rw [show 26017793 - 1 = 26017792 from by norm_num]
    reduce_mod_char
  · have e : 26017793 - 1 = [2 ^ 16, 397 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26017793 - 1) / 2 = 13008896 from by norm_num]
      have h2 : (3 : ZMod 26017793) ^ 13008896 = ((26017792 : ℕ) : ZMod 26017793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26017793 - 1) / 397 = 65536 from by norm_num]
      have h2 : (3 : ZMod 26017793) ^ 65536 = ((6782830 : ℕ) : ZMod 26017793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)


-- Section 2: Balance equation setup and modular divisibility helper.

theorem dvd_two_pow_add_one {p d : ℕ}
    (h : ((2 : ZMod p) ^ d + 1) = 0) : p ∣ 2 ^ d + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

theorem dvd_41_3_764 : 41 ∣ 1 + 3 ^ 764 := by
  have h1 : 41 ∣ 1 + 3 ^ 4 := by norm_num
  have h2 : 1 + 3 ^ 4 ∣ 1 + 3 ^ 764 := one_add_pow_dvd_of_odd_mul (by norm_num : 764 % (2 * 4) = 4)
  exact h1.trans h2

theorem balance_764 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3)
    (he : n.factorization 3 = 764) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (2 ^ padicValNat 2 n + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * 3 ^ 764 * ∏ p ∈ P, p := by
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
  rw [he, Nat.factorization_def n Nat.prime_two] at E
  exact ⟨_, hP, E⟩

theorem dvd_two_pow_of_odd_mul {a d : ℕ} (hmod : a % (2 * d) = d) :
    2 ^ d + 1 ∣ 2 ^ a + 1 := by
  have h := one_add_pow_dvd_of_odd_mul (z := 2) hmod
  rwa [add_comm 1 (2 ^ d), add_comm 1 (2 ^ a)] at h

-- Section 3: Kill lemmas using 41 | 1 + 3^764 (forcing 41 in P and 7 | 41 + 1).

theorem kill_d6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 6 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g13 : 13 ∈ P := S2 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13 ∣ 2 ^ 6 + 1).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g13 (by norm_num) (by norm_num)
  omega

theorem kill_d16 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 16 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g65537 : 65537 ∈ P := S2 65537 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 65537 ∣ 2 ^ 16 + 1).trans hd)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 65537 g65537 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 83 g83 (by norm_num) (by norm_num)
  omega

theorem kill_d36 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 36 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have g241 : 241 ∈ P := S2 241 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 241 g241 (by norm_num)

theorem kill_d72 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 72 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have g577 : 577 ∈ P := S2 577 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 577 g577 (by norm_num)

theorem kill_d128 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 128 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g1 : 59649589127497217 ∈ P := S2 59649589127497217 prime_59649589127497217 (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  have g2 : 13562889751591 ∈ P := S1 13562889751591 prime_13562889751591 (by norm_num) (hnz (by norm_num))
    59649589127497217 g1 (by norm_num)
  have g3 : 37967 ∈ P := S1 37967 (by norm_num) (by norm_num) (hnz (by norm_num))
    13562889751591 g2 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 37967 g3 (by norm_num) (by norm_num)
  omega

theorem kill_d256 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 256 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g1 : 1238926361552897 ∈ P := S2 1238926361552897 prime_1238926361552897 (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  have g2 : 206487726925483 ∈ P := S1 206487726925483 prime_206487726925483 (by norm_num) (hnz (by norm_num))
    1238926361552897 g1 (by norm_num)
  have g3 : 11621 ∈ P := S1 11621 (by norm_num) (by norm_num) (hnz (by norm_num))
    206487726925483 g2 (by norm_num)
  have g4 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num))
    11621 g3 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 13 g4 (by norm_num) (by norm_num)
  omega

theorem kill_d512 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 512 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g1 : 2424833 ∈ P := S2 2424833 prime_2424833 (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  have g2 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num))
    2424833 g1 (by norm_num)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 1259 g2 (by norm_num) (by norm_num)
  omega

theorem kill_d1024 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 1024 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP hK E
  have g41 : 41 ∈ P := S7 41 (by norm_num) (by norm_num) (hnz (by norm_num)) dvd_41_3_764
  have g1 : 6487031809 ∈ P := S2 6487031809 prime_6487031809 (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  have := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41 g41 6487031809 g1 (by norm_num) (by norm_num)
  omega

theorem kill_d2048 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 2048 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have g1 : 974849 ∈ P := S2 974849 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 974849 g1 (by norm_num)

theorem kill_d4096 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 764) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 764 * ∏ p ∈ P, p)
    (hd : 2 ^ 4096 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 764 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP hK E
  have g1 : 26017793 ∈ P := S2 26017793 prime_26017793 (by norm_num) (hnz (by norm_num))
    ((dvd_two_pow_add_one (by reduce_mod_char)).trans hd)
  have g2 : 43801 ∈ P := S1 43801 (by norm_num) (by norm_num) (hnz (by norm_num))
    26017793 g1 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43801 g2 (by norm_num)

theorem mod_double_zero {a k : ℕ} (h1 : a % k = 0) (h2 : a % (2 * k) ≠ k) : a % (2 * k) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h1
  have hmul : k * q % (2 * k) = k * (q % 2) := by
    rw [mul_comm 2 k, Nat.mul_mod_mul_left]
  rw [hmul] at h2 ⊢
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq <;> simp [hq] at h2 ⊢

-- Section 4: Main reduction.

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨max (max A1 A2) (max A3 A4), fun n h hiff he heven hG => ?_⟩
  obtain ⟨P, hP, E⟩ := balance_764 h hiff he
  by_cases h4m : padicValNat 2 n % 4 = 2
  · have h6 : padicValNat 2 n % 12 ≠ 6 := fun hm =>
      kill_d6 hP E (dvd_two_pow_of_odd_mul hm)
    exact (h1 n h hiff he h4m h6 hG).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · have hm4 : padicValNat 2 n % 4 = 0 := mod_double_zero heven h4m
    by_cases h8m : padicValNat 2 n % 8 = 4
    · have h36 : padicValNat 2 n % 72 ≠ 36 := fun hm =>
        kill_d36 hP E (dvd_two_pow_of_odd_mul hm)
      exact (h2 n h hiff he h8m h36 hG).trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · have hm8 : padicValNat 2 n % 8 = 0 := mod_double_zero hm4 h8m
      by_cases h16m : padicValNat 2 n % 16 = 8
      · have h72 : padicValNat 2 n % 144 ≠ 72 := fun hm =>
          kill_d72 hP E (dvd_two_pow_of_odd_mul hm)
        exact (h3 n h hiff he h16m h72 hG).trans (le_trans (le_max_left _ _) (le_max_right _ _))
      · have h16 : padicValNat 2 n % 16 = 0 := mod_double_zero hm8 h16m
        have h32 : padicValNat 2 n % 32 = 0 := mod_double_zero h16 fun hm =>
          kill_d16 hP E (dvd_two_pow_of_odd_mul hm)
        have h64 : padicValNat 2 n % 64 = 0 := mod_double_zero h32 (hG 32 (by simp))
        have h128 : padicValNat 2 n % 128 = 0 := mod_double_zero h64 (hG 64 (by simp))
        have h256 : padicValNat 2 n % 256 = 0 := mod_double_zero h128 fun hm =>
          kill_d128 hP E (dvd_two_pow_of_odd_mul hm)
        have h512 : padicValNat 2 n % 512 = 0 := mod_double_zero h256 fun hm =>
          kill_d256 hP E (dvd_two_pow_of_odd_mul hm)
        have h1024 : padicValNat 2 n % 1024 = 0 := mod_double_zero h512 fun hm =>
          kill_d512 hP E (dvd_two_pow_of_odd_mul hm)
        have h2048 : padicValNat 2 n % 2048 = 0 := mod_double_zero h1024 fun hm =>
          kill_d1024 hP E (dvd_two_pow_of_odd_mul hm)
        have h4096 : padicValNat 2 n % 4096 = 0 := mod_double_zero h2048 fun hm =>
          kill_d2048 hP E (dvd_two_pow_of_odd_mul hm)
        have h8192 : padicValNat 2 n % 8192 = 0 := mod_double_zero h4096 fun hm =>
          kill_d4096 hP E (dvd_two_pow_of_odd_mul hm)
        exact (h4 n h hiff he h8192 hG).trans (le_trans (le_max_right _ _) (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H2_R1_H2_R1
