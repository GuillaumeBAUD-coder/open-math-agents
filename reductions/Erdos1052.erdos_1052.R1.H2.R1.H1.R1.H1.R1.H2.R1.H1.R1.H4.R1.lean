import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H4_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1 hiding H1 H2 H3 H4 main

-- H1: 2^20 || a (a mod 2^21 = 2^20).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 ^ 21 = 2 ^ 20 →
    padicValNat 2 n ≤ A

-- H2: 2^24 || a (a mod 2^25 = 2^24).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 2 ^ 25 = 2 ^ 24 →
    padicValNat 2 n ≤ A

-- H3: 2^33 divides a.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    2 ^ 33 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

theorem zmod_sq_step {q a b : ℕ} (h : (a * a) % q = b) :
    ((a : ℕ) : ZMod q) ^ 2 = ((b : ℕ) : ZMod q) := by
  rw [sq, ← Nat.cast_mul, ← ZMod.natCast_mod (a * a) q, h]

theorem dvd_two_pow_two_pow_add_one {k q : ℕ} (hq : 0 < q)
    (h : (2 : ZMod q) ^ 2 ^ k = ((q - 1 : ℕ) : ZMod q)) : q ∣ 2 ^ 2 ^ k + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [h, ← Nat.cast_add_one, Nat.sub_add_cancel hq, ZMod.natCast_self]

theorem cert_13981013 : Nat.Prime 13981013 := by
  refine lucas_primality 13981013 (2 : ZMod 13981013) ?_ (fun q hq hd => ?_)
  · rw [show 13981013 - 1 = 13981012 from by norm_num]
    reduce_mod_char
  · have e : 13981013 - 1 = [2 ^ 2, 3495253 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13981013 - 1) / 2 = 6990506 from by norm_num]
      have h2 : (2 : ZMod 13981013) ^ 6990506 = ((13981012 : ℕ) : ZMod 13981013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13981013 - 1) / 3495253 = 4 from by norm_num]
      have h2 : (2 : ZMod 13981013) ^ 4 = ((16 : ℕ) : ZMod 13981013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_16149761 : Nat.Prime 16149761 := by
  refine lucas_primality 16149761 (6 : ZMod 16149761) ?_ (fun q hq hd => ?_)
  · rw [show 16149761 - 1 = 16149760 from by norm_num]
    reduce_mod_char
  · have e : 16149761 - 1 = [2 ^ 8, 5 ^ 1, 11 ^ 1, 31 ^ 1, 37 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16149761 - 1) / 2 = 8074880 from by norm_num]
      have h2 : (6 : ZMod 16149761) ^ 8074880 = ((16149760 : ℕ) : ZMod 16149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16149761 - 1) / 5 = 3229952 from by norm_num]
      have h2 : (6 : ZMod 16149761) ^ 3229952 = ((5865729 : ℕ) : ZMod 16149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16149761 - 1) / 11 = 1468160 from by norm_num]
      have h2 : (6 : ZMod 16149761) ^ 1468160 = ((5353097 : ℕ) : ZMod 16149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16149761 - 1) / 31 = 520960 from by norm_num]
      have h2 : (6 : ZMod 16149761) ^ 520960 = ((13929959 : ℕ) : ZMod 16149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (16149761 - 1) / 37 = 436480 from by norm_num]
      have h2 : (6 : ZMod 16149761) ^ 436480 = ((13380085 : ℕ) : ZMod 16149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_26114321 : Nat.Prime 26114321 := by
  refine lucas_primality 26114321 (3 : ZMod 26114321) ?_ (fun q hq hd => ?_)
  · rw [show 26114321 - 1 = 26114320 from by norm_num]
    reduce_mod_char
  · have e : 26114321 - 1 = [2 ^ 4, 5 ^ 1, 197 ^ 1, 1657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26114321 - 1) / 2 = 13057160 from by norm_num]
      have h2 : (3 : ZMod 26114321) ^ 13057160 = ((26114320 : ℕ) : ZMod 26114321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26114321 - 1) / 5 = 5222864 from by norm_num]
      have h2 : (3 : ZMod 26114321) ^ 5222864 = ((6992451 : ℕ) : ZMod 26114321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26114321 - 1) / 197 = 132560 from by norm_num]
      have h2 : (3 : ZMod 26114321) ^ 132560 = ((19990516 : ℕ) : ZMod 26114321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (26114321 - 1) / 1657 = 15760 from by norm_num]
      have h2 : (3 : ZMod 26114321) ^ 15760 = ((9268749 : ℕ) : ZMod 26114321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_27536591 : Nat.Prime 27536591 := by
  refine lucas_primality 27536591 (11 : ZMod 27536591) ?_ (fun q hq hd => ?_)
  · rw [show 27536591 - 1 = 27536590 from by norm_num]
    reduce_mod_char
  · have e : 27536591 - 1 = [2 ^ 1, 5 ^ 1, 431 ^ 1, 6389 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27536591 - 1) / 2 = 13768295 from by norm_num]
      have h2 : (11 : ZMod 27536591) ^ 13768295 = ((27536590 : ℕ) : ZMod 27536591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27536591 - 1) / 5 = 5507318 from by norm_num]
      have h2 : (11 : ZMod 27536591) ^ 5507318 = ((17695909 : ℕ) : ZMod 27536591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27536591 - 1) / 431 = 63890 from by norm_num]
      have h2 : (11 : ZMod 27536591) ^ 63890 = ((18907095 : ℕ) : ZMod 27536591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27536591 - 1) / 6389 = 4310 from by norm_num]
      have h2 : (11 : ZMod 27536591) ^ 4310 = ((25461874 : ℕ) : ZMod 27536591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_27962027 : Nat.Prime 27962027 := by
  refine lucas_primality 27962027 (2 : ZMod 27962027) ?_ (fun q hq hd => ?_)
  · rw [show 27962027 - 1 = 27962026 from by norm_num]
    reduce_mod_char
  · have e : 27962027 - 1 = [2 ^ 1, 13981013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27962027 - 1) / 2 = 13981013 from by norm_num]
      have h2 : (2 : ZMod 27962027) ^ 13981013 = ((27962026 : ℕ) : ZMod 27962027) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_13981013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (27962027 - 1) / 13981013 = 2 from by norm_num]
      have h2 : (2 : ZMod 27962027) ^ 2 = ((4 : ℕ) : ZMod 27962027) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_167772161 : Nat.Prime 167772161 := by
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

theorem cert_1045429261 : Nat.Prime 1045429261 := by
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

theorem cert_2404314443 : Nat.Prime 2404314443 := by
  refine lucas_primality 2404314443 (2 : ZMod 2404314443) ?_ (fun q hq hd => ?_)
  · rw [show 2404314443 - 1 = 2404314442 from by norm_num]
    reduce_mod_char
  · have e : 2404314443 - 1 = [2 ^ 1, 251 ^ 1, 4789471 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2404314443 - 1) / 2 = 1202157221 from by norm_num]
      have h2 : (2 : ZMod 2404314443) ^ 1202157221 = ((2404314442 : ℕ) : ZMod 2404314443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2404314443 - 1) / 251 = 9578942 from by norm_num]
      have h2 : (2 : ZMod 2404314443) ^ 9578942 = ((1613899799 : ℕ) : ZMod 2404314443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2404314443 - 1) / 4789471 = 502 from by norm_num]
      have h2 : (2 : ZMod 2404314443) ^ 502 = ((2092616710 : ℕ) : ZMod 2404314443) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_14425886659 : Nat.Prime 14425886659 := by
  refine lucas_primality 14425886659 (2 : ZMod 14425886659) ?_ (fun q hq hd => ?_)
  · rw [show 14425886659 - 1 = 14425886658 from by norm_num]
    reduce_mod_char
  · have e : 14425886659 - 1 = [2 ^ 1, 3 ^ 1, 2404314443 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14425886659 - 1) / 2 = 7212943329 from by norm_num]
      have h2 : (2 : ZMod 14425886659) ^ 7212943329 = ((14425886658 : ℕ) : ZMod 14425886659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14425886659 - 1) / 3 = 4808628886 from by norm_num]
      have h2 : (2 : ZMod 14425886659) ^ 4808628886 = ((4763228115 : ℕ) : ZMod 14425886659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_2404314443).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14425886659 - 1) / 2404314443 = 6 from by norm_num]
      have h2 : (2 : ZMod 14425886659) ^ 6 = ((64 : ℕ) : ZMod 14425886659) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_28851773317 : Nat.Prime 28851773317 := by
  refine lucas_primality 28851773317 (5 : ZMod 28851773317) ?_ (fun q hq hd => ?_)
  · rw [show 28851773317 - 1 = 28851773316 from by norm_num]
    reduce_mod_char
  · have e : 28851773317 - 1 = [2 ^ 2, 3 ^ 1, 2404314443 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28851773317 - 1) / 2 = 14425886658 from by norm_num]
      have h2 : (5 : ZMod 28851773317) ^ 14425886658 = ((28851773316 : ℕ) : ZMod 28851773317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28851773317 - 1) / 3 = 9617257772 from by norm_num]
      have h2 : (5 : ZMod 28851773317) ^ 9617257772 = ((7250530766 : ℕ) : ZMod 28851773317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_2404314443).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28851773317 - 1) / 2404314443 = 12 from by norm_num]
      have h2 : (5 : ZMod 28851773317) ^ 12 = ((244140625 : ℕ) : ZMod 28851773317) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_38222840587 : Nat.Prime 38222840587 := by
  refine lucas_primality 38222840587 (3 : ZMod 38222840587) ?_ (fun q hq hd => ?_)
  · rw [show 38222840587 - 1 = 38222840586 from by norm_num]
    reduce_mod_char
  · have e : 38222840587 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 67 ^ 1, 439 ^ 1, 30941 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 2 = 19111420293 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 19111420293 = ((38222840586 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 3 = 12740946862 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 12740946862 = ((37992920057 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 7 = 5460405798 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 5460405798 = ((27495879404 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 67 = 570490158 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 570490158 = ((5261433763 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 439 = 87067974 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 87067974 = ((23809751133 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (38222840587 - 1) / 30941 = 1235346 from by norm_num]
      have h2 : (3 : ZMod 38222840587) ^ 1235346 = ((9326614050 : ℕ) : ZMod 38222840587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_52795084261 : Nat.Prime 52795084261 := by
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

theorem cert_140091319777 : Nat.Prime 140091319777 := by
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

theorem cert_4485296422913 : Nat.Prime 4485296422913 := by
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

theorem cert_12704513261569 : Nat.Prime 12704513261569 := by
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

theorem cert_12810187352747 : Nat.Prime 12810187352747 := by
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
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_27536591).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12810187352747 - 1) / 27536591 = 465206 from by norm_num]
      have h2 : (2 : ZMod 12810187352747) ^ 465206 = ((90982695622 : ℕ) : ZMod 12810187352747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_25409026523137 : Nat.Prime 25409026523137 := by
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

theorem cert_25991531462657 : Nat.Prime 25991531462657 := by
  refine lucas_primality 25991531462657 (3 : ZMod 25991531462657) ?_ (fun q hq hd => ?_)
  · rw [show 25991531462657 - 1 = 25991531462656 from by norm_num]
    reduce_mod_char
  · have e : 25991531462657 - 1 = [2 ^ 29, 48413 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25991531462657 - 1) / 2 = 12995765731328 from by norm_num]
      have h2 : (3 : ZMod 25991531462657) ^ 12995765731328 = ((25991531462656 : ℕ) : ZMod 25991531462657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (25991531462657 - 1) / 48413 = 536870912 from by norm_num]
      have h2 : (3 : ZMod 25991531462657) ^ 536870912 = ((23187224625299 : ℕ) : ZMod 25991531462657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_76861124116481 : Nat.Prime 76861124116481 := by
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

theorem cert_133627050692153 : Nat.Prime 133627050692153 := by
  refine lucas_primality 133627050692153 (3 : ZMod 133627050692153) ?_ (fun q hq hd => ?_)
  · rw [show 133627050692153 - 1 = 133627050692152 from by norm_num]
    reduce_mod_char
  · have e : 133627050692153 - 1 = [2 ^ 3, 19 ^ 1, 23 ^ 1, 38222840587 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133627050692153 - 1) / 2 = 66813525346076 from by norm_num]
      have h2 : (3 : ZMod 133627050692153) ^ 66813525346076 = ((133627050692152 : ℕ) : ZMod 133627050692153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133627050692153 - 1) / 19 = 7033002668008 from by norm_num]
      have h2 : (3 : ZMod 133627050692153) ^ 7033002668008 = ((133113435492595 : ℕ) : ZMod 133627050692153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133627050692153 - 1) / 23 = 5809871769224 from by norm_num]
      have h2 : (3 : ZMod 133627050692153) ^ 5809871769224 = ((50127744365346 : ℕ) : ZMod 133627050692153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_38222840587).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (133627050692153 - 1) / 38222840587 = 3496 from by norm_num]
      have h2 : (3 : ZMod 133627050692153) ^ 3496 = ((121489651625876 : ℕ) : ZMod 133627050692153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_151413703311361 : Nat.Prime 151413703311361 := by
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

theorem cert_640126220763137 : Nat.Prime 640126220763137 := by
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

theorem cert_2405286912458753 : Nat.Prime 2405286912458753 := by
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

theorem cert_1766730974551267606529 : Nat.Prime 1766730974551267606529 := by
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

theorem cert_46931635677864055013377 : Nat.Prime 46931635677864055013377 := by
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
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_140091319777).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (46931635677864055013377 - 1) / 140091319777 = 335007449088 from by norm_num]
      have h2 : (5 : ZMod 46931635677864055013377) ^ 335007449088 = ((24553789991219906639167 : ℕ) : ZMod 46931635677864055013377) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem cert_64658705994591851009055774868504577 : Nat.Prime 64658705994591851009055774868504577 := by
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
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_1045429261).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 1045429261 = 61848953732883750810812416 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 61848953732883750810812416 = ((5579996185421350680871962834478292 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq cert_52795084261).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64658705994591851009055774868504577 - 1) / 52795084261 = 1224710726380174931132416 from by norm_num]
      have h2 : (3 : ZMod 64658705994591851009055774868504577) ^ 1224710726380174931132416 = ((53743358277992979144433879976849567 : ℕ) : ZMod 64658705994591851009055774868504577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem dvd_F21 : 4485296422913 ∣ 2 ^ 2 ^ 21 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 4485296422913) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 4485296422913) := by norm_num
  have s1 : (2 : ZMod 4485296422913) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 4485296422913) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 4485296422913) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 4485296422913) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 4485296422913) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 4485296422913) ^ 2 ^ 6 = ((2681045335734 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 4485296422913) ^ 2 ^ 7 = ((2526827132735 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 4485296422913) ^ 2 ^ 8 = ((1850727711881 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 4485296422913) ^ 2 ^ 9 = ((799655977055 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 4485296422913) ^ 2 ^ 10 = ((1992980664694 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 4485296422913) ^ 2 ^ 11 = ((1428076237607 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 4485296422913) ^ 2 ^ 12 = ((191834108361 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 4485296422913) ^ 2 ^ 13 = ((931417385166 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 4485296422913) ^ 2 ^ 14 = ((646865695460 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 4485296422913) ^ 2 ^ 15 = ((1788844105822 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 4485296422913) ^ 2 ^ 16 = ((48628813748 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 4485296422913) ^ 2 ^ 17 = ((3128558077167 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 4485296422913) ^ 2 ^ 18 = ((1282825594311 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 4485296422913) ^ 2 ^ 19 = ((173424391284 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 4485296422913) ^ 2 ^ 20 = ((4114310363993 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 4485296422913) ^ 2 ^ 21 = ((4485296422912 : ℕ) : ZMod 4485296422913) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  exact s21

theorem k_fermat_21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 21 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4485296422913 : 4485296422913 ∈ P := S2 4485296422913 cert_4485296422913 (by norm_num) (hnz (by norm_num)) (dvd_F21.trans hd)
  have g10487 : 10487 ∈ P := S1 10487 (by norm_num) (by norm_num) (hnz (by norm_num)) 4485296422913 g4485296422913 (by norm_num)
  have g81281 : 81281 ∈ P := S1 81281 (by norm_num) (by norm_num) (hnz (by norm_num)) 4485296422913 g4485296422913 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 10487 g10487 81281 g81281 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F22 : 64658705994591851009055774868504577 ∣ 2 ^ 2 ^ 22 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 64658705994591851009055774868504577) := by norm_num
  have s1 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 6 = ((18446744073709551616 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 7 = ((48255977396143453723120073697127282 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 8 = ((58865102006259746088798231097310509 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 9 = ((44639355360823436294527494019393460 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 10 = ((52069179847335574546934500896144614 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 11 = ((17806126219782433817699203006391888 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 12 = ((44190688468052235435872536955138020 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 13 = ((63305649855444999067484952276163523 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 14 = ((38604196552396478617365426174493989 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 15 = ((38892652859877639977046987933329419 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 16 = ((51206241010604613279582785312976071 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 17 = ((32758883320593386525985356815339958 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 18 = ((37503060576126463298028676460583099 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 19 = ((4275978816384749998247721382240844 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 20 = ((23190175009078168218865198675526703 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 21 = ((33574698357578368617172669732108163 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 64658705994591851009055774868504577) ^ 2 ^ 22 = ((64658705994591851009055774868504576 : ℕ) : ZMod 64658705994591851009055774868504577) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  exact s22

theorem k_fermat_22 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 22 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g64658705994591851009055774868504577 : 64658705994591851009055774868504577 ∈ P := S2 64658705994591851009055774868504577 cert_64658705994591851009055774868504577 (by norm_num) (hnz (by norm_num)) (dvd_F22.trans hd)
  have g67 : 67 ∈ P := S7 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g16149761 : 16149761 ∈ P := S1 16149761 cert_16149761 (by norm_num) (hnz (by norm_num)) 64658705994591851009055774868504577 g64658705994591851009055774868504577 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 16149761 g16149761 67 g67 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F23 : 167772161 ∣ 2 ^ 2 ^ 23 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 167772161) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 167772161) := by norm_num
  have s1 : (2 : ZMod 167772161) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 167772161) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 167772161) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 167772161) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 167772161) ^ 2 ^ 5 = ((100663271 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 167772161) ^ 2 ^ 6 = ((40265974 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 167772161) ^ 2 ^ 7 = ((8214125 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 167772161) ^ 2 ^ 8 = ((93931382 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 167772161) ^ 2 ^ 9 = ((131872124 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 167772161) ^ 2 ^ 10 = ((2027927 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 167772161) ^ 2 ^ 11 = ((56706897 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 167772161) ^ 2 ^ 12 = ((102469870 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 167772161) ^ 2 ^ 13 = ((42312541 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 167772161) ^ 2 ^ 14 = ((37665517 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 167772161) ^ 2 ^ 15 = ((46675951 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 167772161) ^ 2 ^ 16 = ((81947549 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 167772161) ^ 2 ^ 17 = ((101571374 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 167772161) ^ 2 ^ 18 = ((145321691 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 167772161) ^ 2 ^ 19 = ((128334446 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 167772161) ^ 2 ^ 20 = ((35921276 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 167772161) ^ 2 ^ 21 = ((30406922 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 167772161) ^ 2 ^ 22 = ((102522193 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 167772161) ^ 2 ^ 23 = ((167772160 : ℕ) : ZMod 167772161) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  exact s23

theorem k_fermat_23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 23 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g167772161 : 167772161 ∈ P := S2 167772161 cert_167772161 (by norm_num) (hnz (by norm_num)) (dvd_F23.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g27962027 : 27962027 ∈ P := S1 27962027 cert_27962027 (by norm_num) (hnz (by norm_num)) 167772161 g167772161 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 27962027 g27962027 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 103 g103 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F25 : 25991531462657 ∣ 2 ^ 2 ^ 25 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 25991531462657) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 25991531462657) := by norm_num
  have s1 : (2 : ZMod 25991531462657) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 25991531462657) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 25991531462657) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 25991531462657) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 25991531462657) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 25991531462657) ^ 2 ^ 6 = ((8372501162919 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 25991531462657) ^ 2 ^ 7 = ((21715727891197 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 25991531462657) ^ 2 ^ 8 = ((19558200498205 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 25991531462657) ^ 2 ^ 9 = ((23706872375112 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 25991531462657) ^ 2 ^ 10 = ((12660974231851 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 25991531462657) ^ 2 ^ 11 = ((12939651009417 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 25991531462657) ^ 2 ^ 12 = ((6085267008359 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 25991531462657) ^ 2 ^ 13 = ((15955559485679 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 25991531462657) ^ 2 ^ 14 = ((23978359484071 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 25991531462657) ^ 2 ^ 15 = ((11505682020718 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 25991531462657) ^ 2 ^ 16 = ((6593144992653 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 25991531462657) ^ 2 ^ 17 = ((24672535482695 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 25991531462657) ^ 2 ^ 18 = ((10822920246219 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 25991531462657) ^ 2 ^ 19 = ((4142709526792 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 25991531462657) ^ 2 ^ 20 = ((20340121868671 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 25991531462657) ^ 2 ^ 21 = ((10755542902475 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 25991531462657) ^ 2 ^ 22 = ((11867850599827 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 25991531462657) ^ 2 ^ 23 = ((24967359850601 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 25991531462657) ^ 2 ^ 24 = ((601642840661 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 25991531462657) ^ 2 ^ 25 = ((25991531462656 : ℕ) : ZMod 25991531462657) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  exact s25

theorem k_fermat_25 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 25 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25991531462657 : 25991531462657 ∈ P := S2 25991531462657 cert_25991531462657 (by norm_num) (hnz (by norm_num)) (dvd_F25.trans hd)
  have g26114321 : 26114321 ∈ P := S1 26114321 cert_26114321 (by norm_num) (hnz (by norm_num)) 25991531462657 g25991531462657 (by norm_num)
  exact S8 67 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 26114321 g26114321 (by norm_num)

theorem dvd_F26 : 76861124116481 ∣ 2 ^ 2 ^ 26 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 76861124116481) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 76861124116481) := by norm_num
  have s1 : (2 : ZMod 76861124116481) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 76861124116481) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 76861124116481) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 76861124116481) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 76861124116481) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 76861124116481) ^ 2 ^ 6 = ((74285754111616 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 76861124116481) ^ 2 ^ 7 = ((7359725573609 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 76861124116481) ^ 2 ^ 8 = ((15089448280686 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 76861124116481) ^ 2 ^ 9 = ((55555456352127 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 76861124116481) ^ 2 ^ 10 = ((74562582731366 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 76861124116481) ^ 2 ^ 11 = ((67671647127950 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 76861124116481) ^ 2 ^ 12 = ((5971968681488 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 76861124116481) ^ 2 ^ 13 = ((36098021144161 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 76861124116481) ^ 2 ^ 14 = ((6095994039544 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 76861124116481) ^ 2 ^ 15 = ((4431383751999 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 76861124116481) ^ 2 ^ 16 = ((46664583799909 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 76861124116481) ^ 2 ^ 17 = ((73143964265520 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 76861124116481) ^ 2 ^ 18 = ((45804336021236 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 76861124116481) ^ 2 ^ 19 = ((26780269872212 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 76861124116481) ^ 2 ^ 20 = ((26395039805551 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 76861124116481) ^ 2 ^ 21 = ((51325760957959 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 76861124116481) ^ 2 ^ 22 = ((34941364218173 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 76861124116481) ^ 2 ^ 23 = ((7719084484353 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 76861124116481) ^ 2 ^ 24 = ((3918257022383 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 76861124116481) ^ 2 ^ 25 = ((4572182500288 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 76861124116481) ^ 2 ^ 26 = ((76861124116480 : ℕ) : ZMod 76861124116481) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  exact s26

theorem k_fermat_26 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 26 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g76861124116481 : 76861124116481 ∈ P := S2 76861124116481 cert_76861124116481 (by norm_num) (hnz (by norm_num)) (dvd_F26.trans hd)
  have g12810187352747 : 12810187352747 ∈ P := S1 12810187352747 cert_12810187352747 (by norm_num) (hnz (by norm_num)) 76861124116481 g76861124116481 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 12810187352747 g12810187352747 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 37 g37 (by norm_num)
  have g28851773317 : 28851773317 ∈ P := S1 28851773317 cert_28851773317 (by norm_num) (hnz (by norm_num)) 12810187352747 g12810187352747 (by norm_num)
  have g14425886659 : 14425886659 ∈ P := S1 14425886659 cert_14425886659 (by norm_num) (hnz (by norm_num)) 28851773317 g28851773317 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 14425886659 g14425886659 19 g19 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F27 : 151413703311361 ∣ 2 ^ 2 ^ 27 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 151413703311361) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 151413703311361) := by norm_num
  have s1 : (2 : ZMod 151413703311361) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 151413703311361) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 151413703311361) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 151413703311361) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 151413703311361) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 151413703311361) ^ 2 ^ 6 = ((12599286440986 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 151413703311361) ^ 2 ^ 7 = ((21390467512808 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 151413703311361) ^ 2 ^ 8 = ((62068776454173 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 151413703311361) ^ 2 ^ 9 = ((33792566490858 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 151413703311361) ^ 2 ^ 10 = ((110761220673081 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 151413703311361) ^ 2 ^ 11 = ((144375796587399 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 151413703311361) ^ 2 ^ 12 = ((87277116202389 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 151413703311361) ^ 2 ^ 13 = ((11439986712934 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 151413703311361) ^ 2 ^ 14 = ((31068378356700 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 151413703311361) ^ 2 ^ 15 = ((93491663896178 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 151413703311361) ^ 2 ^ 16 = ((129345335748458 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 151413703311361) ^ 2 ^ 17 = ((118692307196770 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 151413703311361) ^ 2 ^ 18 = ((86814350978442 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 151413703311361) ^ 2 ^ 19 = ((30668882845044 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 151413703311361) ^ 2 ^ 20 = ((101879193405558 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 151413703311361) ^ 2 ^ 21 = ((120832742597745 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 151413703311361) ^ 2 ^ 22 = ((140707059208076 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 151413703311361) ^ 2 ^ 23 = ((93072304862705 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 151413703311361) ^ 2 ^ 24 = ((19332531381732 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 151413703311361) ^ 2 ^ 25 = ((96156337997341 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 151413703311361) ^ 2 ^ 26 = ((93782427441976 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 151413703311361) ^ 2 ^ 27 = ((151413703311360 : ℕ) : ZMod 151413703311361) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  exact s27

theorem k_fermat_27 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 27 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g151413703311361 : 151413703311361 ∈ P := S2 151413703311361 cert_151413703311361 (by norm_num) (hnz (by norm_num)) (dvd_F27.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (hnz (by norm_num)) 151413703311361 g151413703311361 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 251 g251 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F28 : 1766730974551267606529 ∣ 2 ^ 2 ^ 28 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 1766730974551267606529) := by norm_num
  have s1 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 6 = ((18446744073709551616 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 7 = ((235488474550434508748 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 8 = ((1374739270328670033214 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 9 = ((676714393698831070487 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 10 = ((1185758173840878144785 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 11 = ((1100946504954263218833 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 12 = ((1662573381987388132102 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 13 = ((281510259231821551385 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 14 = ((1183367960848068018319 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 15 = ((874608075522058663484 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 16 = ((1177047758387576627190 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 17 = ((589880890681706989620 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 18 = ((37731984696827207320 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 19 = ((206757103634726006263 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 20 = ((229362170412337164473 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 21 = ((1307577250572163586105 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 22 = ((1113874690630691413232 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 23 = ((1341564028746387936573 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 24 = ((888110000628804431326 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 25 = ((1696927709645782131894 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 26 = ((472433215458415186662 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 27 = ((248561592212150858568 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  have s28 : (2 : ZMod 1766730974551267606529) ^ 2 ^ 28 = ((1766730974551267606528 : ℕ) : ZMod 1766730974551267606529) := by
    rw [pow_succ, pow_mul, s27]
    exact zmod_sq_step (by norm_num)
  exact s28

theorem k_fermat_28 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 28 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1766730974551267606529 : 1766730974551267606529 ∈ P := S2 1766730974551267606529 cert_1766730974551267606529 (by norm_num) (hnz (by norm_num)) (dvd_F28.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 1766730974551267606529 g1766730974551267606529 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 139 g139 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F29 : 2405286912458753 ∣ 2 ^ 2 ^ 29 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 2405286912458753) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 2405286912458753) := by norm_num
  have s1 : (2 : ZMod 2405286912458753) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 2405286912458753) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 2405286912458753) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 2405286912458753) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 2405286912458753) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 2405286912458753) ^ 2 ^ 6 = ((598742063374859 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 2405286912458753) ^ 2 ^ 7 = ((685060816189921 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 2405286912458753) ^ 2 ^ 8 = ((1300723141242725 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 2405286912458753) ^ 2 ^ 9 = ((2258530900802546 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 2405286912458753) ^ 2 ^ 10 = ((188400430950140 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 2405286912458753) ^ 2 ^ 11 = ((2075684318891675 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 2405286912458753) ^ 2 ^ 12 = ((1499892362461620 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 2405286912458753) ^ 2 ^ 13 = ((2175726520639885 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 2405286912458753) ^ 2 ^ 14 = ((1582980630453328 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 2405286912458753) ^ 2 ^ 15 = ((84375104460262 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 2405286912458753) ^ 2 ^ 16 = ((981373545794824 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 2405286912458753) ^ 2 ^ 17 = ((2393334767811633 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 2405286912458753) ^ 2 ^ 18 = ((2302401437179848 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 2405286912458753) ^ 2 ^ 19 = ((464074330474221 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 2405286912458753) ^ 2 ^ 20 = ((285316221365646 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 2405286912458753) ^ 2 ^ 21 = ((88649000235170 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 2405286912458753) ^ 2 ^ 22 = ((1031741222872105 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 2405286912458753) ^ 2 ^ 23 = ((229115630733520 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 2405286912458753) ^ 2 ^ 24 = ((1969394261721164 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 2405286912458753) ^ 2 ^ 25 = ((1760780432057030 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 2405286912458753) ^ 2 ^ 26 = ((1844404978305268 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 2405286912458753) ^ 2 ^ 27 = ((1936351871167657 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  have s28 : (2 : ZMod 2405286912458753) ^ 2 ^ 28 = ((694786139534 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s27]
    exact zmod_sq_step (by norm_num)
  have s29 : (2 : ZMod 2405286912458753) ^ 2 ^ 29 = ((2405286912458752 : ℕ) : ZMod 2405286912458753) := by
    rw [pow_succ, pow_mul, s28]
    exact zmod_sq_step (by norm_num)
  exact s29

theorem k_fermat_29 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 29 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2405286912458753 : 2405286912458753 ∈ P := S2 2405286912458753 cert_2405286912458753 (by norm_num) (hnz (by norm_num)) (dvd_F29.trans hd)
  have g133627050692153 : 133627050692153 ∈ P := S1 133627050692153 cert_133627050692153 (by norm_num) (hnz (by norm_num)) 2405286912458753 g2405286912458753 (by norm_num)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 133627050692153 g133627050692153 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

theorem dvd_F30 : 640126220763137 ∣ 2 ^ 2 ^ 30 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 640126220763137) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 640126220763137) := by norm_num
  have s1 : (2 : ZMod 640126220763137) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 640126220763137) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 640126220763137) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 640126220763137) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 640126220763137) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 640126220763137) ^ 2 ^ 6 = ((226769978232687 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 640126220763137) ^ 2 ^ 7 = ((81036211873763 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 640126220763137) ^ 2 ^ 8 = ((169979496713323 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 640126220763137) ^ 2 ^ 9 = ((346170631736720 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 640126220763137) ^ 2 ^ 10 = ((144540403559493 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 640126220763137) ^ 2 ^ 11 = ((599185373434582 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 640126220763137) ^ 2 ^ 12 = ((178979209368625 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 640126220763137) ^ 2 ^ 13 = ((174681647978798 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 640126220763137) ^ 2 ^ 14 = ((376409106889929 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 640126220763137) ^ 2 ^ 15 = ((364799944309461 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 640126220763137) ^ 2 ^ 16 = ((218737108940965 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 640126220763137) ^ 2 ^ 17 = ((190302311869829 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 640126220763137) ^ 2 ^ 18 = ((215254742685763 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 640126220763137) ^ 2 ^ 19 = ((115817389478521 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 640126220763137) ^ 2 ^ 20 = ((246023045584102 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 640126220763137) ^ 2 ^ 21 = ((487564806880225 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 640126220763137) ^ 2 ^ 22 = ((562231820886579 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 640126220763137) ^ 2 ^ 23 = ((172277060737096 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 640126220763137) ^ 2 ^ 24 = ((135440858711535 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 640126220763137) ^ 2 ^ 25 = ((513826845141497 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 640126220763137) ^ 2 ^ 26 = ((482259770670948 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 640126220763137) ^ 2 ^ 27 = ((140902846195950 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  have s28 : (2 : ZMod 640126220763137) ^ 2 ^ 28 = ((342813829196393 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s27]
    exact zmod_sq_step (by norm_num)
  have s29 : (2 : ZMod 640126220763137) ^ 2 ^ 29 = ((399460410565227 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s28]
    exact zmod_sq_step (by norm_num)
  have s30 : (2 : ZMod 640126220763137) ^ 2 ^ 30 = ((640126220763136 : ℕ) : ZMod 640126220763137) := by
    rw [pow_succ, pow_mul, s29]
    exact zmod_sq_step (by norm_num)
  exact s30

theorem k_fermat_30 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 30 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g640126220763137 : 640126220763137 ∈ P := S2 640126220763137 cert_640126220763137 (by norm_num) (hnz (by norm_num)) (dvd_F30.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g3972019 : 3972019 ∈ P := S1 3972019 (by norm_num) (by norm_num) (hnz (by norm_num)) 640126220763137 g640126220763137 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 3972019 g3972019 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F31 : 46931635677864055013377 ∣ 2 ^ 2 ^ 31 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 46931635677864055013377) := by norm_num
  have s1 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 6 = ((18446744073709551616 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 7 = ((38363021979501503732146 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 8 = ((30560352921216510868749 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 9 = ((43986250657625358671264 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 10 = ((3836856324017187631627 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 11 = ((29927870920830085165491 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 12 = ((1645254058175554898997 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 13 = ((20861441227712941901034 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 14 = ((46637882059404545989129 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 15 = ((4923156192062248979376 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 16 = ((8539384385590223011933 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 17 = ((567709204361255269387 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 18 = ((38459744987078020098276 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 19 = ((31441578002548143296673 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 20 = ((19010711966899296975721 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 21 = ((43547131931047618492289 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 22 = ((27012099093172316999667 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 23 = ((13614695271352585231974 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 24 = ((24658615689284278066333 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 25 = ((42528030790942464843713 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 26 = ((12624592063262567219927 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 27 = ((19471768060058524545966 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  have s28 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 28 = ((30270822658639989819115 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s27]
    exact zmod_sq_step (by norm_num)
  have s29 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 29 = ((14997555417822130938895 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s28]
    exact zmod_sq_step (by norm_num)
  have s30 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 30 = ((19159544924293175031873 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s29]
    exact zmod_sq_step (by norm_num)
  have s31 : (2 : ZMod 46931635677864055013377) ^ 2 ^ 31 = ((46931635677864055013376 : ℕ) : ZMod 46931635677864055013377) := by
    rw [pow_succ, pow_mul, s30]
    exact zmod_sq_step (by norm_num)
  exact s31

theorem k_fermat_31 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 31 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g46931635677864055013377 : 46931635677864055013377 ∈ P := S2 46931635677864055013377 cert_46931635677864055013377 (by norm_num) (hnz (by norm_num)) (dvd_F31.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 46931635677864055013377 g46931635677864055013377 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem dvd_F32 : 25409026523137 ∣ 2 ^ 2 ^ 32 + 1 := by
  apply dvd_two_pow_two_pow_add_one (by norm_num)
  have s0 : (2 : ZMod 25409026523137) ^ 2 ^ 0 = ((2 : ℕ) : ZMod 25409026523137) := by norm_num
  have s1 : (2 : ZMod 25409026523137) ^ 2 ^ 1 = ((4 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s0]
    exact zmod_sq_step (by norm_num)
  have s2 : (2 : ZMod 25409026523137) ^ 2 ^ 2 = ((16 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s1]
    exact zmod_sq_step (by norm_num)
  have s3 : (2 : ZMod 25409026523137) ^ 2 ^ 3 = ((256 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s2]
    exact zmod_sq_step (by norm_num)
  have s4 : (2 : ZMod 25409026523137) ^ 2 ^ 4 = ((65536 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s3]
    exact zmod_sq_step (by norm_num)
  have s5 : (2 : ZMod 25409026523137) ^ 2 ^ 5 = ((4294967296 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s4]
    exact zmod_sq_step (by norm_num)
  have s6 : (2 : ZMod 25409026523137) ^ 2 ^ 6 = ((19499150797849 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s5]
    exact zmod_sq_step (by norm_num)
  have s7 : (2 : ZMod 25409026523137) ^ 2 ^ 7 = ((19905770632008 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s6]
    exact zmod_sq_step (by norm_num)
  have s8 : (2 : ZMod 25409026523137) ^ 2 ^ 8 = ((22190326300255 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s7]
    exact zmod_sq_step (by norm_num)
  have s9 : (2 : ZMod 25409026523137) ^ 2 ^ 9 = ((135719443020 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s8]
    exact zmod_sq_step (by norm_num)
  have s10 : (2 : ZMod 25409026523137) ^ 2 ^ 10 = ((15472650352769 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s9]
    exact zmod_sq_step (by norm_num)
  have s11 : (2 : ZMod 25409026523137) ^ 2 ^ 11 = ((10444808750099 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s10]
    exact zmod_sq_step (by norm_num)
  have s12 : (2 : ZMod 25409026523137) ^ 2 ^ 12 = ((17998614488214 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s11]
    exact zmod_sq_step (by norm_num)
  have s13 : (2 : ZMod 25409026523137) ^ 2 ^ 13 = ((4479413496373 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s12]
    exact zmod_sq_step (by norm_num)
  have s14 : (2 : ZMod 25409026523137) ^ 2 ^ 14 = ((6072749567913 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s13]
    exact zmod_sq_step (by norm_num)
  have s15 : (2 : ZMod 25409026523137) ^ 2 ^ 15 = ((17332703494837 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s14]
    exact zmod_sq_step (by norm_num)
  have s16 : (2 : ZMod 25409026523137) ^ 2 ^ 16 = ((19179254918376 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s15]
    exact zmod_sq_step (by norm_num)
  have s17 : (2 : ZMod 25409026523137) ^ 2 ^ 17 = ((17722364353783 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s16]
    exact zmod_sq_step (by norm_num)
  have s18 : (2 : ZMod 25409026523137) ^ 2 ^ 18 = ((3240112118583 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s17]
    exact zmod_sq_step (by norm_num)
  have s19 : (2 : ZMod 25409026523137) ^ 2 ^ 19 = ((13037739232311 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s18]
    exact zmod_sq_step (by norm_num)
  have s20 : (2 : ZMod 25409026523137) ^ 2 ^ 20 = ((8009711139841 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s19]
    exact zmod_sq_step (by norm_num)
  have s21 : (2 : ZMod 25409026523137) ^ 2 ^ 21 = ((7750700496522 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s20]
    exact zmod_sq_step (by norm_num)
  have s22 : (2 : ZMod 25409026523137) ^ 2 ^ 22 = ((21355834185828 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s21]
    exact zmod_sq_step (by norm_num)
  have s23 : (2 : ZMod 25409026523137) ^ 2 ^ 23 = ((13916109625335 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s22]
    exact zmod_sq_step (by norm_num)
  have s24 : (2 : ZMod 25409026523137) ^ 2 ^ 24 = ((7285406066849 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s23]
    exact zmod_sq_step (by norm_num)
  have s25 : (2 : ZMod 25409026523137) ^ 2 ^ 25 = ((17109046983628 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s24]
    exact zmod_sq_step (by norm_num)
  have s26 : (2 : ZMod 25409026523137) ^ 2 ^ 26 = ((14432356652311 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s25]
    exact zmod_sq_step (by norm_num)
  have s27 : (2 : ZMod 25409026523137) ^ 2 ^ 27 = ((5001977167638 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s26]
    exact zmod_sq_step (by norm_num)
  have s28 : (2 : ZMod 25409026523137) ^ 2 ^ 28 = ((14902842700865 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s27]
    exact zmod_sq_step (by norm_num)
  have s29 : (2 : ZMod 25409026523137) ^ 2 ^ 29 = ((25168296042536 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s28]
    exact zmod_sq_step (by norm_num)
  have s30 : (2 : ZMod 25409026523137) ^ 2 ^ 30 = ((11363426243319 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s29]
    exact zmod_sq_step (by norm_num)
  have s31 : (2 : ZMod 25409026523137) ^ 2 ^ 31 = ((9872447659838 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s30]
    exact zmod_sq_step (by norm_num)
  have s32 : (2 : ZMod 25409026523137) ^ 2 ^ 32 = ((25409026523136 : ℕ) : ZMod 25409026523137) := by
    rw [pow_succ, pow_mul, s31]
    exact zmod_sq_step (by norm_num)
  exact s32

theorem k_fermat_32 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (hd : 2 ^ 2 ^ 32 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 11 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g25409026523137 : 25409026523137 ∈ P := S2 25409026523137 cert_25409026523137 (by norm_num) (hnz (by norm_num)) (dvd_F32.trans hd)
  have g661 : 661 ∈ P := S7 661 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g331 : 331 ∈ P := S1 331 (by norm_num) (by norm_num) (hnz (by norm_num)) 661 g661 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (hnz (by norm_num)) 331 g331 (by norm_num)
  have g12704513261569 : 12704513261569 ∈ P := S1 12704513261569 cert_12704513261569 (by norm_num) (hnz (by norm_num)) 25409026523137 g25409026523137 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 12704513261569 g12704513261569 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)

theorem high_tail {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 11) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 11 * ∏ p ∈ P, p)
    (h20 : m % 2 ^ 20 = 0) :
    m % 2 ^ 21 = 2 ^ 20 ∨ m % 2 ^ 25 = 2 ^ 24 ∨ 2 ^ 33 ∣ m := by
  by_cases c20 : m % 2 ^ 21 = 2 ^ 20
  · exact Or.inl c20
  have h21 : m % 2 ^ 21 = 0 := by
    simpa [show 2 * 2 ^ 20 = 2 ^ 21 from by norm_num] using dbl (k := 2 ^ 20) (by norm_num) h20 c20
  have h22 : m % 2 ^ 22 = 0 := by
    have ne21 : m % (2 * 2 ^ 21) ≠ 2 ^ 21 := fun hm =>
      k_fermat_21 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 21 = 2 ^ 22 from by norm_num] using dbl (k := 2 ^ 21) (by norm_num) h21 ne21
  have h23 : m % 2 ^ 23 = 0 := by
    have ne22 : m % (2 * 2 ^ 22) ≠ 2 ^ 22 := fun hm =>
      k_fermat_22 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 22 = 2 ^ 23 from by norm_num] using dbl (k := 2 ^ 22) (by norm_num) h22 ne22
  have h24 : m % 2 ^ 24 = 0 := by
    have ne23 : m % (2 * 2 ^ 23) ≠ 2 ^ 23 := fun hm =>
      k_fermat_23 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 23 = 2 ^ 24 from by norm_num] using dbl (k := 2 ^ 23) (by norm_num) h23 ne23
  by_cases c24 : m % 2 ^ 25 = 2 ^ 24
  · exact Or.inr (Or.inl c24)
  have h25 : m % 2 ^ 25 = 0 := by
    simpa [show 2 * 2 ^ 24 = 2 ^ 25 from by norm_num] using dbl (k := 2 ^ 24) (by norm_num) h24 c24
  have h26 : m % 2 ^ 26 = 0 := by
    have ne25 : m % (2 * 2 ^ 25) ≠ 2 ^ 25 := fun hm =>
      k_fermat_25 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 25 = 2 ^ 26 from by norm_num] using dbl (k := 2 ^ 25) (by norm_num) h25 ne25
  have h27 : m % 2 ^ 27 = 0 := by
    have ne26 : m % (2 * 2 ^ 26) ≠ 2 ^ 26 := fun hm =>
      k_fermat_26 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 26 = 2 ^ 27 from by norm_num] using dbl (k := 2 ^ 26) (by norm_num) h26 ne26
  have h28 : m % 2 ^ 28 = 0 := by
    have ne27 : m % (2 * 2 ^ 27) ≠ 2 ^ 27 := fun hm =>
      k_fermat_27 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 27 = 2 ^ 28 from by norm_num] using dbl (k := 2 ^ 27) (by norm_num) h27 ne27
  have h29 : m % 2 ^ 29 = 0 := by
    have ne28 : m % (2 * 2 ^ 28) ≠ 2 ^ 28 := fun hm =>
      k_fermat_28 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 28 = 2 ^ 29 from by norm_num] using dbl (k := 2 ^ 28) (by norm_num) h28 ne28
  have h30 : m % 2 ^ 30 = 0 := by
    have ne29 : m % (2 * 2 ^ 29) ≠ 2 ^ 29 := fun hm =>
      k_fermat_29 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 29 = 2 ^ 30 from by norm_num] using dbl (k := 2 ^ 29) (by norm_num) h29 ne29
  have h31 : m % 2 ^ 31 = 0 := by
    have ne30 : m % (2 * 2 ^ 30) ≠ 2 ^ 30 := fun hm =>
      k_fermat_30 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 30 = 2 ^ 31 from by norm_num] using dbl (k := 2 ^ 30) (by norm_num) h30 ne30
  have h32 : m % 2 ^ 32 = 0 := by
    have ne31 : m % (2 * 2 ^ 31) ≠ 2 ^ 31 := fun hm =>
      k_fermat_31 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 31 = 2 ^ 32 from by norm_num] using dbl (k := 2 ^ 31) (by norm_num) h31 ne31
  have h33 : m % 2 ^ 33 = 0 := by
    have ne32 : m % (2 * 2 ^ 32) ≠ 2 ^ 32 := fun hm =>
      k_fermat_32 hP E (two_pow_add_one_dvd_of_odd_mul hm)
    simpa [show 2 * 2 ^ 32 = 2 ^ 33 from by norm_num] using dbl (k := 2 ^ 32) (by norm_num) h32 ne32
  exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero h33))

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), fun n h hiff he hmod20 => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  rw [he, ha] at E
  have h20' : padicValNat 2 n % 2 ^ 20 = 0 := by simpa using hmod20
  rcases high_tail hP E h20' with c | c | c
  · exact (h1 n h hiff he c).trans (le_max_left _ _)
  · exact (h2 n h hiff he c).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 n h hiff he c).trans ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H4_R1
