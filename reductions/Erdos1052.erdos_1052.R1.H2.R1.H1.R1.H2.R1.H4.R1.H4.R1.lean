import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1

/-!
# Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H4.R1

Eliminates the `e % 16 = 8` class completely for all 314 primes `z ∈ [7, 2100)` (0 survivors,
proving `16 ∣ n.factorization z` unconditionally), and sieves `e % 32 = 16` (229/314 eliminated,
leaving 85 primes) and `e % 64 = 32` (221/314 eliminated including `z = 7`, leaving 93 primes)
via forced-chain contradictions and Lucas primality certificates.

Splits step `H4` (`8 ∣ e`) cleanly into:
- `H1`: `e % 32 = 16` with `z` in the surviving 85-prime list.
- `H2`: `e % 64 = 32` with `z` in the surviving 93-prime list.
- `H3`: `64 ∣ e` (`n.factorization z % 64 = 0`).
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1 hiding H1 H2 H3 H4 main

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 32 = 16 →
    z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 64 = 32 →
    z ∈ ({41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ∀ z : ℕ, z.Prime → 7 ≤ z → z < 2100 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    n.factorization z % 64 = 0 →
    (z = 7 → 41 ≤ n.factorization 7 ∧
      ∀ d ∈ ({2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 32, 37} : Finset ℕ),
        n.factorization 7 % (2 * d) ≠ d) →
    padicValNat 2 n % 6 ≠ 3 → (z ≠ 11 → padicValNat 2 n % 10 ≠ 5) →
    (z ≠ 11 → z ≠ 43 → padicValNat 2 n % 14 ≠ 7) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    (z ≠ 17 → padicValNat 2 n % 8 ≠ 4) → (z ≠ 11 → z ≠ 43 → z ≠ 257 → padicValNat 2 n % 16 ≠ 8) →
    (z ≠ 743 → padicValNat 2 n % 4096 ≠ 2048) →
    (Odd (padicValNat 2 n) → ∀ d, d ∣ padicValNat 2 n → d % 6 = 1 ∨ (z % 3 = 2 ∧ z ∣ 2 ^ d + 1)) →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- Section 1. Fast modular squaring divisibility and Lucas check helpers.

lemma d8 {z p : ℕ} (r1 r2 r3 : ℕ)
    (h : z * z % p = r1 ∧ r1 * r1 % p = r2 ∧ r2 * r2 % p = r3 ∧ (1 + r3) % p = 0) :
    p ∣ 1 + z ^ 8 := by
  apply Nat.dvd_of_mod_eq_zero
  have e2 : z ^ 2 % p = r1 := by simpa [pow_two] using h.1
  have e4 : z ^ 4 % p = r2 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Nat.mul_mod, e2]; exact h.2.1
  have e8 : z ^ 8 % p = r3 := by rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, Nat.mul_mod, e4]; exact h.2.2.1
  rw [Nat.add_mod, e8, Nat.mod_add_mod]; exact h.2.2.2

lemma d16 {z p : ℕ} (r1 r2 r3 r4 : ℕ)
    (h : z * z % p = r1 ∧ r1 * r1 % p = r2 ∧ r2 * r2 % p = r3 ∧ r3 * r3 % p = r4 ∧ (1 + r4) % p = 0) :
    p ∣ 1 + z ^ 16 := by
  apply Nat.dvd_of_mod_eq_zero
  have e2 : z ^ 2 % p = r1 := by simpa [pow_two] using h.1
  have e4 : z ^ 4 % p = r2 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Nat.mul_mod, e2]; exact h.2.1
  have e8 : z ^ 8 % p = r3 := by rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, Nat.mul_mod, e4]; exact h.2.2.1
  have e16 : z ^ 16 % p = r4 := by rw [show (16 : ℕ) = 8 + 8 from rfl, pow_add, Nat.mul_mod, e8]; exact h.2.2.2.1
  rw [Nat.add_mod, e16, Nat.mod_add_mod]; exact h.2.2.2.2

lemma d32 {z p : ℕ} (r1 r2 r3 r4 r5 : ℕ)
    (h : z * z % p = r1 ∧ r1 * r1 % p = r2 ∧ r2 * r2 % p = r3 ∧ r3 * r3 % p = r4 ∧ r4 * r4 % p = r5 ∧ (1 + r5) % p = 0) :
    p ∣ 1 + z ^ 32 := by
  apply Nat.dvd_of_mod_eq_zero
  have e2 : z ^ 2 % p = r1 := by simpa [pow_two] using h.1
  have e4 : z ^ 4 % p = r2 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Nat.mul_mod, e2]; exact h.2.1
  have e8 : z ^ 8 % p = r3 := by rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add, Nat.mul_mod, e4]; exact h.2.2.1
  have e16 : z ^ 16 % p = r4 := by rw [show (16 : ℕ) = 8 + 8 from rfl, pow_add, Nat.mul_mod, e8]; exact h.2.2.2.1
  have e32 : z ^ 32 % p = r5 := by rw [show (32 : ℕ) = 16 + 16 from rfl, pow_add, Nat.mul_mod, e16]; exact h.2.2.2.2.1
  rw [Nat.add_mod, e32, Nat.mod_add_mod]; exact h.2.2.2.2.2

lemma lucas_chk {p a q r k exp rem : ℕ} (hq : q.Prime) (hr : r.Prime) (hd : q ∣ r ^ k)
    (hexp : (p - 1) / r = exp) (hpow : (a : ZMod p) ^ exp = ((rem : ℕ) : ZMod p))
    (hrem : rem % p ≠ 1 % p) : (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  have h1 := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hd)
  subst h1
  rw [hexp, hpow]
  exact zmod_ne_one hrem

-- Section 2. Lucas primality certificates (68 primes > 4e7).

theorem prime_146844953 : Nat.Prime 146844953 := by
  refine lucas_primality 146844953 (3 : ZMod 146844953) ?_ (fun q hq hd => ?_)
  · rw [show 146844953 - 1 = 146844952 from by norm_num]; reduce_mod_char
  · have e : 146844953 - 1 = [2 ^ 3, 2207 ^ 1, 8317 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 73422476) (rem := 146844952) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 66536) (rem := 51826127) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 17656) (rem := 44145537) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_169318049 : Nat.Prime 169318049 := by
  refine lucas_primality 169318049 (3 : ZMod 169318049) ?_ (fun q hq hd => ?_)
  · rw [show 169318049 - 1 = 169318048 from by norm_num]; reduce_mod_char
  · have e : 169318049 - 1 = [2 ^ 5, 349 ^ 1, 15161 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 84659024) (rem := 169318048) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 485152) (rem := 64783065) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11168) (rem := 25133279) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_230251457 : Nat.Prime 230251457 := by
  refine lucas_primality 230251457 (3 : ZMod 230251457) ?_ (fun q hq hd => ?_)
  · rw [show 230251457 - 1 = 230251456 from by norm_num]; reduce_mod_char
  · have e : 230251457 - 1 = [2 ^ 6, 1789 ^ 1, 2011 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 115125728) (rem := 230251456) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 128704) (rem := 108748013) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 114496) (rem := 101120855) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_258426017 : Nat.Prime 258426017 := by
  refine lucas_primality 258426017 (3 : ZMod 258426017) ?_ (fun q hq hd => ?_)
  · rw [show 258426017 - 1 = 258426016 from by norm_num]; reduce_mod_char
  · have e : 258426017 - 1 = [2 ^ 5, 173 ^ 1, 46681 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 129213008) (rem := 258426016) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1493792) (rem := 68396593) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5536) (rem := 57699234) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_297457729 : Nat.Prime 297457729 := by
  refine lucas_primality 297457729 (23 : ZMod 297457729) ?_ (fun q hq hd => ?_)
  · rw [show 297457729 - 1 = 297457728 from by norm_num]; reduce_mod_char
  · have e : 297457729 - 1 = [2 ^ 6, 3 ^ 1, 167 ^ 1, 9277 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 148728864) (rem := 297457728) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 99152576) (rem := 101685871) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1781184) (rem := 2905440) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 32064) (rem := 130456233) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_304237489 : Nat.Prime 304237489 := by
  refine lucas_primality 304237489 (7 : ZMod 304237489) ?_ (fun q hq hd => ?_)
  · rw [show 304237489 - 1 = 304237488 from by norm_num]; reduce_mod_char
  · have e : 304237489 - 1 = [2 ^ 4, 3 ^ 1, 6338281 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 152118744) (rem := 304237488) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 101412496) (rem := 243640312) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 48) (rem := 22462450) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_305690377 : Nat.Prime 305690377 := by
  refine lucas_primality 305690377 (5 : ZMod 305690377) ?_ (fun q hq hd => ?_)
  · rw [show 305690377 - 1 = 305690376 from by norm_num]; reduce_mod_char
  · have e : 305690377 - 1 = [2 ^ 3, 3 ^ 1, 12737099 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 152845188) (rem := 305690376) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 101896792) (rem := 138691871) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 24) (rem := 39560824) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_365656673 : Nat.Prime 365656673 := by
  refine lucas_primality 365656673 (3 : ZMod 365656673) ?_ (fun q hq hd => ?_)
  · rw [show 365656673 - 1 = 365656672 from by norm_num]; reduce_mod_char
  · have e : 365656673 - 1 = [2 ^ 5, 17 ^ 2, 19 ^ 1, 2081 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 182828336) (rem := 365656672) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 21509216) (rem := 198022946) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 19245088) (rem := 235118405) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 175712) (rem := 65037274) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_407865361 : Nat.Prime 407865361 := by
  refine lucas_primality 407865361 (11 : ZMod 407865361) ?_ (fun q hq hd => ?_)
  · rw [show 407865361 - 1 = 407865360 from by norm_num]; reduce_mod_char
  · have e : 407865361 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 14281 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 203932680) (rem := 407865360) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 135955120) (rem := 388788868) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 81573072) (rem := 300398511) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 58266480) (rem := 330426176) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 23992080) (rem := 49842018) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 28560) (rem := 2963373) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_439404181 : Nat.Prime 439404181 := by
  refine lucas_primality 439404181 (2 : ZMod 439404181) ?_ (fun q hq hd => ?_)
  · rw [show 439404181 - 1 = 439404180 from by norm_num]; reduce_mod_char
  · have e : 439404181 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 1, 97 ^ 1, 103 ^ 1, 733 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 219702090) (rem := 439404180) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 146468060) (rem := 59348334) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 87880836) (rem := 36035160) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4529940) (rem := 285746281) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4266060) (rem := 437186096) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 599460) (rem := 439185151) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_507572189 : Nat.Prime 507572189 := by
  refine lucas_primality 507572189 (2 : ZMod 507572189) ?_ (fun q hq hd => ?_)
  · rw [show 507572189 - 1 = 507572188 from by norm_num]; reduce_mod_char
  · have e : 507572189 - 1 = [2 ^ 2, 23 ^ 1, 5517089 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 253786094) (rem := 507572188) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 22068356) (rem := 428164134) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 92) (rem := 420894122) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_611380753 : Nat.Prime 611380753 := by
  refine lucas_primality 611380753 (5 : ZMod 611380753) ?_ (fun q hq hd => ?_)
  · rw [show 611380753 - 1 = 611380752 from by norm_num]; reduce_mod_char
  · have e : 611380753 - 1 = [2 ^ 4, 3 ^ 1, 12737099 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 305690376) (rem := 611380752) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 203793584) (rem := 82937474) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 48) (rem := 266728211) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_751962317 : Nat.Prime 751962317 := by
  refine lucas_primality 751962317 (2 : ZMod 751962317) ?_ (fun q hq hd => ?_)
  · rw [show 751962317 - 1 = 751962316 from by norm_num]; reduce_mod_char
  · have e : 751962317 - 1 = [2 ^ 2, 7 ^ 1, 19 ^ 1, 59 ^ 1, 23957 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 375981158) (rem := 751962316) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 107423188) (rem := 689790133) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 39576964) (rem := 167651559) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 12745124) (rem := 413112311) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 31388) (rem := 43708848) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_822740921 : Nat.Prime 822740921 := by
  refine lucas_primality 822740921 (3 : ZMod 822740921) ?_ (fun q hq hd => ?_)
  · rw [show 822740921 - 1 = 822740920 from by norm_num]; reduce_mod_char
  · have e : 822740921 - 1 = [2 ^ 3, 5 ^ 1, 89 ^ 1, 231107 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 411370460) (rem := 822740920) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 164548184) (rem := 549461922) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9244280) (rem := 561153394) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3560) (rem := 522657209) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_874058123 : Nat.Prime 874058123 := by
  refine lucas_primality 874058123 (2 : ZMod 874058123) ?_ (fun q hq hd => ?_)
  · rw [show 874058123 - 1 = 874058122 from by norm_num]; reduce_mod_char
  · have e : 874058123 - 1 = [2 ^ 1, 7 ^ 1, 7177 ^ 1, 8699 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 437029061) (rem := 874058122) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 124865446) (rem := 260406463) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 121786) (rem := 842845462) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 100478) (rem := 751339757) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_887369321 : Nat.Prime 887369321 := by
  refine lucas_primality 887369321 (3 : ZMod 887369321) ?_ (fun q hq hd => ?_)
  · rw [show 887369321 - 1 = 887369320 from by norm_num]; reduce_mod_char
  · have e : 887369321 - 1 = [2 ^ 3, 5 ^ 1, 127 ^ 1, 174679 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 443684660) (rem := 887369320) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 177473864) (rem := 766235785) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6987160) (rem := 834208373) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5080) (rem := 599871620) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_986950541 : Nat.Prime 986950541 := by
  refine lucas_primality 986950541 (2 : ZMod 986950541) ?_ (fun q hq hd => ?_)
  · rw [show 986950541 - 1 = 986950540 from by norm_num]; reduce_mod_char
  · have e : 986950541 - 1 = [2 ^ 2, 5 ^ 1, 373 ^ 1, 132299 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 493475270) (rem := 986950540) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 197390108) (rem := 501047659) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2645980) (rem := 580355903) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 7460) (rem := 562437114) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1351728281 : Nat.Prime 1351728281 := by
  refine lucas_primality 1351728281 (3 : ZMod 1351728281) ?_ (fun q hq hd => ?_)
  · rw [show 1351728281 - 1 = 1351728280 from by norm_num]; reduce_mod_char
  · have e : 1351728281 - 1 = [2 ^ 3, 5 ^ 1, 7 ^ 1, 29 ^ 1, 61 ^ 1, 2729 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 675864140) (rem := 1351728280) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 270345656) (rem := 597493821) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 193104040) (rem := 1312225023) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 46611320) (rem := 334438398) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 22159480) (rem := 31785685) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 495320) (rem := 900488063) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1638724289 : Nat.Prime 1638724289 := by
  refine lucas_primality 1638724289 (3 : ZMod 1638724289) ?_ (fun q hq hd => ?_)
  · rw [show 1638724289 - 1 = 1638724288 from by norm_num]; reduce_mod_char
  · have e : 1638724289 - 1 = [2 ^ 6, 25605067 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 819362144) (rem := 1638724288) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 64) (rem := 1210056614) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1709413193 : Nat.Prime 1709413193 := by
  refine lucas_primality 1709413193 (3 : ZMod 1709413193) ?_ (fun q hq hd => ?_)
  · rw [show 1709413193 - 1 = 1709413192 from by norm_num]; reduce_mod_char
  · have e : 1709413193 - 1 = [2 ^ 3, 313 ^ 1, 682673 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 854706596) (rem := 1709413192) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5461384) (rem := 723984064) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2504) (rem := 99644709) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1726276009 : Nat.Prime 1726276009 := by
  refine lucas_primality 1726276009 (7 : ZMod 1726276009) ?_ (fun q hq hd => ?_)
  · rw [show 1726276009 - 1 = 1726276008 from by norm_num]; reduce_mod_char
  · have e : 1726276009 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 2, 199247 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 863138004) (rem := 1726276008) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 575425336) (rem := 48085376) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 90856632) (rem := 654560651) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8664) (rem := 1307265353) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1861745233 : Nat.Prime 1861745233 := by
  refine lucas_primality 1861745233 (5 : ZMod 1861745233) ?_ (fun q hq hd => ?_)
  · rw [show 1861745233 - 1 = 1861745232 from by norm_num]; reduce_mod_char
  · have e : 1861745233 - 1 = [2 ^ 4, 3 ^ 1, 2777 ^ 1, 13967 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 930872616) (rem := 1861745232) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 620581744) (rem := 1514443192) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 670416) (rem := 21300364) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 133296) (rem := 762088630) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_3452552017 : Nat.Prime 3452552017 := by
  refine lucas_primality 3452552017 (7 : ZMod 3452552017) ?_ (fun q hq hd => ?_)
  · rw [show 3452552017 - 1 = 3452552016 from by norm_num]; reduce_mod_char
  · have e : 3452552017 - 1 = [2 ^ 4, 3 ^ 1, 19 ^ 2, 199247 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 1726276008) (rem := 3452552016) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1150850672) (rem := 251894622) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 181713264) (rem := 3085815328) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 17328) (rem := 3260235922) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_5830437863 : Nat.Prime 5830437863 := by
  refine lucas_primality 5830437863 (5 : ZMod 5830437863) ?_ (fun q hq hd => ?_)
  · rw [show 5830437863 - 1 = 5830437862 from by norm_num]; reduce_mod_char
  · have e : 5830437863 - 1 = [2 ^ 1, 2069 ^ 1, 1408999 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2915218931) (rem := 5830437862) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2817998) (rem := 5491588469) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4138) (rem := 5381037278) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_7152978793 : Nat.Prime 7152978793 := by
  refine lucas_primality 7152978793 (5 : ZMod 7152978793) ?_ (fun q hq hd => ?_)
  · rw [show 7152978793 - 1 = 7152978792 from by norm_num]; reduce_mod_char
  · have e : 7152978793 - 1 = [2 ^ 3, 3 ^ 1, 19 ^ 1, 43 ^ 1, 53 ^ 1, 6883 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 3576489396) (rem := 7152978792) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2384326264) (rem := 5969035372) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 376472568) (rem := 5284203782) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 166348344) (rem := 1619771549) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 134961864) (rem := 794149277) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1039224) (rem := 3546611745) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_7592718929 : Nat.Prime 7592718929 := by
  refine lucas_primality 7592718929 (3 : ZMod 7592718929) ?_ (fun q hq hd => ?_)
  · rw [show 7592718929 - 1 = 7592718928 from by norm_num]; reduce_mod_char
  · have e : 7592718929 - 1 = [2 ^ 4, 733 ^ 1, 647401 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 3796359464) (rem := 7592718928) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 10358416) (rem := 1921316407) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11728) (rem := 2968358613) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_16013775593 : Nat.Prime 16013775593 := by
  refine lucas_primality 16013775593 (3 : ZMod 16013775593) ?_ (fun q hq hd => ?_)
  · rw [show 16013775593 - 1 = 16013775592 from by norm_num]; reduce_mod_char
  · have e : 16013775593 - 1 = [2 ^ 3, 67 ^ 1, 2837 ^ 1, 10531 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 8006887796) (rem := 16013775592) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 239011576) (rem := 402845746) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5644616) (rem := 4270240951) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1520632) (rem := 9359039550) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_18295290017 : Nat.Prime 18295290017 := by
  refine lucas_primality 18295290017 (3 : ZMod 18295290017) ?_ (fun q hq hd => ?_)
  · rw [show 18295290017 - 1 = 18295290016 from by norm_num]; reduce_mod_char
  · have e : 18295290017 - 1 = [2 ^ 5, 23 ^ 1, 3571 ^ 1, 6961 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 9147645008) (rem := 18295290016) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 795447392) (rem := 13317023670) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5123296) (rem := 12555714256) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2628256) (rem := 8817363546) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_31582417313 : Nat.Prime 31582417313 := by
  refine lucas_primality 31582417313 (3 : ZMod 31582417313) ?_ (fun q hq hd => ?_)
  · rw [show 31582417313 - 1 = 31582417312 from by norm_num]; reduce_mod_char
  · have e : 31582417313 - 1 = [2 ^ 5, 986950541 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 15791208656) (rem := 31582417312) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_986950541 hqx (exp := 32) (rem := 16600263505) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_39064015937 : Nat.Prime 39064015937 := by
  refine lucas_primality 39064015937 (3 : ZMod 39064015937) ?_ (fun q hq hd => ?_)
  · rw [show 39064015937 - 1 = 39064015936 from by norm_num]; reduce_mod_char
  · have e : 39064015937 - 1 = [2 ^ 6, 11 ^ 1, 283 ^ 1, 196073 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 19532007968) (rem := 39064015936) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3551274176) (rem := 17769310426) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 138035392) (rem := 7533516646) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 199232) (rem := 30233161185) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_44695037407 : Nat.Prime 44695037407 := by
  refine lucas_primality 44695037407 (3 : ZMod 44695037407) ?_ (fun q hq hd => ?_)
  · rw [show 44695037407 - 1 = 44695037406 from by norm_num]; reduce_mod_char
  · have e : 44695037407 - 1 = [2 ^ 1, 3 ^ 1, 103 ^ 1, 149 ^ 1, 485383 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 22347518703) (rem := 44695037406) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 14898345802) (rem := 15635013126) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 433932402) (rem := 43111269437) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 299966694) (rem := 35163323908) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 92082) (rem := 9108250834) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_85826901353 : Nat.Prime 85826901353 := by
  refine lucas_primality 85826901353 (3 : ZMod 85826901353) ?_ (fun q hq hd => ?_)
  · rw [show 85826901353 - 1 = 85826901352 from by norm_num]; reduce_mod_char
  · have e : 85826901353 - 1 = [2 ^ 3, 17 ^ 1, 97 ^ 1, 701 ^ 1, 9281 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 42913450676) (rem := 85826901352) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5048641256) (rem := 57638121014) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 884813416) (rem := 77843863355) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 122434952) (rem := 58244412718) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9247592) (rem := 3375662451) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_97154822801 : Nat.Prime 97154822801 := by
  refine lucas_primality 97154822801 (3 : ZMod 97154822801) ?_ (fun q hq hd => ?_)
  · rw [show 97154822801 - 1 = 97154822800 from by norm_num]; reduce_mod_char
  · have e : 97154822801 - 1 = [2 ^ 4, 5 ^ 2, 7 ^ 1, 34698151 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 48577411400) (rem := 97154822800) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 19430964560) (rem := 69487052630) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 13879260400) (rem := 45377070766) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2800) (rem := 84628094167) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_138059635409 : Nat.Prime 138059635409 := by
  refine lucas_primality 138059635409 (3 : ZMod 138059635409) ?_ (fun q hq hd => ?_)
  · rw [show 138059635409 - 1 = 138059635408 from by norm_num]; reduce_mod_char
  · have e : 138059635409 - 1 = [2 ^ 4, 17 ^ 1, 507572189 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 69029817704) (rem := 138059635408) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8121155024) (rem := 98843118033) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_507572189 hqx (exp := 272) (rem := 75411064683) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_216641645201 : Nat.Prime 216641645201 := by
  refine lucas_primality 216641645201 (3 : ZMod 216641645201) ?_ (fun q hq hd => ?_)
  · rw [show 216641645201 - 1 = 216641645200 from by norm_num]; reduce_mod_char
  · have e : 216641645201 - 1 = [2 ^ 4, 5 ^ 2, 37 ^ 1, 257 ^ 1, 56957 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 108320822600) (rem := 216641645200) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 43328329040) (rem := 156053380030) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5855179600) (rem := 104835881494) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 842963600) (rem := 46980180584) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3803600) (rem := 189599908281) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_231682423177 : Nat.Prime 231682423177 := by
  refine lucas_primality 231682423177 (5 : ZMod 231682423177) ?_ (fun q hq hd => ?_)
  · rw [show 231682423177 - 1 = 231682423176 from by norm_num]; reduce_mod_char
  · have e : 231682423177 - 1 = [2 ^ 3, 3 ^ 3, 8839 ^ 1, 121349 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 115841211588) (rem := 231682423176) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 77227474392) (rem := 45296366704) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 26211384) (rem := 187270582786) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1909224) (rem := 142020310516) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_463364846353 : Nat.Prime 463364846353 := by
  refine lucas_primality 463364846353 (5 : ZMod 463364846353) ?_ (fun q hq hd => ?_)
  · rw [show 463364846353 - 1 = 463364846352 from by norm_num]; reduce_mod_char
  · have e : 463364846353 - 1 = [2 ^ 4, 3 ^ 3, 8839 ^ 1, 121349 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 231682423176) (rem := 463364846352) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 154454948784) (rem := 257062359618) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 52422768) (rem := 172996845925) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3818448) (rem := 35401320918) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_686002709617 : Nat.Prime 686002709617 := by
  refine lucas_primality 686002709617 (5 : ZMod 686002709617) ?_ (fun q hq hd => ?_)
  · rw [show 686002709617 - 1 = 686002709616 from by norm_num]; reduce_mod_char
  · have e : 686002709617 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 73 ^ 1, 27968147 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 343001354808) (rem := 686002709616) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 228667569872) (rem := 3065746292) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 98000387088) (rem := 319609929130) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9397297392) (rem := 649731144571) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 24528) (rem := 378827773560) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_850403095063 : Nat.Prime 850403095063 := by
  refine lucas_primality 850403095063 (3 : ZMod 850403095063) ?_ (fun q hq hd => ?_)
  · rw [show 850403095063 - 1 = 850403095062 from by norm_num]; reduce_mod_char
  · have e : 850403095063 - 1 = [2 ^ 1, 3 ^ 1, 223 ^ 1, 521 ^ 1, 1219919 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 425201547531) (rem := 850403095062) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 283467698354) (rem := 850400655222) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3813466794) (rem := 162729766144) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1632251622) (rem := 107746802891) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 697098) (rem := 217925314960) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1571511860719 : Nat.Prime 1571511860719 := by
  refine lucas_primality 1571511860719 (11 : ZMod 1571511860719) ?_ (fun q hq hd => ?_)
  · rw [show 1571511860719 - 1 = 1571511860718 from by norm_num]; reduce_mod_char
  · have e : 1571511860719 - 1 = [2 ^ 1, 3 ^ 1, 103 ^ 1, 433 ^ 1, 977 ^ 1, 6011 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 785755930359) (rem := 1571511860718) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 523837286906) (rem := 1175564724041) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 15257396706) (rem := 232608076322) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3629357646) (rem := 73052503954) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1608507534) (rem := 739783960724) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 261439338) (rem := 1565067846602) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_5844100138801 : Nat.Prime 5844100138801 := by
  refine lucas_primality 5844100138801 (39 : ZMod 5844100138801) ?_ (fun q hq hd => ?_)
  · rw [show 5844100138801 - 1 = 5844100138800 from by norm_num]; reduce_mod_char
  · have e : 5844100138801 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 7 ^ 1, 11 ^ 1, 17 ^ 1, 37 ^ 1, 193 ^ 1, 521 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2922050069400) (rem := 5844100138800) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1948033379600) (rem := 3898849014355) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1168820027760) (rem := 168710660029) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 834871448400) (rem := 2313013398304) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 531281830800) (rem := 4031245820467) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 343770596400) (rem := 1504211832417) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 157948652400) (rem := 193587787826) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 30280311600) (rem := 1351442645499) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11217082800) (rem := 532261738868) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_5844802782997 : Nat.Prime 5844802782997 := by
  refine lucas_primality 5844802782997 (5 : ZMod 5844802782997) ?_ (fun q hq hd => ?_)
  · rw [show 5844802782997 - 1 = 5844802782996 from by norm_num]; reduce_mod_char
  · have e : 5844802782997 - 1 = [2 ^ 2, 3 ^ 3, 2099 ^ 1, 25783013 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2922401391498) (rem := 5844802782996) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1948267594332) (rem := 5572568597916) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2784565404) (rem := 2764930648455) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 226692) (rem := 2283865981869) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_11905643330881 : Nat.Prime 11905643330881 := by
  refine lucas_primality 11905643330881 (7 : ZMod 11905643330881) ?_ (fun q hq hd => ?_)
  · rw [show 11905643330881 - 1 = 11905643330880 from by norm_num]; reduce_mod_char
  · have e : 11905643330881 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 23 ^ 1, 97 ^ 1, 25153 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 5952821665440) (rem := 11905643330880) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3968547776960) (rem := 3343525563345) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2381128666176) (rem := 1454908708599) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 915818717760) (rem := 737212015541) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 700331960640) (rem := 10685140722960) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 517636666560) (rem := 1278383570980) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 122738591040) (rem := 7529943984381) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 473328960) (rem := 8473149679318) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_31129845205681 : Nat.Prime 31129845205681 := by
  refine lucas_primality 31129845205681 (19 : ZMod 31129845205681) ?_ (fun q hq hd => ?_)
  · rw [show 31129845205681 - 1 = 31129845205680 from by norm_num]; reduce_mod_char
  · have e : 31129845205681 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 13 ^ 1, 17 ^ 1, 281 ^ 1, 232073 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 15564922602840) (rem := 31129845205680) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 10376615068560) (rem := 15763990543087) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6225969041136) (rem := 7862545861837) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2394603477360) (rem := 933506620967) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1831167365040) (rem := 3024926457528) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 110782367280) (rem := 2263574625413) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 134138160) (rem := 4094954845433) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_680097254967499 : Nat.Prime 680097254967499 := by
  refine lucas_primality 680097254967499 (2 : ZMod 680097254967499) ?_ (fun q hq hd => ?_)
  · rw [show 680097254967499 - 1 = 680097254967498 from by norm_num]; reduce_mod_char
  · have e : 680097254967499 - 1 = [2 ^ 1, 3 ^ 1, 19441 ^ 1, 5830437863 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 340048627483749) (rem := 680097254967498) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 226699084989166) (rem := 159555112469291) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 34982627178) (rem := 229977822239705) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_5830437863 hqx (exp := 116646) (rem := 433896630917115) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_5322960113892133441 : Nat.Prime 5322960113892133441 := by
  refine lucas_primality 5322960113892133441 (23 : ZMod 5322960113892133441) ?_ (fun q hq hd => ?_)
  · rw [show 5322960113892133441 - 1 = 5322960113892133440 from by norm_num]; reduce_mod_char
  · have e : 5322960113892133441 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 4, 17 ^ 1, 809 ^ 1, 1217 ^ 1, 1657 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2661480056946066720) (rem := 5322960113892133440) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1774320037964044480) (rem := 479007443090340667) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1064592022778426688) (rem := 2285472874329870146) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 760422873413161920) (rem := 4025366336020900521) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 409458470299394880) (rem := 2884468710315307356) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 313115300817184320) (rem := 2162952216395656885) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6579678756356160) (rem := 4659125484309364466) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4373837398432320) (rem := 433703328470745690) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3212408034937920) (rem := 2733213927825350556) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_154458987565304908081 : Nat.Prime 154458987565304908081 := by
  refine lucas_primality 154458987565304908081 (22 : ZMod 154458987565304908081) ?_ (fun q hq hd => ?_)
  · rw [show 154458987565304908081 - 1 = 154458987565304908080 from by norm_num]; reduce_mod_char
  · have e : 154458987565304908081 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 77229493782652454040) (rem := 154458987565304908080) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 51486329188434969360) (rem := 153707719926768190867) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 30891797513060981616) (rem := 97257578762099617919) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 22065569652186415440) (rem := 62342317593246970955) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9085822797959112240) (rem := 121276897999462730936) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4982547985977577680) (rem := 74477710659929038377) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1735494242306796720) (rem := 28954775254526202272) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8238252043591920) (rem := 128502659349271340404) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 13296291326640) (rem := 82062916363309179529) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_187344375361201003441 : Nat.Prime 187344375361201003441 := by
  refine lucas_primality 187344375361201003441 (7 : ZMod 187344375361201003441) ?_ (fun q hq hd => ?_)
  · rw [show 187344375361201003441 - 1 = 187344375361201003440 from by norm_num]; reduce_mod_char
  · have e : 187344375361201003441 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 11 ^ 1, 17 ^ 1, 31 ^ 1, 13913 ^ 1, 54217 ^ 1, 178513 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 93672187680600501720) (rem := 187344375361201003440) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 62448125120400334480) (rem := 151074112745837592689) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 37468875072240200688) (rem := 177997278617638054719) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 17031306851018273040) (rem := 66886178376851379664) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11020257374188294320) (rem := 55498232022066697395) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6043366947135516240) (rem := 2712327342107032316) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 13465419058520880) (rem := 95138739146420144888) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3455454476662320) (rem := 115422375990419231374) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1049471889224880) (rem := 58521660825565052709) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_263815884193138017859 : Nat.Prime 263815884193138017859 := by
  refine lucas_primality 263815884193138017859 (3 : ZMod 263815884193138017859) ?_ (fun q hq hd => ?_)
  · rw [show 263815884193138017859 - 1 = 263815884193138017858 from by norm_num]; reduce_mod_char
  · have e : 263815884193138017859 - 1 = [2 ^ 1, 3 ^ 2, 13 ^ 1, 23 ^ 2, 41 ^ 1, 59471 ^ 1, 874058123 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 131907942096569008929) (rem := 263815884193138017858) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 87938628064379339286) (rem := 4985626218720) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 20293529553318309066) (rem := 122030896806823834822) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11470255834484261646) (rem := 179645615899062129142) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6434533760808244338) (rem := 26848951943425886575) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4436042511360798) (rem := 93356766177130081296) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_874058123 hqx (exp := 301828765446) (rem := 156991528212215898544) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_308917975130609816161 : Nat.Prime 308917975130609816161 := by
  refine lucas_primality 308917975130609816161 (13 : ZMod 308917975130609816161) ?_ (fun q hq hd => ?_)
  · rw [show 308917975130609816161 - 1 = 308917975130609816160 from by norm_num]; reduce_mod_char
  · have e : 308917975130609816161 - 1 = [2 ^ 5, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 154458987565304908080) (rem := 308917975130609816160) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 102972658376869938720) (rem := 17576062560) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 61783595026121963232) (rem := 206590181932928584910) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 44131139304372830880) (rem := 167825244286979190014) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 18171645595918224480) (rem := 115321492361953978636) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9965095971955155360) (rem := 93065406286446501689) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3470988484613593440) (rem := 295851381508786004267) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 16476504087183840) (rem := 121238973810406622614) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 26592582653280) (rem := 292298248863797292695) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_391522268549910113761 : Nat.Prime 391522268549910113761 := by
  refine lucas_primality 391522268549910113761 (7 : ZMod 391522268549910113761) ?_ (fun q hq hd => ?_)
  · rw [show 391522268549910113761 - 1 = 391522268549910113760 from by norm_num]; reduce_mod_char
  · have e : 391522268549910113761 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 41 ^ 1, 3769 ^ 1, 83641 ^ 1, 3712249 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 195761134274955056880) (rem := 391522268549910113760) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 130507422849970037920) (rem := 231271064225077831481) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 78304453709982022752) (rem := 31905389043854728245) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 23030721679406477280) (rem := 326851294368334798426) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9549323623168539360) (rem := 61310283255149987668) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 103879614897827040) (rem := 14508914975452326175) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4680985025883360) (rem := 137293625435670238408) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 105467674326240) (rem := 20601890820612504744) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_617835950261219632321 : Nat.Prime 617835950261219632321 := by
  refine lucas_primality 617835950261219632321 (13 : ZMod 617835950261219632321) ?_ (fun q hq hd => ?_)
  · rw [show 617835950261219632321 - 1 = 617835950261219632320 from by norm_num]; reduce_mod_char
  · have e : 617835950261219632321 - 1 = [2 ^ 6, 3 ^ 3, 5 ^ 1, 7 ^ 1, 17 ^ 1, 31 ^ 1, 89 ^ 1, 18749 ^ 1, 11616697 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 308917975130609816160) (rem := 617835950261219632320) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 205945316753739877440) (rem := 193295184803823204143) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 123567190052243926464) (rem := 135041647953987295650) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 88262278608745661760) (rem := 65551264838099969656) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 36343291191836448960) (rem := 502873660097882331170) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 19930191943910310720) (rem := 197976818676267501944) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6941976969227186880) (rem := 203867665893113277926) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 32953008174367680) (rem := 444664815012419945237) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 53185165306560) (rem := 235395380913004348708) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1688970022366499085361 : Nat.Prime 1688970022366499085361 := by
  refine lucas_primality 1688970022366499085361 (19 : ZMod 1688970022366499085361) ?_ (fun q hq hd => ?_)
  · rw [show 1688970022366499085361 - 1 = 1688970022366499085360 from by norm_num]; reduce_mod_char
  · have e : 1688970022366499085361 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 2, 17 ^ 1, 41 ^ 1, 149 ^ 1, 809 ^ 1, 1709413193 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 844485011183249542680) (rem := 1688970022366499085360) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 562990007455499695120) (rem := 313841957584733611173) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 337794004473299817072) (rem := 730393477472656836958) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 241281431766642726480) (rem := 1362093641708984841444) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 99351177786264652080) (rem := 1458175416256592498542) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 41194390789426806960) (rem := 687568052343683270415) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11335369277627510640) (rem := 794475789489949900612) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2087725614791717040) (rem := 556889674905279995470) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_1709413193 hqx (exp := 988040825520) (rem := 1346243110665697671972) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_4632458802461936442001 : Nat.Prime 4632458802461936442001 := by
  refine lucas_primality 4632458802461936442001 (7 : ZMod 4632458802461936442001) ?_ (fun q hq hd => ?_)
  · rw [show 4632458802461936442001 - 1 = 4632458802461936442000 from by norm_num]; reduce_mod_char
  · have e : 4632458802461936442001 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 3, 17 ^ 1, 31 ^ 1, 73 ^ 1, 139 ^ 1, 25657 ^ 1, 1875793 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2316229401230968221000) (rem := 4632458802461936442000) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1544152934153978814000) (rem := 2824095767483113999563) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 926491760492387288400) (rem := 2725552651604867361331) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 272497576615408026000) (rem := 4121666342549931232022) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 149434154918126982000) (rem := 2778421075716455381935) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 63458339759752554000) (rem := 454843032959924251672) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 33327041744330478000) (rem := 3784997188369603435744) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 180553408522506000) (rem := 2736527710743310489002) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2469600218394000) (rem := 4273839752542140666278) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_6142943339981990979841 : Nat.Prime 6142943339981990979841 := by
  refine lucas_primality 6142943339981990979841 (7 : ZMod 6142943339981990979841) ?_ (fun q hq hd => ?_)
  · rw [show 6142943339981990979841 - 1 = 6142943339981990979840 from by norm_num]; reduce_mod_char
  · have e : 6142943339981990979841 - 1 = [2 ^ 8, 3 ^ 2, 5 ^ 1, 13 ^ 2, 17 ^ 2, 41 ^ 1, 197 ^ 1, 1351728281 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 3071471669990995489920) (rem := 6142943339981990979840) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2047647779993996993280) (rem := 2488760029108608127281) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1228588667996398195968) (rem := 4831843815929851032368) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 472534103075537767680) (rem := 1729395982672160015388) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 361349608234234763520) (rem := 190923987703541082134) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 149827886341024170240) (rem := 6063386863067679483866) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 31182453502446654720) (rem := 3660252589286864604910) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_1351728281 hqx (exp := 4544510480640) (rem := 2590801450044973918234) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_14102207757738301344667 : Nat.Prime 14102207757738301344667 := by
  refine lucas_primality 14102207757738301344667 (2 : ZMod 14102207757738301344667) ?_ (fun q hq hd => ?_)
  · rw [show 14102207757738301344667 - 1 = 14102207757738301344666 from by norm_num]; reduce_mod_char
  · have e : 14102207757738301344667 - 1 = [2 ^ 1, 3 ^ 1, 19 ^ 1, 101 ^ 1, 8369 ^ 1, 996617 ^ 1, 146844953 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 7051103878869150672333) (rem := 14102207757738301344666) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4700735919246100448222) (rem := 9412978877160) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 742221460933594807614) (rem := 11463514856404764106528) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 139625819383547538066) (rem := 860002731514019257552) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1685052904497347514) (rem := 9087046424170131318763) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 14150077469818698) (rem := 6489475046707793901520) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_146844953 hqx (exp := 96034677866922) (rem := 6210876543092564443790) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_148222903052887857582961 : Nat.Prime 148222903052887857582961 := by
  refine lucas_primality 148222903052887857582961 (19 : ZMod 148222903052887857582961) ?_ (fun q hq hd => ?_)
  · rw [show 148222903052887857582961 - 1 = 148222903052887857582960 from by norm_num]; reduce_mod_char
  · have e : 148222903052887857582961 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 43 ^ 1, 137 ^ 1, 2693 ^ 1, 16013775593 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 74111451526443928791480) (rem := 148222903052887857582960) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 49407634350962619194320) (rem := 74711190071700642766264) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 29644580610577571516592) (rem := 97655409073520151933651) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 13474809368444350689360) (rem := 100945967511233799781657) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11401761773299065967920) (rem := 90479880960977931974858) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8718994297228697504880) (rem := 77781450901128819620997) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3447044257043903664720) (rem := 27375643209903193002734) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1081919000386042756080) (rem := 103122243715862512358000) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 55040067973593708720) (rem := 113419930287194512502293) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_16013775593 hqx (exp := 9255962292720) (rem := 4396671571817664632815) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_292083232917564916412257 : Nat.Prime 292083232917564916412257 := by
  refine lucas_primality 292083232917564916412257 (10 : ZMod 292083232917564916412257) ?_ (fun q hq hd => ?_)
  · rw [show 292083232917564916412257 - 1 = 292083232917564916412256 from by norm_num]; reduce_mod_char
  · have e : 292083232917564916412257 - 1 = [2 ^ 5, 3 ^ 4, 7 ^ 2, 251 ^ 1, 1301 ^ 1, 2377 ^ 1, 13831 ^ 1, 214211 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 146041616458782458206128) (rem := 292083232917564916412256) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 97361077639188305470752) (rem := 241159873560980868056283) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 41726176131080702344608) (rem := 196311791142205818153155) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1163678218795079348256) (rem := 239145095492924710542334) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 224506712465461119456) (rem := 157332845536231998811326) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 122878936860565804128) (rem := 154182975208697792581639) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 21118012646776438176) (rem := 36660686025541370400129) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1363530504584568096) (rem := 169205819322008764270862) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_590440230397776959593681 : Nat.Prime 590440230397776959593681 := by
  refine lucas_primality 590440230397776959593681 (11 : ZMod 590440230397776959593681) ?_ (fun q hq hd => ?_)
  · rw [show 590440230397776959593681 - 1 = 590440230397776959593680 from by norm_num]; reduce_mod_char
  · have e : 590440230397776959593681 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 73 ^ 1, 233 ^ 1, 2237 ^ 1, 3209 ^ 1, 169318049 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 295220115198888479796840) (rem := 590440230397776959593680) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 196813410132592319864560) (rem := 254921573758117326786864) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 118088046079555391918736) (rem := 525316157413433658545761) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 84348604342539565656240) (rem := 68414341132712688404931) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 34731778258692762329040) (rem := 118554777801772502164626) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8088222334216122734160) (rem := 377898461031761073196631) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2534078242050544890960) (rem := 414970441997603996302227) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 263942883503700026640) (rem := 327158231897694958325730) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 183995085820435325520) (rem := 157947907406528233010910) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_169318049 hqx (exp := 3487166512282320) (rem := 170110332423670041574173) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_1095403448591351982886081 : Nat.Prime 1095403448591351982886081 := by
  refine lucas_primality 1095403448591351982886081 (7 : ZMod 1095403448591351982886081) ?_ (fun q hq hd => ?_)
  · rw [show 1095403448591351982886081 - 1 = 1095403448591351982886080 from by norm_num]; reduce_mod_char
  · have e : 1095403448591351982886081 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1, 23 ^ 1, 29 ^ 1, 102673 ^ 1, 121661 ^ 1, 424001 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 547701724295675991443040) (rem := 1095403448591351982886080) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 365134482863783994295360) (rem := 289460296567326544967486) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 219080689718270396577216) (rem := 497250603331662467769147) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 64435496975961881346240) (rem := 378743063561177913725175) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 57652813083755367520320) (rem := 886568615380837920813144) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 47626236895276173168960) (rem := 893785107038003379037121) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 37772532710046620099520) (rem := 139631844511227487434394) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 10668855965943840960) (rem := 363410806030260643408378) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9003735367877561280) (rem := 52625529787566332974610) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2583492606364966080) (rem := 420091106579880746134947) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_4257696543602770772646001 : Nat.Prime 4257696543602770772646001 := by
  refine lucas_primality 4257696543602770772646001 (23 : ZMod 4257696543602770772646001) ?_ (fun q hq hd => ?_)
  · rw [show 4257696543602770772646001 - 1 = 4257696543602770772646000 from by norm_num]; reduce_mod_char
  · have e : 4257696543602770772646001 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 3, 17 ^ 1, 109 ^ 1, 653 ^ 1, 6833 ^ 1, 85826901353 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 2128848271801385386323000) (rem := 4257696543602770772646000) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1419232181200923590882000) (rem := 1262503865815169254566361) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 851539308720554154529200) (rem := 2944447831058537353997286) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 250452737858986516038000) (rem := 2248915518086247382708826) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 39061436179841933694000) (rem := 3112685988464087989683004) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6520209101995054782000) (rem := 2199475077556148845568600) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 623107938475453062000) (rem := 3278725428516616863093927) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_85826901353 hqx (exp := 49607948982000) (rem := 40148578956622738743043) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_15092859525078825081684721 : Nat.Prime 15092859525078825081684721 := by
  refine lucas_primality 15092859525078825081684721 (13 : ZMod 15092859525078825081684721) ?_ (fun q hq hd => ?_)
  · rw [show 15092859525078825081684721 - 1 = 15092859525078825081684720 from by norm_num]; reduce_mod_char
  · have e : 15092859525078825081684721 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 17 ^ 1, 41 ^ 1, 383 ^ 1, 7753 ^ 1, 1171981 ^ 1, 8642057 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 7546429762539412540842360) (rem := 15092859525078825081684720) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5030953175026275027228240) (rem := 11242979085777978125768537) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3018571905015765016336944) (rem := 7528680598331038170986848) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 887815266181107357746160) (rem := 7951816781688134671499224) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 368118525001922562967920) (rem := 8494337118725441125157956) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 39406943929709726061840) (rem := 1361453900319334069315037) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1946712179166622608240) (rem := 2910331912294578730904399) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 12878075263232787120) (rem := 8405679352123310777133752) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1746442950454830960) (rem := 10973436805176030949954124) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_34714989264498225976453201 : Nat.Prime 34714989264498225976453201 := by
  refine lucas_primality 34714989264498225976453201 (13 : ZMod 34714989264498225976453201) ?_ (fun q hq hd => ?_)
  · rw [show 34714989264498225976453201 - 1 = 34714989264498225976453200 from by norm_num]; reduce_mod_char
  · have e : 34714989264498225976453201 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 2, 17 ^ 1, 29 ^ 1, 97 ^ 1, 157 ^ 1, 283 ^ 1, 317 ^ 1, 18257 ^ 1, 2352569 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 17357494632249112988226600) (rem := 34714989264498225976453200) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 11571663088166075325484400) (rem := 10099981508292588533680532) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6942997852899645195290640) (rem := 15888757456745343784564047) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2042058192029307410379600) (rem := 3271766400211544452985475) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1197068595327525033670800) (rem := 19714793806984554599938025) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 357886487262868309035600) (rem := 20809202033610619633594171) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 221114581302536471187600) (rem := 12932980247656305479756323) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 122667806588332953980400) (rem := 21791223462470931658734777) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 109511007143527526739600) (rem := 8564626202966537261090480) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1901461864736716107600) (rem := 10690900381480917898728163) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 14756204500058542800) (rem := 20477223021294096717403411) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_44588753651715539427437281 : Nat.Prime 44588753651715539427437281 := by
  refine lucas_primality 44588753651715539427437281 (7 : ZMod 44588753651715539427437281) ?_ (fun q hq hd => ?_)
  · rw [show 44588753651715539427437281 - 1 = 44588753651715539427437280 from by norm_num]; reduce_mod_char
  · have e : 44588753651715539427437281 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 17 ^ 1, 73 ^ 1, 313 ^ 1, 877 ^ 1, 307301 ^ 1, 887369321 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 22294376825857769713718640) (rem := 44588753651715539427437280) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 14862917883905179809145760) (rem := 26384985227716738140783357) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8917750730343107885487456) (rem := 7807850307470586220699957) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2622867861865619966319840) (rem := 14678191221855118804027730) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 610804844544048485307360) (rem := 12435701199191587923074098) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 142456081954362745774560) (rem := 10827872632270917114309325) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 50842364483142006188640) (rem := 2591770570846223719153502) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 145097977721242493280) (rem := 9870518629974292464740708) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_887369321 hqx (exp := 50248247935219680) (rem := 23084410912367260548176645) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_49712937585586541809314241 : Nat.Prime 49712937585586541809314241 := by
  refine lucas_primality 49712937585586541809314241 (22 : ZMod 49712937585586541809314241) ?_ (fun q hq hd => ?_)
  · rw [show 49712937585586541809314241 - 1 = 49712937585586541809314240 from by norm_num]; reduce_mod_char
  · have e : 49712937585586541809314241 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 17 ^ 1, 37 ^ 1, 41 ^ 1, 109 ^ 1, 127 ^ 1, 2897 ^ 1, 7152978793 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 24856468792793270904657120) (rem := 49712937585586541809314240) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 16570979195195513936438080) (rem := 44922939733950679930879418) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9942587517117308361862848) (rem := 22363739480806215686955308) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 7101848226512363115616320) (rem := 16089424733200065716527881) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 2924290446210973047606720) (rem := 211677471177316327030401) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1343592907718555184035520) (rem := 34603972914315220522695469) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1212510672819183946568640) (rem := 44019930465148314811634358) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 456081996198041667975360) (rem := 36666491220745465745564651) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 391440453429815289837120) (rem := 14198022904006748064501735) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 17160144144144474217920) (rem := 28358523021651218378141911) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_7152978793 hqx (exp := 6949962948895680) (rem := 30821527047556548217997107) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_75086230851720457458598081 : Nat.Prime 75086230851720457458598081 := by
  refine lucas_primality 75086230851720457458598081 (29 : ZMod 75086230851720457458598081) ?_ (fun q hq hd => ?_)
  · rw [show 75086230851720457458598081 - 1 = 75086230851720457458598080 from by norm_num]; reduce_mod_char
  · have e : 75086230851720457458598081 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 11 ^ 1, 13 ^ 1, 17 ^ 1, 73 ^ 1, 23977 ^ 1, 1873513 ^ 1, 3270457 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 37543115425860228729299040) (rem := 75086230851720457458598080) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 25028743617240152486199360) (rem := 50164892047715565924783884) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 15017246170344091491719616) (rem := 59575252897564766635536151) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6826020986520041587145280) (rem := 37974470453851736091465826) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 5775863911670804419892160) (rem := 44400832531295167583570123) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 4416837108924732791682240) (rem := 20867501348573158156921801) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1028578504818088458336960) (rem := 21473227190888840674861067) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3131594063132187407040) (rem := 70557377107474270706553817) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 40077774134324372160) (rem := 44680659743683608221626814) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 22958941472620021440) (rem := 21514812229647093314914045) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_157790771387783474187901681 : Nat.Prime 157790771387783474187901681 := by
  refine lucas_primality 157790771387783474187901681 (46 : ZMod 157790771387783474187901681) ?_ (fun q hq hd => ?_)
  · rw [show 157790771387783474187901681 - 1 = 157790771387783474187901680 from by norm_num]; reduce_mod_char
  · have e : 157790771387783474187901681 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 13 ^ 1, 17 ^ 1, 19 ^ 1, 41 ^ 1, 79 ^ 1, 24793 ^ 1, 216641645201 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 78895385693891737093950840) (rem := 157790771387783474187901680) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 52596923795927824729300560) (rem := 128795136153219986079706857) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 31558154277556694837580336) (rem := 36671248266588331074577248) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 12137751645214113399069360) (rem := 2271995413202934410189180) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 9281810081634322011053040) (rem := 5966810128202699781002737) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 8304777441462288115152720) (rem := 117506119145486799983484895) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 3848555399702035955802480) (rem := 102738287985453238282466992) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 1997351536554221192251920) (rem := 110893397454494339645860817) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 6364327487104564763760) (rem := 127901076745872497519675346) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_216641645201 hqx (exp := 728349211165680) (rem := 155576231510888710411160007) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

theorem prime_177208342683739494697085521 : Nat.Prime 177208342683739494697085521 := by
  refine lucas_primality 177208342683739494697085521 (13 : ZMod 177208342683739494697085521) ?_ (fun q hq hd => ?_)
  · rw [show 177208342683739494697085521 - 1 = 177208342683739494697085520 from by norm_num]; reduce_mod_char
  · have e : 177208342683739494697085521 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 17 ^ 1, 347 ^ 1, 521 ^ 1, 673 ^ 1, 433889 ^ 1, 822740921 ^ 1].prod := by norm_num
    rw [e] at hd; obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lucas_chk hq (by norm_num) hqx (exp := 88604171341869747348542760) (rem := 177208342683739494697085520) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 59069447561246498232361840) (rem := 675241973361197185877318) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 35441668536747898939417104) (rem := 154180442698008285557467177) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 10424020157867029099828560) (rem := 98198043403505692725270366) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 510686866523744941490160) (rem := 69396127806186637473236569) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 340131175976467360263120) (rem := 69981351834155286567383508) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 263311058965437584988240) (rem := 47828478854521729485635670) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq (by norm_num) hqx (exp := 408418610943673369680) (rem := 91172202644042177920507970) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)
    · exact lucas_chk hq prime_822740921 hqx (exp := 215387782667175120) (rem := 152958629641469686898283034) (by norm_num) (by push_cast; reduce_mod_char) (by norm_num)

-- Section 3. Sieve of z in ranges of 300.

theorem zs2_0 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 7
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 49 283 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 11
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g51329 := a7 51329 (by norm_num) ((d16 121 14641 8977 51328 (by norm_num)).trans hd)
      have g5 := a1 5 51329 g51329 (by norm_num)
      exact a3 3 5 g5 51329 g51329 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 121 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 13
    · exfalso; have hd := D8 he
      have g407865361 := b7 407865361 prime_407865361 (by norm_num) ((d8 169 28561 407865360 (by norm_num)).trans hd)
      have g12583 := a1 12583 407865361 g407865361 (by norm_num)
      exact a6 11 12583 g12583 (by norm_num)
    · exfalso; have hd := D16 he
      have g2657 := a7 2657 (by norm_num) ((d16 169 1991 2494 2656 (by norm_num)).trans hd)
      have g443 := a1 443 2657 g2657 (by norm_num)
      exact a3 3 443 g443 2657 g2657 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 169 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 17
    · exfalso; have hd := D8 he
      have g18913 := a7 18913 (by norm_num) ((d8 289 7869 18912 (by norm_num)).trans hd)
      exact a6 7 18913 g18913 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 32 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g1409 := a7 1409 (by norm_num) ((d32 289 390 1337 957 1408 (by norm_num)).trans hd)
      have g5 := a1 5 1409 g1409 (by norm_num)
      exact a3 3 5 g5 1409 g1409 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 19
    · exfalso; have hd := D8 he
      have g15073 := a7 15073 (by norm_num) ((d8 361 9737 15072 (by norm_num)).trans hd)
      have g7537 := a1 7537 15073 g15073 (by norm_num)
      have g3769 := a1 3769 7537 g7537 (by norm_num)
      have g29 := a1 29 3769 g3769 (by norm_num)
      have g5 := a1 5 3769 g3769 (by norm_num)
      exact a3 3 29 g29 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 70 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g151681 := a7 151681 (by norm_num) ((d32 361 130321 144833 25675 151680 (by norm_num)).trans hd)
      have g149 := a1 149 151681 g151681 (by norm_num)
      exact a6 5 149 g149 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 23
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 15 225 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 29
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 69 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 31
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1889 := a7 1889 (by norm_num) ((d16 961 1689 331 1888 (by norm_num)).trans hd)
      exact a6 3 1889 g1889 (by norm_num)
    · exfalso; have hd := D32 he
      have g4801 := a7 4801 (by norm_num) ((d32 961 1729 3219 1403 4800 (by norm_num)).trans hd)
      exact a6 7 4801 g4801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 37
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 22 35 327 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 41
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 43
    · exfalso; have hd := D8 he
      have g5844100138801 := b7 5844100138801 prime_5844100138801 (by norm_num) ((d8 1849 3418801 5844100138800 (by norm_num)).trans hd)
      have g67 := a1 67 5844100138801 g5844100138801 (by norm_num)
      have g17 := a1 17 67 g67 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g769 := a7 769 (by norm_num) ((d16 311 596 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 696 156 123 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 47
    · exfalso; have hd := D8 he
      have g11905643330881 := b7 11905643330881 prime_11905643330881 (by norm_num) ((d8 2209 4879681 11905643330880 (by norm_num)).trans hd)
      have g850403095063 := b1 850403095063 prime_850403095063 11905643330881 g11905643330881 (by norm_num)
      have g41 := a1 41 850403095063 g850403095063 (by norm_num)
      exact a3 7 41 g41 11905643330881 g11905643330881 (by norm_num)
    · exfalso; have hd := D16 he
      have g5441 := a7 5441 (by norm_num) ((d16 2209 4545 2989 5440 (by norm_num)).trans hd)
      have g907 := a1 907 5441 g5441 (by norm_num)
      have g227 := a1 227 907 g907 (by norm_num)
      exact a3 3 227 g227 5441 g5441 (by norm_num)
    · exfalso; have hd := D32 he
      have g292993 := a7 292993 (by norm_num) ((d32 2209 191793 162678 124945 292992 (by norm_num)).trans hd)
      have g191 := a1 191 292993 g292993 (by norm_num)
      have g59 := a1 59 292993 g292993 (by norm_num)
      exact a3 3 191 g191 59 g59 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 53
    · exfalso; have hd := D8 he
      have g31129845205681 := b7 31129845205681 prime_31129845205681 (by norm_num) ((d8 2809 7890481 31129845205680 (by norm_num)).trans hd)
      have g5743 := a1 5743 31129845205681 g31129845205681 (by norm_num)
      have g359 := a1 359 5743 g5743 (by norm_num)
      exact a6 3 359 g359 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 59
    · exfalso; have hd := D8 he
      have g337 := a7 337 (by norm_num) ((d8 111 189 336 (by norm_num)).trans hd)
      exact a6 13 337 g337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 61
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g14593 := a7 14593 (by norm_num) ((d16 3721 11677 9930 14592 (by norm_num)).trans hd)
      have g7297 := a1 7297 14593 g14593 (by norm_num)
      have g89 := a1 89 7297 g7297 (by norm_num)
      exact a6 3 89 g89 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 67
    · exfalso; have hd := D8 he
      have g1153 := a7 1153 (by norm_num) ((d8 1030 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 120 8 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 71
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 23 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 73
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 189 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 79
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1021793 := a7 1021793 (by norm_num) ((d16 6241 121947 917280 1021792 (by norm_num)).trans hd)
      have g170299 := a1 170299 1021793 g1021793 (by norm_num)
      exact a6 5 170299 g170299 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 404 229 357 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 83
    · exfalso; have hd := D8 he
      have g10289 := a7 10289 (by norm_num) ((d8 6889 5453 10288 (by norm_num)).trans hd)
      exact a6 7 10289 g10289 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 542 71 425 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 89
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 8 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 97
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g7681 := a7 7681 (by norm_num) ((d16 1728 5756 3383 7680 (by norm_num)).trans hd)
      have g167 := a1 167 7681 g7681 (by norm_num)
      have g23 := a1 23 7681 g7681 (by norm_num)
      exact a3 3 167 g167 23 g23 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 177 171 391 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)

theorem zs2_100 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 100 ≤ z) (hi : z < 200)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 101
    · exfalso; have hd := D8 he
      have g929 := a7 929 (by norm_num) ((d8 911 324 928 (by norm_num)).trans hd)
      have g5 := a1 5 929 g929 (by norm_num)
      exact a3 3 5 g5 929 g929 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 317 237 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 103
    · exfalso; have hd := D8 he
      have g10433 := a7 10433 (by norm_num) ((d8 176 10110 10432 (by norm_num)).trans hd)
      have g47 := a1 47 10433 g10433 (by norm_num)
      exact a3 3 47 g47 10433 g10433 (by norm_num)
    · exfalso; have hd := D16 he
      have g118369 := a7 118369 (by norm_num) ((d16 10609 100331 91432 118368 (by norm_num)).trans hd)
      have g19 := a1 19 118369 g118369 (by norm_num)
      exact a3 5 19 g19 118369 g118369 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 873 287 830 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 107
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := a7 673 (by norm_num) ((d16 8 64 58 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D32 he
      have g4801 := a7 4801 (by norm_num) ((d32 1847 2699 1484 3398 4800 (by norm_num)).trans hd)
      exact a6 7 4801 g4801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 109
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1601 := a7 1601 (by norm_num) ((d16 674 1193 1561 1600 (by norm_num)).trans hd)
      exact a6 3 1601 g1601 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 351 983 75 1013 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 113
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 465 136 40 62 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 127
    · exfalso; have hd := D8 he
      have g14369 := a7 14369 (by norm_num) ((d8 1760 8265 14368 (by norm_num)).trans hd)
      have g5 := a1 5 14369 g14369 (by norm_num)
      exact a3 3 5 g5 14369 g14369 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g1207681 := a7 1207681 (by norm_num) ((d32 16129 493226 249479 723425 1207680 (by norm_num)).trans hd)
      have g86263 := a1 86263 1207681 g1207681 (by norm_num)
      have g41 := a1 41 86263 g86263 (by norm_num)
      exact a3 7 41 g41 1207681 g1207681 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 131
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 110 251 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 99 372 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 137
    · exfalso; have hd := D8 he
      have g1095793 := a7 1095793 (by norm_num) ((d8 18769 525808 1095792 (by norm_num)).trans hd)
      have g2699 := a1 2699 1095793 g1095793 (by norm_num)
      exact a6 3 2699 g2699 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 8 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g1601 := a7 1601 (by norm_num) ((d32 1158 927 1193 1561 1600 (by norm_num)).trans hd)
      exact a6 3 1601 g1601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 139
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 1066 895 239 1139 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 149
    · exfalso; have hd := D8 he
      have g23873 := a7 23873 (by norm_num) ((d8 22201 2443 23872 (by norm_num)).trans hd)
      have g23 := a1 23 23873 g23873 (by norm_num)
      exact a3 3 23 g23 23873 g23873 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 151
    · exfalso; have hd := D8 he
      have g1873 := a7 1873 (by norm_num) ((d8 325 737 1872 (by norm_num)).trans hd)
      have g937 := a1 937 1873 g1873 (by norm_num)
      have g67 := a1 67 937 g937 (by norm_num)
      have g17 := a1 17 67 g67 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g7937 := a7 7937 (by norm_num) ((d32 6927 4164 4488 5975 7936 (by norm_num)).trans hd)
      exact a6 3 7937 g7937 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 157
    · exfalso; have hd := D8 he
      have g1297 := a7 1297 (by norm_num) ((d8 6 36 1296 (by norm_num)).trans hd)
      have g59 := a1 59 1297 g1297 (by norm_num)
      have g11 := a1 11 1297 g1297 (by norm_num)
      exact a3 3 59 g59 11 g11 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 163
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := a7 577 (by norm_num) ((d16 27 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 167
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g19009 := a7 19009 (by norm_num) ((d32 8880 5068 3465 11546 19008 (by norm_num)).trans hd)
      have g1901 := a1 1901 19009 g19009 (by norm_num)
      have g5 := a1 5 19009 g19009 (by norm_num)
      exact a3 3 1901 g1901 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 173
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 14 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 179
    · exfalso; have hd := D8 he
      have g1009 := a7 1009 (by norm_num) ((d8 762 469 1008 (by norm_num)).trans hd)
      have g101 := a1 101 1009 g1009 (by norm_num)
      have g5 := a1 5 1009 g1009 (by norm_num)
      exact a3 3 101 g101 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 181
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g6113 := a7 6113 (by norm_num) ((d16 2196 5372 5024 6112 (by norm_num)).trans hd)
      have g1019 := a1 1019 6113 g6113 (by norm_num)
      exact a3 3 1019 g1019 6113 g6113 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 191
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 95 98 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g25537 := a7 25537 (by norm_num) ((d16 10944 2606 23931 25536 (by norm_num)).trans hd)
      exact a6 113 25537 g25537 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 193
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := a7 3329 (by norm_num) ((d16 630 749 1729 3328 (by norm_num)).trans hd)
      exact a6 3 3329 g3329 (by norm_num)
    · exfalso; have hd := D32 he
      have g7489 := a7 7489 (by norm_num) ((d32 7293 971 6716 5898 7488 (by norm_num)).trans hd)
      have g107 := a1 107 7489 g7489 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 197
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 2 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 359 458 596 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 199
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

theorem zs2_200 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 200 ≤ z) (hi : z < 300)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 211
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 60 2 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 223
    · exfalso; have hd := D8 he
      have g618577 := a7 618577 (by norm_num) ((d8 49729 521172 618576 (by norm_num)).trans hd)
      have g309289 := a1 309289 618577 g618577 (by norm_num)
      have g197 := a1 197 309289 g309289 (by norm_num)
      exact a6 3 197 g197 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 128 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g2753 := a7 2753 (by norm_num) ((d32 175 342 1338 794 2752 (by norm_num)).trans hd)
      exact a6 3 2753 g2753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 227
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 129 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 229
    · exfalso; have hd := D8 he
      have g449 := a7 449 (by norm_num) ((d8 357 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g53569 := a7 53569 (by norm_num) ((d16 52441 40297 11112 53568 (by norm_num)).trans hd)
      have g11 := a1 11 53569 g53569 (by norm_num)
      have g5 := a1 5 53569 g53569 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 233
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3169 := a7 3169 (by norm_num) ((d16 416 1930 1325 3168 (by norm_num)).trans hd)
      have g317 := a1 317 3169 g3169 (by norm_num)
      have g5 := a1 5 3169 g3169 (by norm_num)
      exact a3 3 317 g317 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g4289 := a7 4289 (by norm_num) ((d32 2821 1946 4018 528 4288 (by norm_num)).trans hd)
      have g5 := a1 5 4289 g4289 (by norm_num)
      exact a3 3 5 g5 4289 g4289 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 239
    · exfalso; have hd := D8 he
      have g5322960113892133441 := b7 5322960113892133441 prime_5322960113892133441 (by norm_num) ((d8 57121 3262808641 5322960113892133440 (by norm_num)).trans hd)
      have g3515089 := a1 3515089 5322960113892133441 g5322960113892133441 (by norm_num)
      exact a3 31 3515089 g3515089 5322960113892133441 g5322960113892133441 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 241
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 391 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D32 he
      have g5569 := a7 5569 (by norm_num) ((d32 2391 3087 1010 973 5568 (by norm_num)).trans hd)
      have g557 := a1 557 5569 g5569 (by norm_num)
      exact a6 3 557 g557 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 251
    · exfalso; have hd := D8 he
      have g1553 := a7 1553 (by norm_num) ((d8 881 1214 1552 (by norm_num)).trans hd)
      have g37 := a1 37 1553 g1553 (by norm_num)
      have g19 := a1 19 37 g37 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 1553 g1553 (by norm_num)
    · exfalso; have hd := D16 he
      have g769 := a7 769 (by norm_num) ((d16 712 173 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 257
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g65537 := a7 65537 (by norm_num) ((d32 512 65533 16 256 65536 (by norm_num)).trans hd)
      exact a6 3 65537 g65537 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 263
    · exfalso; have hd := D8 he
      have g85889 := a7 85889 (by norm_num) ((d8 69169 75594 85888 (by norm_num)).trans hd)
      have g5 := a1 5 85889 g85889 (by norm_num)
      exact a3 3 5 g5 85889 g85889 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g57089 := a7 57089 (by norm_num) ((d32 12080 6916 47563 30255 57088 (by norm_num)).trans hd)
      have g5 := a1 5 57089 g57089 (by norm_num)
      exact a3 3 5 g5 57089 g57089 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 269
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := a7 929 (by norm_num) ((d16 828 911 324 928 (by norm_num)).trans hd)
      have g5 := a1 5 929 g929 (by norm_num)
      exact a3 3 5 g5 929 g929 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 179 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 271
    · exfalso; have hd := D8 he
      have g113089 := a7 113089 (by norm_num) ((d8 73441 26804 113088 (by norm_num)).trans hd)
      have g263 := a1 263 113089 g113089 (by norm_num)
      have g5 := a1 5 113089 g113089 (by norm_num)
      exact a3 3 263 g263 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 802 983 75 1013 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 277
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4673 := a7 4673 (by norm_num) ((d16 1961 4315 1993 4672 (by norm_num)).trans hd)
      have g41 := a1 41 4673 g4673 (by norm_num)
      exact a3 3 41 g41 4673 g4673 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 58 930 830 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 281
    · exfalso; have hd := D8 he
      have g340577 := a7 340577 (by norm_num) ((d8 78961 236959 340576 (by norm_num)).trans hd)
      exact a6 3 340577 g340577 (by norm_num)
    · exfalso; have hd := D16 he
      have g3457 := a7 3457 (by norm_num) ((d16 2907 1741 2749 3456 (by norm_num)).trans hd)
      have g13 := a1 13 3457 g3457 (by norm_num)
      exact a3 7 13 g13 3457 g3457 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 24 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 283
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g120929 := a7 120929 (by norm_num) ((d16 80089 52832 57975 120928 (by norm_num)).trans hd)
      have g5 := a1 5 120929 g120929 (by norm_num)
      exact a3 3 5 g5 120929 g120929 (by norm_num)
    · exfalso; have hd := D32 he
      have g3329 := a7 3329 (by norm_num) ((d32 193 630 749 1729 3328 (by norm_num)).trans hd)
      exact a6 3 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 293
    · exfalso; have hd := D8 he
      have g353 := a7 353 (by norm_num) ((d8 70 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D16 he
      have g1409 := a7 1409 (by norm_num) ((d16 1309 137 452 1408 (by norm_num)).trans hd)
      have g5 := a1 5 1409 g1409 (by norm_num)
      exact a3 3 5 g5 1409 g1409 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

theorem zs2_300 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 300 ≤ z) (hi : z < 400)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 307
    · exfalso; have hd := D8 he
      have g337 := a7 337 (by norm_num) ((d8 226 189 336 (by norm_num)).trans hd)
      exact a6 13 337 g337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 540 737 387 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 311
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 362 65 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 313
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g585857 := a7 585857 (by norm_num) ((d16 97969 415587 153398 585856 (by norm_num)).trans hd)
      have g13 := a1 13 585857 g585857 (by norm_num)
      exact a3 7 13 g13 585857 g585857 (by norm_num)
    · exfalso; have hd := D32 he
      have g137537 := a7 137537 (by norm_num) ((d32 97969 42953 38891 15492 137536 (by norm_num)).trans hd)
      exact a6 3 137537 g137537 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 317
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 331
    · exfalso; have hd := D8 he
      have g72673 := a7 72673 (by norm_num) ((d8 36888 67965 72672 (by norm_num)).trans hd)
      have g179 := a1 179 72673 g72673 (by norm_num)
      exact a6 3 179 g179 (by norm_num)
    · exfalso; have hd := D16 he
      have g36833 := a7 36833 (by norm_num) ((d16 35895 32685 4893 36832 (by norm_num)).trans hd)
      have g877 := a1 877 36833 g36833 (by norm_num)
      have g439 := a1 439 877 g877 (by norm_num)
      have g5 := a1 5 439 g439 (by norm_num)
      exact a3 3 5 g5 36833 g36833 (by norm_num)
    · exfalso; have hd := D32 he
      have g30977 := a7 30977 (by norm_num) ((d32 16630 25221 17123 30801 30976 (by norm_num)).trans hd)
      exact a6 3 30977 g30977 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 337
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 347
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 36 237 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 170 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 349
    · exfalso; have hd := D8 he
      have g449 := a7 449 (by norm_num) ((d8 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g81409 := a7 81409 (by norm_num) ((d16 40392 77304 80771 81408 (by norm_num)).trans hd)
      have g1163 := a1 1163 81409 g81409 (by norm_num)
      have g5 := a1 5 81409 g81409 (by norm_num)
      exact a3 3 1163 g1163 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 240 32 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 353
    · exfalso; have hd := D8 he
      have g12738353 := a7 12738353 (by norm_num) ((d8 124609 12088927 12738352 (by norm_num)).trans hd)
      have g229 := a1 229 12738353 g12738353 (by norm_num)
      have g5 := a1 5 229 g229 (by norm_num)
      exact a3 3 5 g5 12738353 g12738353 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 124 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 359
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 36 237 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 367
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 373
    · exfalso; have hd := D8 he
      have g187344375361201003441 := b7 187344375361201003441 prime_187344375361201003441 (by norm_num) ((d8 139129 19356878641 187344375361201003440 (by norm_num)).trans hd)
      have g3594931 := a1 3594931 187344375361201003441 g187344375361201003441 (by norm_num)
      have g14431 := a1 14431 187344375361201003441 g187344375361201003441 (by norm_num)
      exact a3 11 3594931 g3594931 14431 g14431 (by norm_num)
    · exfalso; have hd := D16 he
      have g371873 := a7 371873 (by norm_num) ((d16 139129 145245 126608 371872 (by norm_num)).trans hd)
      have g61979 := a1 61979 371873 g371873 (by norm_num)
      exact a3 3 61979 g61979 371873 g371873 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 169 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 379
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g68897 := a7 68897 (by norm_num) ((d16 5847 14497 27159 68896 (by norm_num)).trans hd)
      have g11483 := a1 11483 68897 g68897 (by norm_num)
      exact a6 3 11483 g11483 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 383
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 541 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D32 he
      have g7489 := a7 7489 (by norm_num) ((d32 4398 5806 1647 1591 7488 (by norm_num)).trans hd)
      have g107 := a1 107 7489 g7489 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 389
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g18913 := a7 18913 (by norm_num) ((d16 17 289 7869 18912 (by norm_num)).trans hd)
      exact a6 7 18913 g18913 (by norm_num)
    · exfalso; have hd := D32 he
      have g419201 := a7 419201 (by norm_num) ((d32 151321 28818 39943 383444 419200 (by norm_num)).trans hd)
      exact a6 3 419201 g419201 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 397
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 121 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)

theorem zs2_400 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 400 ≤ z) (hi : z < 500)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 401
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4129 := a7 4129 (by norm_num) ((d16 3899 3352 895 4128 (by norm_num)).trans hd)
      have g59 := a1 59 4129 g4129 (by norm_num)
      have g5 := a1 5 4129 g4129 (by norm_num)
      exact a3 3 59 g59 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 409
    · exfalso; have hd := D8 he
      have g391522268549910113761 := b7 391522268549910113761 prime_391522268549910113761 (by norm_num) ((d8 167281 27982932961 391522268549910113760 (by norm_num)).trans hd)
      have g1291 := a1 1291 391522268549910113761 g391522268549910113761 (by norm_num)
      have g37 := a1 37 391522268549910113761 g391522268549910113761 (by norm_num)
      exact a3 19 1291 g1291 37 g37 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 419
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 124 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 421
    · exfalso; have hd := D8 he
      have g264289 := a7 264289 (by norm_num) ((d8 177241 188674 264288 (by norm_num)).trans hd)
      have g19 := a1 19 264289 g264289 (by norm_num)
      exact a3 5 19 g19 264289 g264289 (by norm_num)
    · exfalso; have hd := D16 he
      have g1217 := a7 1217 (by norm_num) ((d16 776 978 1139 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 67 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 431
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g411361 := a7 411361 (by norm_num) ((d16 185761 131636 277093 411360 (by norm_num)).trans hd)
      have g29383 := a1 29383 411361 g411361 (by norm_num)
      have g3673 := a1 3673 29383 g29383 (by norm_num)
      have g167 := a1 167 3673 g3673 (by norm_num)
      have g11 := a1 11 3673 g3673 (by norm_num)
      exact a3 3 167 g167 11 g11 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 544 512 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 433
    · exfalso; have hd := D8 he
      have g617835950261219632321 := b7 617835950261219632321 prime_617835950261219632321 (by norm_num) ((d8 187489 35152125121 617835950261219632320 (by norm_num)).trans hd)
      have g308917975130609816161 := b1 308917975130609816161 prime_308917975130609816161 617835950261219632321 g617835950261219632321 (by norm_num)
      have g154458987565304908081 := b1 154458987565304908081 prime_154458987565304908081 308917975130609816161 g308917975130609816161 (by norm_num)
      have g293 := a1 293 154458987565304908081 g154458987565304908081 (by norm_num)
      exact a6 7 293 g293 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 136 249 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 439
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g328897 := a7 328897 (by norm_num) ((d32 192721 32322 134812 84918 328896 (by norm_num)).trans hd)
      have g164449 := a1 164449 328897 g328897 (by norm_num)
      exact a6 5 164449 g164449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 443
    · exfalso; have hd := D8 he
      have g230251457 := b7 230251457 prime_230251457 (by norm_num) ((d8 196249 61676682 230251456 (by norm_num)).trans hd)
      have g93827 := a1 93827 230251457 g230251457 (by norm_num)
      exact a3 3 93827 g93827 230251457 g230251457 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g25601 := a7 25601 (by norm_num) ((d32 17042 12020 13957 25441 25600 (by norm_num)).trans hd)
      have g17 := a1 17 25601 g25601 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 449
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 796 776 978 1139 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 457
    · exfalso; have hd := D8 he
      have g61729 := a7 61729 (by norm_num) ((d8 23662 8214 61728 (by norm_num)).trans hd)
      have g6173 := a1 6173 61729 g61729 (by norm_num)
      exact a6 3 6173 g6173 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 23 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 461
    · exfalso; have hd := D8 he
      have g14657 := a7 14657 (by norm_num) ((d8 7323 11023 14656 (by norm_num)).trans hd)
      have g349 := a1 349 14657 g14657 (by norm_num)
      exact a6 5 349 g349 (by norm_num)
    · exfalso; have hd := D16 he
      have g5153 := a7 5153 (by norm_num) ((d16 1248 1298 4926 5152 (by norm_num)).trans hd)
      have g859 := a1 859 5153 g5153 (by norm_num)
      have g5 := a1 5 859 g859 (by norm_num)
      exact a3 3 5 g5 5153 g5153 (by norm_num)
    · exfalso; have hd := D32 he
      have g29761 := a7 29761 (by norm_num) ((d32 4194 885 9439 20048 29760 (by norm_num)).trans hd)
      have g647 := a1 647 29761 g29761 (by norm_num)
      exact a6 3 647 g647 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 463
    · exfalso; have hd := D8 he
      have g5009 := a7 5009 (by norm_num) ((d8 3991 4470 5008 (by norm_num)).trans hd)
      have g5 := a1 5 5009 g5009 (by norm_num)
      exact a3 3 5 g5 5009 g5009 (by norm_num)
    · exfalso; have hd := D16 he
      have g3169 := a7 3169 (by norm_num) ((d16 2046 3036 1844 3168 (by norm_num)).trans hd)
      have g317 := a1 317 3169 g3169 (by norm_num)
      have g5 := a1 5 3169 g3169 (by norm_num)
      exact a3 3 317 g317 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 587 57 173 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 467
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 479
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 197 2 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 487
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 491
    · exfalso; have hd := D8 he
      have g1688970022366499085361 := b7 1688970022366499085361 prime_1688970022366499085361 (by norm_num) ((d8 241081 58120048561 1688970022366499085360 (by norm_num)).trans hd)
      have g44695037407 := b1 44695037407 prime_44695037407 1688970022366499085361 g1688970022366499085361 (by norm_num)
      have g439404181 := b1 439404181 prime_439404181 1688970022366499085361 g1688970022366499085361 (by norm_num)
      exact a3 7 44695037407 g44695037407 439404181 g439404181 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 24 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 499
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 225 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 314 506 425 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)

theorem zs2_500 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 500 ≤ z) (hi : z < 600)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 503
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 134 38 288 (by norm_num)).trans hd)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 179 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 509
    · exfalso; have hd := D8 he
      have g2833 := a7 2833 (by norm_num) ((d8 1278 1476 2832 (by norm_num)).trans hd)
      have g109 := a1 109 2833 g2833 (by norm_num)
      have g11 := a1 11 109 g109 (by norm_num)
      have g5 := a1 5 109 g109 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 521
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g307201 := a7 307201 (by norm_num) ((d16 271441 207038 56311 307200 (by norm_num)).trans hd)
      have g21943 := a1 21943 307201 g307201 (by norm_num)
      have g13 := a1 13 21943 g21943 (by norm_num)
      exact a3 7 13 g13 307201 g307201 (by norm_num)
    · exfalso; have hd := D32 he
      have g34369 := a7 34369 (by norm_num) ((d32 30858 23019 7488 14305 34368 (by norm_num)).trans hd)
      have g491 := a1 491 34369 g34369 (by norm_num)
      have g5 := a1 5 34369 g34369 (by norm_num)
      exact a3 3 491 g491 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 523
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 69 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g1460033 := a7 1460033 (by norm_num) ((d32 273529 182789 423349 944952 1460032 (by norm_num)).trans hd)
      exact a6 3 1460033 g1460033 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 541
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := a7 929 (by norm_num) ((d16 46 258 605 928 (by norm_num)).trans hd)
      have g5 := a1 5 929 g929 (by norm_num)
      exact a3 3 5 g5 929 g929 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 547
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g19009 := a7 19009 (by norm_num) ((d32 14074 3696 11954 7463 19008 (by norm_num)).trans hd)
      have g1901 := a1 1901 19009 g19009 (by norm_num)
      have g5 := a1 5 19009 g19009 (by norm_num)
      exact a3 3 1901 g1901 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 557
    · exfalso; have hd := D8 he
      have g4632458802461936442001 := b7 4632458802461936442001 prime_4632458802461936442001 (by norm_num) ((d8 310249 96254442001 4632458802461936442000 (by norm_num)).trans hd)
      have g37 := a1 37 4632458802461936442001 g4632458802461936442001 (by norm_num)
      exact a3 19 37 g37 4632458802461936442001 g4632458802461936442001 (by norm_num)
    · exfalso; have hd := D16 he
      have g22721 := a7 22721 (by norm_num) ((d16 14876 15557 18878 22720 (by norm_num)).trans hd)
      have g541 := a1 541 22721 g22721 (by norm_num)
      have g271 := a1 271 541 g541 (by norm_num)
      have g17 := a1 17 271 g271 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 439 100 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 563
    · exfalso; have hd := D8 he
      have g31582417313 := b7 31582417313 prime_31582417313 (by norm_num) ((d8 316969 5722095022 31582417312 (by norm_num)).trans hd)
      have g751962317 := b1 751962317 prime_751962317 31582417313 g31582417313 (by norm_num)
      exact a3 3 751962317 g751962317 31582417313 g31582417313 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 70 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g12289 := a7 12289 (by norm_num) ((d32 9744 722 5146 10810 12288 (by norm_num)).trans hd)
      have g1229 := a1 1229 12289 g12289 (by norm_num)
      have g5 := a1 5 12289 g12289 (by norm_num)
      exact a3 3 1229 g1229 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 569
    · exfalso; have hd := D8 he
      have g288529 := a7 288529 (by norm_num) ((d8 35232 42066 288528 (by norm_num)).trans hd)
      have g11 := a1 11 288529 g288529 (by norm_num)
      have g5 := a1 5 288529 g288529 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 60 70 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g495041 := a7 495041 (by norm_num) ((d32 323761 213699 225392 446244 495040 (by norm_num)).trans hd)
      have g82507 := a1 82507 495041 g495041 (by norm_num)
      have g20627 := a1 20627 82507 g82507 (by norm_num)
      exact a6 3 20627 g20627 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 571
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 577
    · exfalso; have hd := D8 he
      have g6142943339981990979841 := b7 6142943339981990979841 prime_6142943339981990979841 (by norm_num) ((d8 332929 110841719041 6142943339981990979840 (by norm_num)).trans hd)
      have g11131 := a1 11131 6142943339981990979841 g6142943339981990979841 (by norm_num)
      exact a6 11 11131 g11131 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := a7 449 (by norm_num) ((d16 220 357 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D32 he
      have g203393 := a7 203393 (by norm_num) ((d32 129536 59582 196695 116744 203392 (by norm_num)).trans hd)
      have g311 := a1 311 203393 g203393 (by norm_num)
      exact a3 3 311 g311 203393 g203393 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 587
    · exfalso; have hd := D8 he
      have g13841 := a7 13841 (by norm_num) ((d8 12385 2263 13840 (by norm_num)).trans hd)
      exact a6 3 13841 g13841 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 189 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 593
    · exfalso; have hd := D8 he
      have g241 := a7 241 (by norm_num) ((d8 30 177 240 (by norm_num)).trans hd)
      exact a6 11 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g635969 := a7 635969 (by norm_num) ((d32 351649 478779 28512 165762 635968 (by norm_num)).trans hd)
      have g5 := a1 5 635969 g635969 (by norm_num)
      exact a3 3 5 g5 635969 g635969 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 599
    · exfalso; have hd := D8 he
      have g1249 := a7 1249 (by norm_num) ((d8 338 585 1248 (by norm_num)).trans hd)
      exact a6 5 1249 g1249 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 14 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)

theorem zs2_600 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 600 ≤ z) (hi : z < 700)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 601
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 70 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g3457 := a7 3457 (by norm_num) ((d32 1673 2216 1716 2749 3456 (by norm_num)).trans hd)
      have g13 := a1 13 3457 g3457 (by norm_num)
      exact a3 7 13 g13 3457 g3457 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 607
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 613
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 44 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g100801 := a7 100801 (by norm_num) ((d32 73366 98959 66531 449 100800 (by norm_num)).trans hd)
      have g3877 := a1 3877 100801 g100801 (by norm_num)
      have g13 := a1 13 100801 g100801 (by norm_num)
      exact a3 7 3877 g3877 13 g13 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 617
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 619
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 33 512 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 631
    · exfalso; have hd := D8 he
      have g304237489 := b7 304237489 prime_304237489 (by norm_num) ((d8 398161 24450152 304237488 (by norm_num)).trans hd)
      have g53 := a1 53 304237489 g304237489 (by norm_num)
      exact a6 3 53 g53 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 100 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 68 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 641
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := a7 1153 (by norm_num) ((d16 413 1078 1013 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 643
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 179 251 288 (by norm_num)).trans hd)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 4 16 256 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 647
    · exfalso; have hd := D8 he
      have g241 := a7 241 (by norm_num) ((d8 233 64 240 (by norm_num)).trans hd)
      exact a6 11 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 304 283 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 185 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 653
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 134 38 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g165857 := a7 165857 (by norm_num) ((d16 94695 84320 70381 165856 (by norm_num)).trans hd)
      have g11 := a1 11 165857 g165857 (by norm_num)
      exact a3 3 11 g11 165857 g165857 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 72 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 659
    · exfalso; have hd := D8 he
      have g79537 := a7 79537 (by norm_num) ((d8 36596 23210 79536 (by norm_num)).trans hd)
      have g39769 := a1 39769 79537 g79537 (by norm_num)
      have g41 := a1 41 39769 g39769 (by norm_num)
      have g5 := a1 5 39769 g39769 (by norm_num)
      exact a3 3 41 g41 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g50753 := a7 50753 (by norm_num) ((d32 28257 11853 9305 49160 50752 (by norm_num)).trans hd)
      have g11 := a1 11 50753 g50753 (by norm_num)
      exact a3 3 11 g11 50753 g50753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 661
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 400 391 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 673
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g15937 := a7 15937 (by norm_num) ((d16 6693 13279 4873 15936 (by norm_num)).trans hd)
      have g613 := a1 613 15937 g15937 (by norm_num)
      have g307 := a1 307 613 g613 (by norm_num)
      have g13 := a1 13 15937 g15937 (by norm_num)
      exact a3 7 307 g307 13 g13 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 151 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 677
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := a7 449 (by norm_num) ((d16 349 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 588 997 123 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 683
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g58049 := a7 58049 (by norm_num) ((d16 2097 43734 6255 58048 (by norm_num)).trans hd)
      exact a6 3 58049 g58049 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 8 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 691
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 577 250 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)

theorem zs2_700 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 700 ≤ z) (hi : z < 800)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 701
    · exfalso; have hd := D8 he
      have g7592718929 := b7 7592718929 prime_7592718929 (by norm_num) ((d8 491401 6100656002 7592718928 (by norm_num)).trans hd)
      have g5 := a1 5 7592718929 g7592718929 (by norm_num)
      exact a3 3 5 g5 7592718929 g7592718929 (by norm_num)
    · exfalso; have hd := D16 he
      have g929 := a7 929 (by norm_num) ((d16 889 671 605 928 (by norm_num)).trans hd)
      have g5 := a1 5 929 g929 (by norm_num)
      exact a3 3 5 g5 929 g929 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 23 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 709
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 110 251 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 719
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g28289 := a7 28289 (by norm_num) ((d32 7759 3089 8528 24054 28288 (by norm_num)).trans hd)
      have g5 := a1 5 28289 g28289 (by norm_num)
      exact a3 3 5 g5 28289 g28289 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 727
    · exfalso; have hd := D8 he
      have g32103713 := a7 32103713 (by norm_num) ((d8 528529 8497028 32103712 (by norm_num)).trans hd)
      have g124433 := a1 124433 32103713 g32103713 (by norm_num)
      exact a6 3 124433 g124433 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 137 8 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 733
    · exfalso; have hd := D8 he
      have g337 := a7 337 (by norm_num) ((d8 111 189 336 (by norm_num)).trans hd)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g32993 := a7 32993 (by norm_num) ((d16 9401 23547 13844 32992 (by norm_num)).trans hd)
      exact a6 3 32993 g32993 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 170 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 739
    · exfalso; have hd := D8 he
      have g257 := a7 257 (by norm_num) ((d8 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 124 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 743
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 69 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 751
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g35201 := a7 35201 (by norm_num) ((d32 785 17808 34256 13000 35200 (by norm_num)).trans hd)
      have g5867 := a1 5867 35201 g35201 (by norm_num)
      exact a6 3 5867 g5867 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 757
    · exfalso; have hd := D8 he
      have g673 := a7 673 (by norm_num) ((d8 326 615 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 70 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 144 742 729 62 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 761
    · exfalso; have hd := D8 he
      have g54049 := a7 54049 (by norm_num) ((d8 38631 7222 54048 (by norm_num)).trans hd)
      exact a6 5 54049 g54049 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 121 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 769
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 359 40 318 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 773
    · exfalso; have hd := D8 he
      have g257 := a7 257 (by norm_num) ((d8 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 253 116 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g1601 := a7 1601 (by norm_num) ((d32 356 257 408 1561 1600 (by norm_num)).trans hd)
      exact a6 3 1601 g1601 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 787
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := a7 673 (by norm_num) ((d16 209 609 58 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 797
    · exfalso; have hd := D8 he
      have g258426017 := b7 258426017 prime_258426017 (by norm_num) ((d8 635209 87461144 258426016 (by norm_num)).trans hd)
      exact a6 3 258426017 g258426017 (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := a7 3329 (by norm_num) ((d16 2699 749 1729 3328 (by norm_num)).trans hd)
      exact a6 3 3329 g3329 (by norm_num)
    · exfalso; have hd := D32 he
      have g22721 := a7 22721 (by norm_num) ((d32 21742 4159 6600 3843 22720 (by norm_num)).trans hd)
      have g541 := a1 541 22721 g22721 (by norm_num)
      have g271 := a1 271 541 g541 (by norm_num)
      have g17 := a1 17 271 g271 (by norm_num)
      exact a6 3 17 g17 (by norm_num)

theorem zs2_800 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 800 ≤ z) (hi : z < 900)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 809
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g118273 := a7 118273 (by norm_num) ((d16 63116 76543 59521 118272 (by norm_num)).trans hd)
      have g4549 := a1 4549 118273 g118273 (by norm_num)
      exact a6 5 4549 g4549 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 163 27 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 811
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 170 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 821
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g3329 := a7 3329 (by norm_num) ((d32 1583 2481 40 1600 3328 (by norm_num)).trans hd)
      exact a6 3 3329 g3329 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 823
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g18401 := a7 18401 (by norm_num) ((d16 14893 14196 17065 18400 (by norm_num)).trans hd)
      have g3067 := a1 3067 18401 g18401 (by norm_num)
      have g59 := a1 59 3067 g3067 (by norm_num)
      exact a3 3 59 g59 18401 g18401 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 677 737 387 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 827
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 155 38 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 102 77 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 829
    · exfalso; have hd := D8 he
      have g5025697 := a7 5025697 (by norm_num) ((d8 687241 265112 5025696 (by norm_num)).trans hd)
      have g167 := a1 167 5025697 g5025697 (by norm_num)
      have g41 := a1 41 5025697 g5025697 (by norm_num)
      exact a3 3 167 g167 41 g41 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 839
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 853
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g340801 := a7 340801 (by norm_num) ((d32 46007 269839 270669 57392 340800 (by norm_num)).trans hd)
      have g2213 := a1 2213 340801 g340801 (by norm_num)
      exact a6 3 2213 g2213 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 857
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g73121 := a7 73121 (by norm_num) ((d16 3239 34818 20065 73120 (by norm_num)).trans hd)
      have g1741 := a1 1741 73121 g73121 (by norm_num)
      have g13 := a1 13 1741 g1741 (by norm_num)
      exact a3 7 13 g13 73121 g73121 (by norm_num)
    · exfalso; have hd := D32 he
      have g13249 := a7 13249 (by norm_num) ((d32 5754 12514 10265 928 13248 (by norm_num)).trans hd)
      exact a6 5 13249 g13249 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 859
    · exfalso; have hd := D8 he
      have g148222903052887857582961 := b7 148222903052887857582961 prime_148222903052887857582961 (by norm_num) ((d8 737881 544468370161 148222903052887857582960 (by norm_num)).trans hd)
      have g5844802782997 := b1 5844802782997 prime_5844802782997 148222903052887857582961 g148222903052887857582961 (by norm_num)
      exact a3 31 5844802782997 g5844802782997 148222903052887857582961 g148222903052887857582961 (by norm_num)
    · exfalso; have hd := D16 he
      have g527489 := a7 527489 (by norm_num) ((d16 210392 26740 280005 527488 (by norm_num)).trans hd)
      exact a6 3 527489 g527489 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 42 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 863
    · exfalso; have hd := D8 he
      have g449 := a7 449 (by norm_num) ((d8 327 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D16 he
      have g1617697 := a7 1617697 (by norm_num) ((d16 744769 62910 781238 1617696 (by norm_num)).trans hd)
      have g42571 := a1 42571 1617697 g1617697 (by norm_num)
      have g29 := a1 29 42571 g42571 (by norm_num)
      have g19 := a1 19 1617697 g1617697 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 29 g29 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 240 32 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 877
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 24 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 881
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g614177 := a7 614177 (by norm_num) ((d16 161984 560639 567562 614176 (by norm_num)).trans hd)
      exact a6 3 614177 g614177 (by norm_num)
    · exfalso; have hd := D32 he
      have g1269953 := a7 1269953 (by norm_num) ((d32 776161 833217 282767 935409 1269952 (by norm_num)).trans hd)
      exact a6 3 1269953 g1269953 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 883
    · exfalso; have hd := D8 he
      have g929 := a7 929 (by norm_num) ((d8 258 605 928 (by norm_num)).trans hd)
      have g5 := a1 5 929 g929 (by norm_num)
      exact a3 3 5 g5 929 g929 (by norm_num)
    · exfalso; have hd := D16 he
      have g10529 := a7 10529 (by norm_num) ((d16 543 37 1369 10528 (by norm_num)).trans hd)
      exact a6 3 10529 g10529 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 887
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g1093249 := a7 1093249 (by norm_num) ((d32 786769 222818 144287 1090911 1093248 (by norm_num)).trans hd)
      exact a6 5 1093249 g1093249 (by norm_num)

theorem zs2_900 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 900 ≤ z) (hi : z < 1000)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 907
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 155 38 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 911
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g25121 := a7 25121 (by norm_num) ((d16 928 7070 19231 25120 (by norm_num)).trans hd)
      have g53 := a1 53 25121 g25121 (by norm_num)
      exact a6 3 53 g53 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 68 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 919
    · exfalso; have hd := D8 he
      have g2142577 := a7 2142577 (by norm_num) ((d8 844561 116228 2142576 (by norm_num)).trans hd)
      have g17 := a1 17 2142577 g2142577 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 565 997 123 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 929
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g2689 := a7 2689 (by norm_num) ((d32 2561 250 653 1547 2688 (by norm_num)).trans hd)
      have g269 := a1 269 2689 g2689 (by norm_num)
      exact a6 3 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 937
    · exfalso; have hd := D8 he
      have g7537 := a7 7537 (by norm_num) ((d8 3677 6488 7536 (by norm_num)).trans hd)
      have g3769 := a1 3769 7537 g7537 (by norm_num)
      have g29 := a1 29 3769 g3769 (by norm_num)
      have g5 := a1 5 3769 g3769 (by norm_num)
      exact a3 3 29 g29 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g5441 := a7 5441 (by norm_num) ((d32 1968 4473 1172 2452 5440 (by norm_num)).trans hd)
      have g907 := a1 907 5441 g5441 (by norm_num)
      have g227 := a1 227 907 g907 (by norm_num)
      exact a3 3 227 g227 5441 g5441 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 941
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 947
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g12161 := a7 12161 (by norm_num) ((d16 9056 9513 7168 12160 (by norm_num)).trans hd)
      have g2027 := a1 2027 12161 g12161 (by norm_num)
      exact a3 3 2027 g2027 12161 g12161 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 136 249 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 953
    · exfalso; have hd := D8 he
      have g14177 := a7 14177 (by norm_num) ((d8 881 10603 14176 (by norm_num)).trans hd)
      have g17 := a1 17 14177 g14177 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 293 70 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g37889 := a7 37889 (by norm_num) ((d32 36762 19792 26782 36754 37888 (by norm_num)).trans hd)
      exact a6 3 37889 g37889 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 967
    · exfalso; have hd := D8 he
      have g10529 := a7 10529 (by norm_num) ((d8 8537 9160 10528 (by norm_num)).trans hd)
      exact a6 3 10529 g10529 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 971
    · exfalso; have hd := D8 he
      have g337 := a7 337 (by norm_num) ((d8 252 148 336 (by norm_num)).trans hd)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D16 he
      have g14657 := a7 14657 (by norm_num) ((d16 4793 5330 3634 14656 (by norm_num)).trans hd)
      have g349 := a1 349 14657 g14657 (by norm_num)
      exact a6 5 349 g349 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 977
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 18 98 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := a7 577 (by norm_num) ((d16 171 391 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 404 229 357 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 983
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g5441 := a7 5441 (by norm_num) ((d16 3232 4545 2989 5440 (by norm_num)).trans hd)
      have g907 := a1 907 5441 g5441 (by norm_num)
      have g227 := a1 227 907 g907 (by norm_num)
      exact a3 3 227 g227 5441 g5441 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 991
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := a7 577 (by norm_num) ((d16 27 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 997
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := a7 449 (by norm_num) ((d16 372 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D32 he
      have g45697 := a7 45697 (by norm_num) ((d32 34372 29843 15816 478 45696 (by norm_num)).trans hd)
      have g313 := a1 313 45697 g45697 (by norm_num)
      have g157 := a1 157 313 g313 (by norm_num)
      have g79 := a1 79 157 g157 (by norm_num)
      have g73 := a1 73 45697 g45697 (by norm_num)
      have g37 := a1 37 73 g73 (by norm_num)
      have g19 := a1 19 37 g37 (by norm_num)
      exact a3 5 79 g79 19 g19 (by norm_num)

theorem zs2_1000 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1000 ≤ z) (hi : z < 1100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1009
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g36929 := a7 36929 (by norm_num) ((d16 20998 20673 30541 36928 (by norm_num)).trans hd)
      have g5 := a1 5 36929 g36929 (by norm_num)
      exact a3 3 5 g5 36929 g36929 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1013
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 225 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 263 506 425 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1019
    · exfalso; have hd := D8 he
      have g1409 := a7 1409 (by norm_num) ((d8 1337 957 1408 (by norm_num)).trans hd)
      have g5 := a1 5 1409 g1409 (by norm_num)
      exact a3 3 5 g5 1409 g1409 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g62401 := a7 62401 (by norm_num) ((d32 39945 9455 38793 34333 62400 (by norm_num)).trans hd)
      have g761 := a1 761 62401 g62401 (by norm_num)
      have g41 := a1 41 62401 g62401 (by norm_num)
      exact a3 3 761 g761 41 g41 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1021
    · exfalso; have hd := D8 he
      have g590440230397776959593681 := b7 590440230397776959593681 prime_590440230397776959593681 (by norm_num) ((d8 1042441 1086683238481 590440230397776959593680 (by norm_num)).trans hd)
      have g3331 := a1 3331 590440230397776959593681 g590440230397776959593681 (by norm_num)
      exact a6 7 3331 g3331 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1031
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3361 := a7 3361 (by norm_num) ((d16 885 112 2461 3360 (by norm_num)).trans hd)
      exact a6 41 3361 g3361 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 127 550 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1033
    · exfalso; have hd := D8 he
      have g860113 := a7 860113 (by norm_num) ((d8 206976 276498 860112 (by norm_num)).trans hd)
      have g430057 := a1 430057 860113 g860113 (by norm_num)
      have g2129 := a1 2129 430057 g430057 (by norm_num)
      have g101 := a1 101 430057 g430057 (by norm_num)
      exact a3 3 2129 g2129 101 g101 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 185 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1039
    · exfalso; have hd := D8 he
      have g41809 := a7 41809 (by norm_num) ((d8 34296 3019 41808 (by norm_num)).trans hd)
      have g113 := a1 113 41809 g41809 (by norm_num)
      have g5 := a1 5 41809 g41809 (by norm_num)
      exact a3 3 113 g113 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 72 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1049
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 100 116 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 439 170 75 1013 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1051
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g20129 := a7 20129 (by norm_num) ((d16 17635 175 10496 20128 (by norm_num)).trans hd)
      have g5 := a1 5 20129 g20129 (by norm_num)
      exact a3 3 5 g5 20129 g20129 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 15 225 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1061
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g16993 := a7 16993 (by norm_num) ((d16 4183 11692 11172 16992 (by norm_num)).trans hd)
      have g293 := a1 293 16993 g16993 (by norm_num)
      have g29 := a1 29 16993 g16993 (by norm_num)
      exact a3 3 293 g293 29 g29 (by norm_num)
    · exfalso; have hd := D32 he
      have g2689 := a7 2689 (by norm_num) ((d32 1719 2439 653 1547 2688 (by norm_num)).trans hd)
      have g269 := a1 269 2689 g2689 (by norm_num)
      exact a6 3 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1063
    · exfalso; have hd := D8 he
      have g4507537 := a7 4507537 (by norm_num) ((d8 1129969 2472656 4507536 (by norm_num)).trans hd)
      have g811 := a1 811 4507537 g4507537 (by norm_num)
      exact a3 7 811 g811 4507537 g4507537 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 197 2 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1069
    · exfalso; have hd := D8 he
      have g37303841 := a7 37303841 (by norm_num) ((d8 1142761 7141234 37303840 (by norm_num)).trans hd)
      have g6217307 := a1 6217307 37303841 g37303841 (by norm_num)
      exact a6 3 6217307 g6217307 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 100 116 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 8 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1087
    · exfalso; have hd := D8 he
      have g243553 := a7 243553 (by norm_num) ((d8 207357 78829 243552 (by norm_num)).trans hd)
      have g2591 := a1 2591 243553 g243553 (by norm_num)
      exact a6 3 2591 g2591 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 23 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1091
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 179 251 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g30593 := a7 30593 (by norm_num) ((d32 27747 23164 269 11175 30592 (by norm_num)).trans hd)
      have g5099 := a1 5099 30593 g30593 (by norm_num)
      exact a3 3 5099 g5099 30593 g30593 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1093
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := a7 2081 (by norm_num) ((d16 155 1134 1979 2080 (by norm_num)).trans hd)
      have g347 := a1 347 2081 g2081 (by norm_num)
      exact a3 3 347 g347 2081 g2081 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 392 633 40 62 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1097
    · exfalso; have hd := D8 he
      have g236993 := a7 236993 (by norm_num) ((d8 18444 96181 236992 (by norm_num)).trans hd)
      have g39499 := a1 39499 236993 g236993 (by norm_num)
      exact a6 5 39499 g39499 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g27073 := a7 27073 (by norm_num) ((d32 12197 674 21108 7303 27072 (by norm_num)).trans hd)
      have g13537 := a1 13537 27073 g27073 (by norm_num)
      have g967 := a1 967 13537 g13537 (by norm_num)
      exact a6 11 967 g967 (by norm_num)

theorem zs2_1100 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1100 ≤ z) (hi : z < 1200)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1103
    · exfalso; have hd := D8 he
      have g1095403448591351982886081 := b7 1095403448591351982886081 prime_1095403448591351982886081 (by norm_num) ((d8 1216609 1480137458881 1095403448591351982886080 (by norm_num)).trans hd)
      have g28069 := a1 28069 1095403448591351982886081 g1095403448591351982886081 (by norm_num)
      have g3889 := a1 3889 1095403448591351982886081 g1095403448591351982886081 (by norm_num)
      exact a3 5 28069 g28069 3889 g3889 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g1153 := a7 1153 (by norm_num) ((d32 194 740 1078 1013 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1109
    · exfalso; have hd := D8 he
      have g18295290017 := b7 18295290017 prime_18295290017 (by norm_num) ((d8 1229881 12393492767 18295290016 (by norm_num)).trans hd)
      exact a6 3 18295290017 g18295290017 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 136 249 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1117
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g13921 := a7 13921 (by norm_num) ((d16 8720 1898 10786 13920 (by norm_num)).trans hd)
      have g6961 := a1 6961 13921 g13921 (by norm_num)
      exact a6 59 6961 g6961 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 215 65 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1123
    · exfalso; have hd := D8 he
      have g3169 := a7 3169 (by norm_num) ((d8 3036 1844 3168 (by norm_num)).trans hd)
      have g317 := a1 317 3169 g3169 (by norm_num)
      have g5 := a1 5 3169 g3169 (by norm_num)
      exact a3 3 317 g317 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g340321 := a7 340321 (by norm_num) ((d16 240166 62550 172284 340320 (by norm_num)).trans hd)
      have g647 := a1 647 340321 g340321 (by norm_num)
      exact a6 3 647 g647 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 67 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1129
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4673 := a7 4673 (by norm_num) ((d16 3585 1475 2680 4672 (by norm_num)).trans hd)
      have g41 := a1 41 4673 g4673 (by norm_num)
      exact a3 3 41 g41 4673 g4673 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 69 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1151
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 223 128 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1153
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4289 := a7 4289 (by norm_num) ((d16 4108 2738 3761 4288 (by norm_num)).trans hd)
      have g5 := a1 5 4289 g4289 (by norm_num)
      exact a3 3 5 g5 4289 g4289 (by norm_num)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 616 625 256 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1163
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := a7 673 (by norm_num) ((d16 512 347 615 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1171
    · exfalso; have hd := D8 he
      have g305521 := a7 305521 (by norm_num) ((d8 149157 76950 305520 (by norm_num)).trans hd)
      have g139 := a1 139 305521 g305521 (by norm_num)
      exact a3 7 139 g139 305521 g305521 (by norm_num)
    · exfalso; have hd := D16 he
      have g280129 := a7 280129 (by norm_num) ((d16 250725 117122 206012 280128 (by norm_num)).trans hd)
      have g109 := a1 109 280129 g280129 (by norm_num)
      exact a3 5 109 g109 280129 g280129 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 169 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1181
    · exfalso; have hd := D8 he
      have g577 := a7 577 (by norm_num) ((d8 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1187
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g577 := a7 577 (by norm_num) ((d16 512 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 69 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1193
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := a7 2081 (by norm_num) ((d16 1926 1134 1979 2080 (by norm_num)).trans hd)
      have g347 := a1 347 2081 g2081 (by norm_num)
      exact a3 3 347 g347 2081 g2081 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 67 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)

theorem zs2_1200 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1200 ≤ z) (hi : z < 1300)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1201
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1213
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1217
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1223
    · exfalso; have hd := D8 he
      have g297457729 := b7 297457729 prime_297457729 (by norm_num) ((d8 1495729 25661632 297457728 (by norm_num)).trans hd)
      have g19 := a1 19 297457729 g297457729 (by norm_num)
      exact a3 5 19 g19 297457729 g297457729 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1229
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 23 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1231
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 134 38 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1237
    · exfalso; have hd := D8 he
      have g138059635409 := b7 138059635409 prime_138059635409 (by norm_num) ((d8 1530169 132463002017 138059635408 (by norm_num)).trans hd)
      exact a6 3 138059635409 g138059635409 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 542 71 425 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1249
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 469 27 729 62 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1259
    · exfalso; have hd := D8 he
      have g4225841 := a7 4225841 (by norm_num) ((d8 1585081 3784170 4225840 (by norm_num)).trans hd)
      exact a6 3 4225841 g4225841 (by norm_num)
    · exfalso; have hd := D16 he
      have g16417 := a7 16417 (by norm_num) ((d16 9049 12822 3846 16416 (by norm_num)).trans hd)
      have g8209 := a1 8209 16417 g16417 (by norm_num)
      have g821 := a1 821 8209 g8209 (by norm_num)
      have g5 := a1 5 8209 g8209 (by norm_num)
      exact a3 3 821 g821 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g20353 := a7 20353 (by norm_num) ((d32 17900 13074 4982 10017 20352 (by norm_num)).trans hd)
      have g10177 := a1 10177 20353 g20353 (by norm_num)
      have g727 := a1 727 10177 g10177 (by norm_num)
      exact a3 7 727 g727 10177 g10177 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1277
    · exfalso; have hd := D8 he
      have g257 := a7 257 (by norm_num) ((d8 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 72 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1279
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1283
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 18 98 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g27361 := a7 27361 (by norm_num) ((d16 4429 25565 24379 27360 (by norm_num)).trans hd)
      have g13681 := a1 13681 27361 g27361 (by norm_num)
      have g6841 := a1 6841 13681 g13681 (by norm_num)
      have g311 := a1 311 6841 g6841 (by norm_num)
      have g11 := a1 11 6841 g6841 (by norm_num)
      exact a3 3 311 g311 11 g11 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 185 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1289
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 221 349 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1291
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 44 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 126 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1297
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

theorem zs2_1300 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1300 ≤ z) (hi : z < 1400)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1301
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g522881 := a7 522881 (by norm_num) ((d32 123958 204698 202269 447397 522880 (by norm_num)).trans hd)
      exact a6 3 522881 g522881 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1303
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1307
    · exfalso; have hd := D8 he
      have g4257696543602770772646001 := b7 4257696543602770772646001 prime_4257696543602770772646001 (by norm_num) ((d8 1708249 2918114646001 4257696543602770772646000 (by norm_num)).trans hd)
      have g57679 := a1 57679 4257696543602770772646001 g4257696543602770772646001 (by norm_num)
      exact a3 7 57679 g57679 4257696543602770772646001 g4257696543602770772646001 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 227 129 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1319
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 128 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1321
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g871553 := a7 871553 (by norm_num) ((d32 1935 258013 618476 152618 871552 (by norm_num)).trans hd)
      have g145259 := a1 145259 871553 g871553 (by norm_num)
      exact a6 3 145259 g145259 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1327
    · exfalso; have hd := D8 he
      have g611380753 := b7 611380753 prime_611380753 (by norm_num) ((d8 1760929 559144578 611380752 (by norm_num)).trans hd)
      have g305690377 := b1 305690377 prime_305690377 611380753 g611380753 (by norm_num)
      have g443 := a1 443 305690377 g305690377 (by norm_num)
      have g23 := a1 23 305690377 g305690377 (by norm_num)
      exact a3 3 443 g443 23 g23 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1361
    · exfalso; have hd := D8 he
      have g1638724289 := b7 1638724289 prime_1638724289 (by norm_num) ((d8 1852321 1243150164 1638724288 (by norm_num)).trans hd)
      have g5 := a1 5 1638724289 g1638724289 (by norm_num)
      exact a3 3 5 g5 1638724289 g1638724289 (by norm_num)
    · exfalso; have hd := D16 he
      have g291457 := a7 291457 (by norm_num) ((d16 103579 77071 45381 291456 (by norm_num)).trans hd)
      have g2389 := a1 2389 291457 g291457 (by norm_num)
      have g239 := a1 239 2389 g2389 (by norm_num)
      have g5 := a1 5 2389 g2389 (by norm_num)
      exact a3 3 239 g239 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1367
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2753 := a7 2753 (by norm_num) ((d16 2155 2467 1959 2752 (by norm_num)).trans hd)
      exact a6 3 2753 g2753 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1373
    · exfalso; have hd := D8 he
      have g1249 := a7 1249 (by norm_num) ((d8 388 664 1248 (by norm_num)).trans hd)
      exact a6 5 1249 g1249 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 34 128 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1381
    · exfalso; have hd := D8 he
      have g8849 := a7 8849 (by norm_num) ((d8 4626 2994 8848 (by norm_num)).trans hd)
      exact a6 5 8849 g8849 (by norm_num)
    · exfalso; have hd := D16 he
      have g25409 := a7 25409 (by norm_num) ((d16 1486 23022 6153 25408 (by norm_num)).trans hd)
      exact a6 11 25409 g25409 (by norm_num)
    · exfalso; have hd := D32 he
      have g114113 := a7 114113 (by norm_num) ((d32 81353 98948 39530 71591 114112 (by norm_num)).trans hd)
      have g11 := a1 11 114113 g114113 (by norm_num)
      exact a3 3 11 g11 114113 g114113 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1399
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1409 := a7 1409 (by norm_num) ((d16 100 137 452 1408 (by norm_num)).trans hd)
      have g5 := a1 5 1409 g1409 (by norm_num)
      exact a3 3 5 g5 1409 g1409 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 10 100 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)

theorem zs2_1400 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1400 ≤ z) (hi : z < 1500)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1409
    · exfalso; have hd := D8 he
      have g38833 := a7 38833 (by norm_num) ((d8 4798 31668 38832 (by norm_num)).trans hd)
      have g19417 := a1 19417 38833 g38833 (by norm_num)
      have g73 := a1 73 19417 g19417 (by norm_num)
      have g37 := a1 37 73 g73 (by norm_num)
      exact a3 19 37 g37 19417 g19417 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g11969 := a7 11969 (by norm_num) ((d32 10396 8715 7920 8840 11968 (by norm_num)).trans hd)
      exact a6 3 11969 g11969 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1423
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 10 100 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1427
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 69 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 179 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1429
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 18 98 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g192833 := a7 192833 (by norm_num) ((d16 113711 160372 77009 192832 (by norm_num)).trans hd)
      exact a6 3 192833 g192833 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1433
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g158209 := a7 158209 (by norm_num) ((d16 154981 136399 99846 158208 (by norm_num)).trans hd)
      have g1217 := a1 1217 158209 g158209 (by norm_num)
      have g5 := a1 5 158209 g158209 (by norm_num)
      exact a3 3 1217 g1217 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g14657 := a7 14657 (by norm_num) ((d32 1509 5246 9327 3634 14656 (by norm_num)).trans hd)
      have g349 := a1 349 14657 g14657 (by norm_num)
      exact a6 5 349 g349 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1439
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := a7 1153 (by norm_num) ((d16 1086 1030 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 24 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1447
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g11777 := a7 11777 (by norm_num) ((d16 9280 4976 5322 11776 (by norm_num)).trans hd)
      have g151 := a1 151 11777 g11777 (by norm_num)
      have g19 := a1 19 151 g151 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 11777 g11777 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 30 129 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1451
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g102433 := a7 102433 (by norm_num) ((d16 56741 71891 58866 102432 (by norm_num)).trans hd)
      have g51217 := a1 51217 102433 g102433 (by norm_num)
      have g25609 := a1 25609 51217 g51217 (by norm_num)
      have g197 := a1 197 25609 g25609 (by norm_num)
      exact a6 3 197 g197 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1453
    · exfalso; have hd := D8 he
      have g319489 := a7 319489 (by norm_num) ((d8 194275 262099 319488 (by norm_num)).trans hd)
      have g743 := a1 743 319489 g319489 (by norm_num)
      have g5 := a1 5 319489 g319489 (by norm_num)
      exact a3 3 743 g743 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := a7 673 (by norm_num) ((d16 8 64 58 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 304 136 40 62 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1459
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g20897 := a7 20897 (by norm_num) ((d16 18084 13903 17056 20896 (by norm_num)).trans hd)
      exact a6 3 20897 g20897 (by norm_num)
    · exfalso; have hd := D32 he
      have g15937 := a7 15937 (by norm_num) ((d32 9060 8050 2658 4873 15936 (by norm_num)).trans hd)
      have g613 := a1 613 15937 g15937 (by norm_num)
      have g307 := a1 307 613 g613 (by norm_num)
      have g13 := a1 13 15937 g15937 (by norm_num)
      exact a3 7 307 g307 13 g13 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1471
    · exfalso; have hd := D8 he
      have g401 := a7 401 (by norm_num) ((d8 45 20 400 (by norm_num)).trans hd)
      have g67 := a1 67 401 g401 (by norm_num)
      have g17 := a1 17 67 g67 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 304 283 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g6529 := a7 6529 (by norm_num) ((d32 2742 3685 5434 4218 6528 (by norm_num)).trans hd)
      have g653 := a1 653 6529 g6529 (by norm_num)
      have g5 := a1 5 6529 g6529 (by norm_num)
      exact a3 3 653 g653 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1481
    · exfalso; have hd := D8 he
      have g769 := a7 769 (by norm_num) ((d8 173 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g1697 := a7 1697 (by norm_num) ((d16 837 1405 414 1696 (by norm_num)).trans hd)
      have g283 := a1 283 1697 g1697 (by norm_num)
      have g71 := a1 71 283 g283 (by norm_num)
      exact a6 3 71 g71 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1483
    · exfalso; have hd := D8 he
      have g607697 := a7 607697 (by norm_num) ((d8 376198 203965 607696 (by norm_num)).trans hd)
      exact a6 3 607697 g607697 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1487
    · exfalso; have hd := D8 he
      have g1297 := a7 1297 (by norm_num) ((d8 1081 1261 1296 (by norm_num)).trans hd)
      have g59 := a1 59 1297 g1297 (by norm_num)
      have g11 := a1 11 1297 g1297 (by norm_num)
      exact a3 3 59 g59 11 g11 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g5953 := a7 5953 (by norm_num) ((d32 2606 4816 968 2403 5952 (by norm_num)).trans hd)
      have g229 := a1 229 5953 g5953 (by norm_num)
      have g23 := a1 23 229 g229 (by norm_num)
      have g5 := a1 5 229 g229 (by norm_num)
      exact a3 3 23 g23 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1489
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1493
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2273 := a7 2273 (by norm_num) ((d16 1509 1808 290 2272 (by norm_num)).trans hd)
      have g379 := a1 379 2273 g2273 (by norm_num)
      have g5 := a1 5 379 g379 (by norm_num)
      exact a3 3 5 g5 2273 g2273 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1499
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g273569 := a7 273569 (by norm_num) ((d16 58449 229498 186710 273568 (by norm_num)).trans hd)
      have g5 := a1 5 273569 g273569 (by norm_num)
      exact a3 3 5 g5 273569 g273569 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 163 27 152 24 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)

theorem zs2_1500 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1500 ≤ z) (hi : z < 1600)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1511
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 69 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 124 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1523
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 391 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D32 he
      have g14657 := a7 14657 (by norm_num) ((d32 3723 9864 5330 3634 14656 (by norm_num)).trans hd)
      have g349 := a1 349 14657 g14657 (by norm_num)
      exact a6 5 349 g349 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1531
    · exfalso; have hd := D8 he
      have g15092859525078825081684721 := b7 15092859525078825081684721 prime_15092859525078825081684721 (by norm_num) ((d8 2343961 5494153169521 15092859525078825081684720 (by norm_num)).trans hd)
      have g1571511860719 := b1 1571511860719 prime_1571511860719 15092859525078825081684721 g15092859525078825081684721 (by norm_num)
      have g686002709617 := b1 686002709617 prime_686002709617 15092859525078825081684721 g15092859525078825081684721 (by norm_num)
      exact a3 23 1571511860719 g1571511860719 686002709617 g686002709617 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 169 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1543
    · exfalso; have hd := D8 he
      have g9041 := a7 9041 (by norm_num) ((d8 3066 6757 9040 (by norm_num)).trans hd)
      have g11 := a1 11 9041 g9041 (by norm_num)
      exact a3 3 11 g11 9041 g9041 (by norm_num)
    · exfalso; have hd := D16 he
      have g128257 := a7 128257 (by norm_num) ((d16 72223 77796 26300 128256 (by norm_num)).trans hd)
      have g4933 := a1 4933 128257 g128257 (by norm_num)
      have g2467 := a1 2467 4933 g4933 (by norm_num)
      have g617 := a1 617 2467 g2467 (by norm_num)
      have g103 := a1 103 617 g617 (by norm_num)
      exact a3 13 103 g103 128257 g128257 (by norm_num)
    · exfalso; have hd := D32 he
      have g2753 := a7 2753 (by norm_num) ((d32 2257 999 1415 794 2752 (by norm_num)).trans hd)
      exact a6 3 2753 g2753 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1549
    · exfalso; have hd := D8 he
      have g19841 := a7 19841 (by norm_num) ((d8 18481 4387 19840 (by norm_num)).trans hd)
      have g3307 := a1 3307 19841 g19841 (by norm_num)
      have g827 := a1 827 3307 g3307 (by norm_num)
      exact a6 3 827 g827 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 60 70 311 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1553
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 121 249 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1559
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 32 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1567
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1571
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 70 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g22721 := a7 22721 (by norm_num) ((d32 14173 20289 7164 18878 22720 (by norm_num)).trans hd)
      have g541 := a1 541 22721 g22721 (by norm_num)
      have g271 := a1 271 541 g541 (by norm_num)
      have g17 := a1 17 271 g271 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1579
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 67 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1583
    · exfalso; have hd := D8 he
      have g97154822801 := b7 97154822801 prime_97154822801 (by norm_num) ((d8 2505889 61571021057 97154822800 (by norm_num)).trans hd)
      have g167 := a1 167 97154822801 g97154822801 (by norm_num)
      exact a3 3 167 g167 97154822801 g97154822801 (by norm_num)
    · exfalso; have hd := D16 he
      have g3329 := a7 3329 (by norm_num) ((d16 2481 40 1600 3328 (by norm_num)).trans hd)
      exact a6 3 3329 g3329 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 170 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1597
    · exfalso; have hd := D8 he
      have g977 := a7 977 (by norm_num) ((d8 439 252 976 (by norm_num)).trans hd)
      have g163 := a1 163 977 g977 (by norm_num)
      have g41 := a1 41 163 g163 (by norm_num)
      exact a3 3 41 g41 977 g977 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g11969 := a7 11969 (by norm_num) ((d32 1012 6779 5850 3129 11968 (by norm_num)).trans hd)
      exact a6 3 11969 g11969 (by norm_num)

theorem zs2_1600 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1600 ≤ z) (hi : z < 1700)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1601
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g3617 := a7 3617 (by norm_num) ((d16 2365 1343 2383 3616 (by norm_num)).trans hd)
      exact a6 3 3617 g3617 (by norm_num)
    · exfalso; have hd := D32 he
      have g9281 := a7 9281 (by norm_num) ((d32 1645 5254 2822 586 9280 (by norm_num)).trans hd)
      have g13 := a1 13 9281 g9281 (by norm_num)
      exact a3 7 13 g13 9281 g9281 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1607
    · exfalso; have hd := D8 he
      have g65393 := a7 65393 (by norm_num) ((d8 32122 52130 65392 (by norm_num)).trans hd)
      exact a6 3 65393 g65393 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1609
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1217 := a7 1217 (by norm_num) ((d16 322 239 1139 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 120 8 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1613
    · exfalso; have hd := D8 he
      have g3137 := a7 3137 (by norm_num) ((d8 1196 3081 3136 (by norm_num)).trans hd)
      have g523 := a1 523 3137 g3137 (by norm_num)
      have g131 := a1 131 523 g523 (by norm_num)
      exact a3 3 131 g131 3137 g3137 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g10433 := a7 10433 (by norm_num) ((d32 3952 103 176 10110 10432 (by norm_num)).trans hd)
      have g47 := a1 47 10433 g10433 (by norm_num)
      exact a3 3 47 g47 10433 g10433 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1619
    · exfalso; have hd := D8 he
      have g78593 := a7 78593 (by norm_num) ((d8 27592 66666 78592 (by norm_num)).trans hd)
      have g13099 := a1 13099 78593 g78593 (by norm_num)
      exact a6 5 13099 g13099 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 27 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g21569 := a7 21569 (by norm_num) ((d32 11312 14036 19619 6356 21568 (by norm_num)).trans hd)
      have g5 := a1 5 21569 g21569 (by norm_num)
      exact a3 3 5 g5 21569 g21569 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1621
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1627
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g11681 := a7 11681 (by norm_num) ((d16 7223 4383 7125 11680 (by norm_num)).trans hd)
      exact a6 3 11681 g11681 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1637
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 30 129 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1657
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1663
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 249 64 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 72 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1667
    · exfalso; have hd := D8 he
      exact q0 97 (by norm_num) ((d8 3234 5357 9408 (by norm_num)).trans hd)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g8641 := a7 8641 (by norm_num) ((d32 5128 1821 6538 7058 8640 (by norm_num)).trans hd)
      have g149 := a1 149 8641 g8641 (by norm_num)
      have g29 := a1 29 8641 g8641 (by norm_num)
      exact a3 3 149 g149 29 g29 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1669
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 179 251 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 185 64 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1693
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g2689 := a7 2689 (by norm_num) ((d32 2464 2223 2036 1547 2688 (by norm_num)).trans hd)
      have g269 := a1 269 2689 g2689 (by norm_num)
      exact a6 3 269 g269 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1697
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g449 := a7 449 (by norm_num) ((d16 372 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
    · exfalso; have hd := D32 he
      have g20929 := a7 20929 (by norm_num) ((d32 12536 16364 14870 2015 20928 (by norm_num)).trans hd)
      have g13 := a1 13 20929 g20929 (by norm_num)
      exact a3 7 13 g13 20929 g20929 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1699
    · exfalso; have hd := D8 he
      have g34714989264498225976453201 := b7 34714989264498225976453201 prime_34714989264498225976453201 (by norm_num) ((d8 2886601 8332465333201 34714989264498225976453200 (by norm_num)).trans hd)
      have g67 := a1 67 34714989264498225976453201 g34714989264498225976453201 (by norm_num)
      have g17 := a1 17 67 g67 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g2753 := a7 2753 (by norm_num) ((d16 1457 286 1959 2752 (by norm_num)).trans hd)
      exact a6 3 2753 g2753 (by norm_num)
    · exfalso; have hd := D32 he
      have g200257 := a7 200257 (by norm_num) ((d32 83003 56438 160259 187088 200256 (by norm_num)).trans hd)
      have g100129 := a1 100129 200257 g200257 (by norm_num)
      have g17 := a1 17 100129 g100129 (by norm_num)
      exact a6 3 17 g17 (by norm_num)

theorem zs2_1700 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1700 ≤ z) (hi : z < 1800)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1709
    · exfalso; have hd := D8 he
      have g39064015937 := b7 39064015937 prime_39064015937 (by norm_num) ((d8 2920681 14422029495 39064015936 (by norm_num)).trans hd)
      have g1331153 := a1 1331153 39064015937 g39064015937 (by norm_num)
      exact a6 3 1331153 g1331153 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g9601 := a7 9601 (by norm_num) ((d32 1977 922 5196 404 9600 (by norm_num)).trans hd)
      have g4801 := a1 4801 9601 g9601 (by norm_num)
      exact a6 7 4801 g4801 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1721
    · exfalso; have hd := D8 he
      have g550337 := a7 550337 (by norm_num) ((d8 210156 449749 550336 (by norm_num)).trans hd)
      exact a6 37 550337 g550337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1723
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 3 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 258 541 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1733
    · exfalso; have hd := D8 he
      have g1697 := a7 1697 (by norm_num) ((d8 1296 1283 1696 (by norm_num)).trans hd)
      have g283 := a1 283 1697 g1697 (by norm_num)
      have g71 := a1 71 283 g283 (by norm_num)
      exact a6 3 71 g71 (by norm_num)
    · exfalso; have hd := D16 he
      have g302977 := a7 302977 (by norm_num) ((d16 276496 154583 107899 302976 (by norm_num)).trans hd)
      have g271 := a1 271 302977 g302977 (by norm_num)
      have g17 := a1 17 271 g271 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1741
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1153 := a7 1153 (by norm_num) ((d16 997 123 140 1152 (by norm_num)).trans hd)
      have g577 := a1 577 1153 g1153 (by norm_num)
      exact a6 17 577 g577 (by norm_num)
    · exfalso; have hd := D32 he
      have g5441 := a7 5441 (by norm_num) ((d32 444 1260 4269 2452 5440 (by norm_num)).trans hd)
      have g907 := a1 907 5441 g5441 (by norm_num)
      have g227 := a1 227 907 g907 (by norm_num)
      exact a3 3 227 g227 5441 g5441 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1747
    · exfalso; have hd := D8 he
      have g82657 := a7 82657 (by norm_num) ((d8 76357 14640 82656 (by norm_num)).trans hd)
      have g1117 := a1 1117 82657 g82657 (by norm_num)
      have g43 := a1 43 1117 g1117 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      have g37 := a1 37 82657 g82657 (by norm_num)
      have g19 := a1 19 37 g37 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1753
    · exfalso; have hd := D8 he
      have g44588753651715539427437281 := b7 44588753651715539427437281 prime_44588753651715539427437281 (by norm_num) ((d8 3073009 9443384314081 44588753651715539427437280 (by norm_num)).trans hd)
      have g199 := a1 199 44588753651715539427437281 g44588753651715539427437281 (by norm_num)
      exact a6 5 199 g199 (by norm_num)
    · exfalso; have hd := D16 he
      have g817889 := a7 817889 (by norm_num) ((d16 619342 297187 369304 817888 (by norm_num)).trans hd)
      have g5 := a1 5 817889 g817889 (by norm_num)
      exact a3 3 5 g5 817889 g817889 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 60 2 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1759
    · exfalso; have hd := D8 he
      have g13729 := a7 13729 (by norm_num) ((d8 5056 13467 13728 (by norm_num)).trans hd)
      have g1373 := a1 1373 13729 g13729 (by norm_num)
      have g5 := a1 5 13729 g13729 (by norm_num)
      exact a3 3 1373 g1373 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g353 := a7 353 (by norm_num) ((d16 36 237 42 352 (by norm_num)).trans hd)
      have g59 := a1 59 353 g353 (by norm_num)
      exact a3 3 59 g59 353 g353 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 22 35 327 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1777
    · exfalso; have hd := D8 he
      have g49712937585586541809314241 := b7 49712937585586541809314241 prime_49712937585586541809314241 (by norm_num) ((d8 3157729 9971252437441 49712937585586541809314240 (by norm_num)).trans hd)
      have g263815884193138017859 := b1 263815884193138017859 prime_263815884193138017859 49712937585586541809314241 g49712937585586541809314241 (by norm_num)
      have g94219 := a1 94219 49712937585586541809314241 g49712937585586541809314241 (by norm_num)
      exact a3 5 263815884193138017859 g263815884193138017859 94219 g94219 (by norm_num)
    · exfalso; have hd := D16 he
      have g16001 := a7 16001 (by norm_num) ((d16 5532 9112 15356 16000 (by norm_num)).trans hd)
      exact a6 3 16001 g16001 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 227 129 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1783
    · exfalso; have hd := D8 he
      have g375233 := a7 375233 (by norm_num) ((d8 177225 197593 375232 (by norm_num)).trans hd)
      have g62539 := a1 62539 375233 g375233 (by norm_num)
      have g5 := a1 5 62539 g62539 (by norm_num)
      exact a3 3 5 g5 375233 g375233 (by norm_num)
    · exfalso; have hd := D16 he
      have g40961 := a7 40961 (by norm_num) ((d16 25092 37894 26420 40960 (by norm_num)).trans hd)
      have g6827 := a1 6827 40961 g40961 (by norm_num)
      exact a3 3 6827 g6827 40961 g40961 (by norm_num)
    · exfalso; have hd := D32 he
      have g769 := a7 769 (by norm_num) ((d32 43 311 596 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1787
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g2081 := a7 2081 (by norm_num) ((d16 1115 868 102 2080 (by norm_num)).trans hd)
      have g347 := a1 347 2081 g2081 (by norm_num)
      exact a3 3 347 g347 2081 g2081 (by norm_num)
    · exfalso; have hd := D32 he
      have g444929 := a7 444929 (by norm_num) ((d32 78866 183465 82446 162583 444928 (by norm_num)).trans hd)
      have g5 := a1 5 444929 g444929 (by norm_num)
      exact a3 3 5 g5 444929 g444929 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1789
    · exfalso; have hd := D8 he
      have g3452552017 := b7 3452552017 prime_3452552017 (by norm_num) ((d8 3200521 3065389019 3452552016 (by norm_num)).trans hd)
      have g1726276009 := b1 1726276009 prime_1726276009 3452552017 g3452552017 (by norm_num)
      have g8663 := a1 8663 1726276009 g1726276009 (by norm_num)
      have g5 := a1 5 1726276009 g1726276009 (by norm_num)
      exact a3 3 8663 g8663 5 g5 (by norm_num)
    · exfalso; have hd := D16 he
      have g769 := a7 769 (by norm_num) ((d16 712 173 707 768 (by norm_num)).trans hd)
      have g11 := a1 11 769 g769 (by norm_num)
      have g5 := a1 5 769 g769 (by norm_num)
      exact a3 3 11 g11 5 g5 (by norm_num)
    · exfalso; have hd := D32 he
      have g25793 := a7 25793 (by norm_num) ((d32 2189 20016 23380 19144 25792 (by norm_num)).trans hd)
      exact a6 3 25793 g25793 (by norm_num)

theorem zs2_1800 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1800 ≤ z) (hi : z < 1900)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1801
    · exfalso; have hd := D8 he
      have g193 := a7 193 (by norm_num) ((d8 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 18 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1811
    · exfalso; have hd := D8 he
      have g1861745233 := b7 1861745233 prime_1861745233 (by norm_num) ((d8 3279721 1267626800 1861745232 (by norm_num)).trans hd)
      have g269 := a1 269 1861745233 g1861745233 (by norm_num)
      exact a6 3 269 g269 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 72 166 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1823
    · exfalso; have hd := D8 he
      have g641 := a7 641 (by norm_num) ((d8 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1831
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g1012321 := a7 1012321 (by norm_num) ((d16 315598 846735 9111 1012320 (by norm_num)).trans hd)
      have g59 := a1 59 1012321 g1012321 (by norm_num)
      have g23 := a1 23 1012321 g1012321 (by norm_num)
      exact a3 3 59 g59 23 g23 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 151 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1847
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g4801 := a7 4801 (by norm_num) ((d16 2699 1484 3398 4800 (by norm_num)).trans hd)
      exact a6 7 4801 g4801 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1861
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1867
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 255 4 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 102 77 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1871
    · exfalso; have hd := D8 he
      have g75086230851720457458598081 := b7 75086230851720457458598081 prime_75086230851720457458598081 (by norm_num) ((d8 3500641 12254487410881 75086230851720457458598080 (by norm_num)).trans hd)
      have g373 := a1 373 75086230851720457458598081 g75086230851720457458598081 (by norm_num)
      have g17 := a1 17 373 g373 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 8 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1873
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      exact q0 97 (by norm_num) ((d16 7981 6840 4052 9408 (by norm_num)).trans hd)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 577 250 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1877
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 544 512 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1879
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 69 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g2273 := a7 2273 (by norm_num) ((d16 672 1530 1983 2272 (by norm_num)).trans hd)
      have g379 := a1 379 2273 g2273 (by norm_num)
      have g5 := a1 5 379 g379 (by norm_num)
      exact a3 3 5 g5 2273 g2273 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1889
    · exfalso; have hd := D8 he
      have g144241 := a7 144241 (by norm_num) ((d8 106537 96561 144240 (by norm_num)).trans hd)
      have g10303 := a1 10303 144241 g144241 (by norm_num)
      exact a3 7 10303 g10303 144241 g144241 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

theorem zs2_1900 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 1900 ≤ z) (hi : z < 2000)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1901
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g673 := a7 673 (by norm_num) ((d16 464 609 58 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 69 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1907
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 143 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1913
    · exfalso; have hd := D8 he
      have g97 := a7 97 (by norm_num) ((d8 50 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 100 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1931
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g40577 := a7 40577 (by norm_num) ((d16 36254 22909 39940 40576 (by norm_num)).trans hd)
      have g6763 := a1 6763 40577 g40577 (by norm_num)
      have g89 := a1 89 6763 g6763 (by norm_num)
      exact a6 3 89 g89 (by norm_num)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 64 250 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1933
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 100 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · exfalso; have hd := D32 he
      have g257 := a7 257 (by norm_num) ((d32 223 128 193 241 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1949
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g583937 := a7 583937 (by norm_num) ((d16 294979 158071 360748 583936 (by norm_num)).trans hd)
      exact a6 3 583937 g583937 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 344 287 830 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1951
    · exfalso; have hd := D8 he
      have g4817 := a7 4817 (by norm_num) ((d8 971 3526 4816 (by norm_num)).trans hd)
      have g11 := a1 11 4817 g4817 (by norm_num)
      exact a3 3 11 g11 4817 g4817 (by norm_num)
    · exfalso; have hd := D16 he
      have g44449 := a7 44449 (by norm_num) ((d16 28236 34432 18896 44448 (by norm_num)).trans hd)
      exact a6 5 44449 g44449 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 228 349 122 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1973
    · exfalso; have hd := D8 he
      have g3855409 := a7 3855409 (by norm_num) ((d8 37320 979751 3855408 (by norm_num)).trans hd)
      have g47 := a1 47 3855409 g3855409 (by norm_num)
      have g5 := a1 5 3855409 g3855409 (by norm_num)
      exact a3 3 47 g47 5 g5 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 577 250 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1979
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1987
    · exfalso; have hd := D8 he
      have g463364846353 := b7 463364846353 prime_463364846353 (by norm_num) ((d8 3948169 296998522912 463364846352 (by norm_num)).trans hd)
      have g231682423177 := b1 231682423177 prime_231682423177 463364846353 g463364846353 (by norm_num)
      have g17 := a1 17 231682423177 g231682423177 (by norm_num)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g641 := a7 641 (by norm_num) ((d16 250 323 487 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1993
    · exfalso; have hd := D8 he
      have g1217 := a7 1217 (by norm_num) ((d8 978 1139 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
    · exfalso; have hd := D16 he
      have g3457 := a7 3457 (by norm_num) ((d16 3413 1936 708 3456 (by norm_num)).trans hd)
      have g13 := a1 13 3457 g3457 (by norm_num)
      exact a3 7 13 g13 3457 g3457 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1997
    · exfalso; have hd := D8 he
      have g292083232917564916412257 := b7 292083232917564916412257 prime_292083232917564916412257 (by norm_num) ((d8 3988009 15904215784081 292083232917564916412256 (by norm_num)).trans hd)
      have g680097254967499 := b1 680097254967499 prime_680097254967499 292083232917564916412257 g292083232917564916412257 (by norm_num)
      exact a6 5 680097254967499 g680097254967499 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g577 := a7 577 (by norm_num) ((d32 362 65 186 553 576 (by norm_num)).trans hd)
      exact a6 17 577 g577 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 1999
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 129 43 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 350 372 92 382 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)

theorem zs2_2000 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 2000 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP (prime_dvd_prime_pow hz) E
  have q1 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False :=
    S_sq hP (prime_dvd_prime_pow hz) E hc h.1 (Finset.notMem_singleton.mpr h.2) ((hd.mul_left _).mul_right _)
  have q0 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c * c ∣ 1 + z ^ e) : False := q1 c h.1 h.2 hd
  have b7 (c) (hc : c.Prime) (h : c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P :=
    S7 c hc h.1 (Finset.notMem_singleton.mpr h.2) hd
  have a7 (c) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z) (hd : c ∣ 1 + z ^ e) : c ∈ P := b7 c h.1 h.2 hd
  have b1 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P :=
    S1 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a1 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : c ∈ P := b1 c h.1 p hp h.2
  have b6 (c) (hc : c.Prime) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False :=
    S6 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p hp h.2.2
  have a6 (c) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c * c ∣ p + 1) : False := b6 c h.1 p hp h.2
  have b8 (c) (hc : c.Prime) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False :=
    S8 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) hd p hp h.2.2
  have a8 (c) (hd : c ∣ 1 + z ^ e) (p) (hp : p ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p + 1) : False := b8 c h.1 hd p hp h.2
  have b3 (c) (hc : c.Prime) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    h.2.2.2.2 (S3 c hc h.1 (Finset.notMem_singleton.mpr h.2.1) p1 hp1 p2 hp2 h.2.2.1 h.2.2.2.1)
  have a3 (c) (p1) (hp1 : p1 ∈ P) (p2) (hp2 : p2 ∈ P) (h : c.Prime ∧ c ≠ 2 ∧ c ≠ z ∧ c ∣ p1 + 1 ∧ c ∣ p2 + 1 ∧ p1 ≠ p2) : False :=
    b3 c h.1 p1 hp1 p2 hp2 h.2
  have D8 : e % 16 = 8 → 1 + z ^ 8 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D16 : e % 32 = 16 → 1 + z ^ 16 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  have D32 : e % 64 = 32 → 1 + z ^ 32 ∣ 1 + z ^ e := fun h => one_add_pow_dvd_of_odd_mul (by omega)
  clear E S1 S2 S3 S4 S5 S6 S7 S8
  interval_cases z <;> first | (exfalso; revert hz; norm_num; done) | skip
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2003
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 9 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 89 64 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g641 := a7 641 (by norm_num) ((d32 631 100 385 154 640 (by norm_num)).trans hd)
      have g107 := a1 107 641 g641 (by norm_num)
      exact a6 3 107 g107 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2011
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · exfalso; have hd := D32 he
      have g449 := a7 449 (by norm_num) ((d32 427 35 327 67 448 (by norm_num)).trans hd)
      exact a6 3 449 g449 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2017
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 12 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 42 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2027
    · exfalso; have hd := D8 he
      have g673 := a7 673 (by norm_num) ((d8 64 58 672 (by norm_num)).trans hd)
      have g337 := a1 337 673 g673 (by norm_num)
      exact a6 13 337 g337 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2029
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 2 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g90977 := a7 90977 (by norm_num) ((d16 22876 11672 43015 90976 (by norm_num)).trans hd)
      have g59 := a1 59 90977 g90977 (by norm_num)
      exact a3 3 59 g59 90977 g90977 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 151 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2039
    · exfalso; have hd := D8 he
      have g241 := a7 241 (by norm_num) ((d8 30 177 240 (by norm_num)).trans hd)
      exact a6 11 241 g241 (by norm_num)
    · exfalso; have hd := D16 he
      have g257 := a7 257 (by norm_num) ((d16 32 253 16 256 (by norm_num)).trans hd)
      have g43 := a1 43 257 g257 (by norm_num)
      have g11 := a1 11 43 g43 (by norm_num)
      exact a3 3 11 g11 257 g257 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2053
    · exfalso; have hd := D8 he
      have g157790771387783474187901681 := b7 157790771387783474187901681 prime_157790771387783474187901681 (by norm_num) ((d8 4214809 17764614906481 157790771387783474187901680 (by norm_num)).trans hd)
      exact a6 7 157790771387783474187901681 g157790771387783474187901681 (by norm_num)
    · exfalso; have hd := D16 he
      have g100769 := a7 100769 (by norm_num) ((d16 83280 31206 83589 100768 (by norm_num)).trans hd)
      have g5 := a1 5 100769 g100769 (by norm_num)
      exact a3 3 5 g5 100769 g100769 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2063
    · exfalso; have hd := D8 he
      exact q0 17 (by norm_num) ((d8 155 38 288 (by norm_num)).trans hd)
    · exfalso; have hd := D16 he
      have g902753 := a7 902753 (by norm_num) ((d16 644957 810015 711566 902752 (by norm_num)).trans hd)
      exact a6 3 902753 g902753 (by norm_num)
    · exfalso; have hd := D32 he
      have g193 := a7 193 (by norm_num) ((d32 126 50 184 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2069
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 8 13 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2081
    · exfalso; have hd := D8 he
      have g17 := a7 17 (by norm_num) ((d8 15 4 16 (by norm_num)).trans hd)
      exact a6 3 17 g17 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 27 150 112 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g1217 := a7 1217 (by norm_num) ((d32 475 480 387 78 1216 (by norm_num)).trans hd)
      have g29 := a1 29 1217 g1217 (by norm_num)
      exact a3 3 29 g29 1217 g1217 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2083
    · exfalso; have hd := D8 he
      have g177208342683739494697085521 := b7 177208342683739494697085521 prime_177208342683739494697085521 (by norm_num) ((d8 4338889 18825957754321 177208342683739494697085520 (by norm_num)).trans hd)
      have g103 := a1 103 177208342683739494697085521 g177208342683739494697085521 (by norm_num)
      have g13 := a1 13 103 g103 (by norm_num)
      have g14102207757738301344667 := b1 14102207757738301344667 prime_14102207757738301344667 177208342683739494697085521 g177208342683739494697085521 (by norm_num)
      exact a3 7 13 g13 14102207757738301344667 g14102207757738301344667 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 79 33 22 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2087
    · exfalso; have hd := D8 he
      have g365656673 := b7 365656673 prime_365656673 (by norm_num) ((d8 4355569 347461848 365656672 (by norm_num)).trans hd)
      have g71 := a1 71 365656673 g365656673 (by norm_num)
      exact a6 3 71 g71 (by norm_num)
    · simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
    · simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2089
    · exfalso; have hd := D8 he
      have g53377 := a7 53377 (by norm_num) ((d8 40384 39975 53376 (by norm_num)).trans hd)
      have g2053 := a1 2053 53377 g53377 (by norm_num)
      exact a3 13 2053 g2053 53377 g53377 (by norm_num)
    · exfalso; have hd := D16 he
      have g97 := a7 97 (by norm_num) ((d16 85 47 75 96 (by norm_num)).trans hd)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g8641 := a7 8641 (by norm_num) ((d32 216 3451 2103 7058 8640 (by norm_num)).trans hd)
      have g149 := a1 149 8641 g8641 (by norm_num)
      have g29 := a1 29 8641 g8641 (by norm_num)
      exact a3 3 149 g149 29 g29 (by norm_num)
  · refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩  -- z = 2099
    · exfalso; have hd := D8 he
      have g113 := a7 113 (by norm_num) ((d8 44 15 112 (by norm_num)).trans hd)
      have g19 := a1 19 113 g113 (by norm_num)
      have g5 := a1 5 19 g19 (by norm_num)
      exact a3 3 5 g5 113 g113 (by norm_num)
    · exfalso; have hd := D16 he
      have g193 := a7 193 (by norm_num) ((d16 190 9 81 192 (by norm_num)).trans hd)
      have g97 := a1 97 193 g193 (by norm_num)
      exact a6 7 97 g97 (by norm_num)
    · exfalso; have hd := D32 he
      have g49921 := a7 49921 (by norm_num) ((d32 12753 46312 45421 31995 49920 (by norm_num)).trans hd)
      have g229 := a1 229 49921 g49921 (by norm_num)
      have g109 := a1 109 49921 g49921 (by norm_num)
      exact a3 5 229 g229 109 g109 (by norm_num)

-- Full sieve on [7, 2100).
theorem zsieve2 {m e z : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime)
    (lo : 7 ≤ z) (hi : z < 2100)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p) :
    (e % 16 ≠ 8) ∧
    (e % 32 = 16 → z ∈ ({29, 37, 41, 53, 59, 71, 73, 83, 89, 113, 157, 167, 173, 199, 211, 307, 353, 367, 397, 419, 449, 467, 479, 487, 491, 503, 509, 523, 547, 599, 607, 613, 617, 619, 643, 661, 691, 719, 727, 739, 743, 751, 761, 769, 811, 829, 877, 887, 929, 937, 967, 1019, 1063, 1103, 1151, 1201, 1213, 1223, 1229, 1237, 1249, 1277, 1297, 1301, 1321, 1373, 1487, 1511, 1531, 1553, 1579, 1637, 1657, 1667, 1693, 1709, 1721, 1747, 1811, 1973, 1979, 2011, 2027, 2069, 2087} : Finset ℕ)) ∧
    (e % 64 = 32 → z ∈ ({7, 41, 53, 59, 61, 101, 149, 157, 163, 179, 181, 191, 199, 227, 229, 239, 251, 293, 317, 337, 359, 367, 379, 401, 409, 467, 487, 509, 541, 571, 607, 617, 641, 709, 787, 829, 839, 883, 907, 941, 967, 971, 983, 991, 1009, 1021, 1163, 1181, 1201, 1213, 1217, 1223, 1231, 1279, 1297, 1303, 1319, 1327, 1361, 1367, 1429, 1451, 1481, 1483, 1489, 1493, 1549, 1559, 1567, 1607, 1621, 1627, 1657, 1721, 1733, 1747, 1801, 1823, 1847, 1861, 1871, 1879, 1889, 1907, 1913, 1979, 1987, 1993, 2027, 2039, 2053, 2069, 2083, 2087} : Finset ℕ)) := by
  rcases Nat.lt_or_ge z 100 with h | h; · exact zs2_0 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 200 with h | h; · exact zs2_100 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 300 with h | h; · exact zs2_200 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 400 with h | h; · exact zs2_300 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 500 with h | h; · exact zs2_400 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 600 with h | h; · exact zs2_500 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 700 with h | h; · exact zs2_600 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 800 with h | h; · exact zs2_700 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 900 with h | h; · exact zs2_800 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1000 with h | h; · exact zs2_900 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1100 with h | h; · exact zs2_1000 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1200 with h | h; · exact zs2_1100 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1300 with h | h; · exact zs2_1200 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1400 with h | h; · exact zs2_1300 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1500 with h | h; · exact zs2_1400 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1600 with h | h; · exact zs2_1500 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1700 with h | h; · exact zs2_1600 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1800 with h | h; · exact zs2_1700 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 1900 with h | h; · exact zs2_1800 hP hz (by omega) h E
  rcases Nat.lt_or_ge z 2000 with h | h; · exact zs2_1900 hP hz (by omega) h E
  exact zs2_2000 hP hz (by omega) hi E

-- Section 4. The step.
theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1.H4 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3),
    fun n h z hz lo hi hS he8 h7 c0 c1 c2 c4 c5 c6 c7 c15 U R => ?_⟩
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hz2 : z ≠ 2 := by omega
  have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf hz2 hs
  rw [Nat.factorization_def n Nat.prime_two] at E
  obtain ⟨z8, z16, z32⟩ := zsieve2 hP hz lo hi E
  have hc : n.factorization z % 16 = 8 ∨ n.factorization z % 32 = 16 ∨ n.factorization z % 64 = 32 ∨ n.factorization z % 64 = 0 := by omega
  rcases hc with c | c | c | c
  · exact absurd c z8
  · exact (h1 n h z hz hS c (z16 c) c0 c1 c2 c4 c5 c6 c7 c15 U R).trans (le_max_left _ _)
  · have hm := z32 c
    have hz7 : z ≠ 7 := by
      rintro rfl
      exact (h7 rfl).2 32 (by simp) c
    rw [Finset.mem_insert] at hm
    exact (h2 n h z hz hS c (hm.resolve_left hz7) c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 n h z hz lo hi hS c h7 c0 c1 c2 c4 c5 c6 c7 c15 U R).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H4_R1
