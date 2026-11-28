import OMAStatements.S_oeis_a298076

/-!
Disproof of T. Ordowski's 2018 conjecture on OEIS A298076.

Counterexample: `b = 80` (positive, `|b| = 80 > 1`, `gcd(80, 27) = 1`) and composite `n = 27 = 3^3`.
1. `27` is both a standard Fermat pseudoprime (`80^26 ≡ 1 [MOD 27]`) and a weak Fermat pseudoprime
   (`80^27 ≡ 80 [MOD 27]`) to base `|b| = 80`, since `80 ≡ -1 (mod 27)`.
2. The only prime divisor of `n = 27` is `p = 3`, and `(80^3 - 1) / (80 - 1) = 80^2 + 80 + 1 = 6481`
   is prime (certified by Lucas primality with base `a = 7` and `6481 - 1 = 2^4 * 3^4 * 5`), with
   `6481 % 27 = 1`. Thus every prime divisor `q` of `(80^p - 1) / (80 - 1)` satisfies `q ≡ 1 (mod 27)`.
3. However, `(80^27 - 1) / (80 - 1) = (80^2 + 80 + 1) * (80^6 + 80^3 + 1) * (80^18 + 80^9 + 1)`,
   and `19 ∣ (80^6 + 80^3 + 1) = 262144512001 = 19 * 13797079579`.
   Hence `19` divides `|(80^27 - 1) / (80 - 1)|`, yet `19 % 27 = 19 ≠ 1`.
-/

namespace OMA.D_oeis_a298076

private lemma mod_pow_double {a e e2 m v w : ℕ} (he : e2 = 2 * e) (hv : a ^ e % m = v)
    (hw : v * v % m = w) : a ^ e2 % m = w := by
  rw [he, show 2 * e = e + e by omega, pow_add, Nat.mul_mod, hv, hw]

private lemma mod_pow_succ {a e e1 m v w : ℕ} (he : e1 = e + 1) (hv : a ^ e % m = v)
    (hw : v * a % m = w) : a ^ e1 % m = w := by
  rw [he, pow_succ, Nat.mul_mod, hv]
  have h1 : (v * (a % m)) % m = (v * a) % m := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1, hw]

private lemma zmod_pow_eq_one {a e m : ℕ} (h : a ^ e % m = 1) :
    ((a : ℕ) : ZMod m) ^ e = 1 := by
  have h1 : ((a ^ e % m : ℕ) : ZMod m) = (1 : ZMod m) := by rw [h]; norm_num
  rw [ZMod.natCast_mod, Nat.cast_pow] at h1
  exact h1

private lemma zmod_pow_ne_one {a e m r : ℕ} (h : a ^ e % m = r) (hr : r ≠ 1 % m) :
    ((a : ℕ) : ZMod m) ^ e ≠ 1 := by
  intro heq
  have hmod : a ^ e ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
    exact heq
  have hmod' : a ^ e % m = 1 % m := hmod
  rw [h] at hmod'
  exact hr hmod'

private lemma prime_6481 : Nat.Prime 6481 := by
  apply lucas_primality 6481 ((7 : ℕ) : ZMod 6481)
  · rw [show (6481 - 1 : ℕ) = 6480 by norm_num]
    have h0_0 : 7 ^ 0 % 6481 = 1 := by norm_num
    have h0_1 : 7 ^ 1 % 6481 = 7 := mod_pow_succ (by norm_num) h0_0 (by norm_num)
    have h0_2 : 7 ^ 2 % 6481 = 49 := mod_pow_double (by norm_num) h0_1 (by norm_num)
    have h0_3 : 7 ^ 3 % 6481 = 343 := mod_pow_succ (by norm_num) h0_2 (by norm_num)
    have h0_4 : 7 ^ 6 % 6481 = 991 := mod_pow_double (by norm_num) h0_3 (by norm_num)
    have h0_5 : 7 ^ 12 % 6481 = 3450 := mod_pow_double (by norm_num) h0_4 (by norm_num)
    have h0_6 : 7 ^ 24 % 6481 = 3384 := mod_pow_double (by norm_num) h0_5 (by norm_num)
    have h0_7 : 7 ^ 25 % 6481 = 4245 := mod_pow_succ (by norm_num) h0_6 (by norm_num)
    have h0_8 : 7 ^ 50 % 6481 = 2845 := mod_pow_double (by norm_num) h0_7 (by norm_num)
    have h0_9 : 7 ^ 100 % 6481 = 5737 := mod_pow_double (by norm_num) h0_8 (by norm_num)
    have h0_10 : 7 ^ 101 % 6481 = 1273 := mod_pow_succ (by norm_num) h0_9 (by norm_num)
    have h0_11 : 7 ^ 202 % 6481 = 279 := mod_pow_double (by norm_num) h0_10 (by norm_num)
    have h0_12 : 7 ^ 404 % 6481 = 69 := mod_pow_double (by norm_num) h0_11 (by norm_num)
    have h0_13 : 7 ^ 405 % 6481 = 483 := mod_pow_succ (by norm_num) h0_12 (by norm_num)
    have h0_14 : 7 ^ 810 % 6481 = 6454 := mod_pow_double (by norm_num) h0_13 (by norm_num)
    have h0_15 : 7 ^ 1620 % 6481 = 729 := mod_pow_double (by norm_num) h0_14 (by norm_num)
    have h0_16 : 7 ^ 3240 % 6481 = 6480 := mod_pow_double (by norm_num) h0_15 (by norm_num)
    have h0_17 : 7 ^ 6480 % 6481 = 1 := mod_pow_double (by norm_num) h0_16 (by norm_num)
    exact zmod_pow_eq_one h0_17
  · intro q hq hdvd
    have hfac : (6481 - 1 : ℕ) = 2 ^ 4 * 3 ^ 4 * 5 := by norm_num
    rw [hfac] at hdvd
    have hq_mem : q = 2 ∨ q = 3 ∨ q = 5 := by
      rcases hq.dvd_mul.mp hdvd with h1 | h5
      · rcases hq.dvd_mul.mp h1 with h2 | h3
        · left
          exact (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp (hq.dvd_of_dvd_pow h2)
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp (hq.dvd_of_dvd_pow h3)
      · right; right
        exact (Nat.prime_dvd_prime_iff_eq hq (by decide)).mp h5
    rcases hq_mem with rfl | rfl | rfl
    · rw [show (6481 - 1) / 2 = 3240 by norm_num]
      have h2_0 : 7 ^ 0 % 6481 = 1 := by norm_num
      have h2_1 : 7 ^ 1 % 6481 = 7 := mod_pow_succ (by norm_num) h2_0 (by norm_num)
      have h2_2 : 7 ^ 2 % 6481 = 49 := mod_pow_double (by norm_num) h2_1 (by norm_num)
      have h2_3 : 7 ^ 3 % 6481 = 343 := mod_pow_succ (by norm_num) h2_2 (by norm_num)
      have h2_4 : 7 ^ 6 % 6481 = 991 := mod_pow_double (by norm_num) h2_3 (by norm_num)
      have h2_5 : 7 ^ 12 % 6481 = 3450 := mod_pow_double (by norm_num) h2_4 (by norm_num)
      have h2_6 : 7 ^ 24 % 6481 = 3384 := mod_pow_double (by norm_num) h2_5 (by norm_num)
      have h2_7 : 7 ^ 25 % 6481 = 4245 := mod_pow_succ (by norm_num) h2_6 (by norm_num)
      have h2_8 : 7 ^ 50 % 6481 = 2845 := mod_pow_double (by norm_num) h2_7 (by norm_num)
      have h2_9 : 7 ^ 100 % 6481 = 5737 := mod_pow_double (by norm_num) h2_8 (by norm_num)
      have h2_10 : 7 ^ 101 % 6481 = 1273 := mod_pow_succ (by norm_num) h2_9 (by norm_num)
      have h2_11 : 7 ^ 202 % 6481 = 279 := mod_pow_double (by norm_num) h2_10 (by norm_num)
      have h2_12 : 7 ^ 404 % 6481 = 69 := mod_pow_double (by norm_num) h2_11 (by norm_num)
      have h2_13 : 7 ^ 405 % 6481 = 483 := mod_pow_succ (by norm_num) h2_12 (by norm_num)
      have h2_14 : 7 ^ 810 % 6481 = 6454 := mod_pow_double (by norm_num) h2_13 (by norm_num)
      have h2_15 : 7 ^ 1620 % 6481 = 729 := mod_pow_double (by norm_num) h2_14 (by norm_num)
      have h2_16 : 7 ^ 3240 % 6481 = 6480 := mod_pow_double (by norm_num) h2_15 (by norm_num)
      exact zmod_pow_ne_one h2_16 (by norm_num)
    · rw [show (6481 - 1) / 3 = 2160 by norm_num]
      have h3_0 : 7 ^ 0 % 6481 = 1 := by norm_num
      have h3_1 : 7 ^ 1 % 6481 = 7 := mod_pow_succ (by norm_num) h3_0 (by norm_num)
      have h3_2 : 7 ^ 2 % 6481 = 49 := mod_pow_double (by norm_num) h3_1 (by norm_num)
      have h3_3 : 7 ^ 4 % 6481 = 2401 := mod_pow_double (by norm_num) h3_2 (by norm_num)
      have h3_4 : 7 ^ 8 % 6481 = 3192 := mod_pow_double (by norm_num) h3_3 (by norm_num)
      have h3_5 : 7 ^ 16 % 6481 = 732 := mod_pow_double (by norm_num) h3_4 (by norm_num)
      have h3_6 : 7 ^ 32 % 6481 = 4382 := mod_pow_double (by norm_num) h3_5 (by norm_num)
      have h3_7 : 7 ^ 33 % 6481 = 4750 := mod_pow_succ (by norm_num) h3_6 (by norm_num)
      have h3_8 : 7 ^ 66 % 6481 = 2139 := mod_pow_double (by norm_num) h3_7 (by norm_num)
      have h3_9 : 7 ^ 67 % 6481 = 2011 := mod_pow_succ (by norm_num) h3_8 (by norm_num)
      have h3_10 : 7 ^ 134 % 6481 = 6458 := mod_pow_double (by norm_num) h3_9 (by norm_num)
      have h3_11 : 7 ^ 135 % 6481 = 6320 := mod_pow_succ (by norm_num) h3_10 (by norm_num)
      have h3_12 : 7 ^ 270 % 6481 = 6478 := mod_pow_double (by norm_num) h3_11 (by norm_num)
      have h3_13 : 7 ^ 540 % 6481 = 9 := mod_pow_double (by norm_num) h3_12 (by norm_num)
      have h3_14 : 7 ^ 1080 % 6481 = 81 := mod_pow_double (by norm_num) h3_13 (by norm_num)
      have h3_15 : 7 ^ 2160 % 6481 = 80 := mod_pow_double (by norm_num) h3_14 (by norm_num)
      exact zmod_pow_ne_one h3_15 (by norm_num)
    · rw [show (6481 - 1) / 5 = 1296 by norm_num]
      have h5_0 : 7 ^ 0 % 6481 = 1 := by norm_num
      have h5_1 : 7 ^ 1 % 6481 = 7 := mod_pow_succ (by norm_num) h5_0 (by norm_num)
      have h5_2 : 7 ^ 2 % 6481 = 49 := mod_pow_double (by norm_num) h5_1 (by norm_num)
      have h5_3 : 7 ^ 4 % 6481 = 2401 := mod_pow_double (by norm_num) h5_2 (by norm_num)
      have h5_4 : 7 ^ 5 % 6481 = 3845 := mod_pow_succ (by norm_num) h5_3 (by norm_num)
      have h5_5 : 7 ^ 10 % 6481 = 864 := mod_pow_double (by norm_num) h5_4 (by norm_num)
      have h5_6 : 7 ^ 20 % 6481 = 1181 := mod_pow_double (by norm_num) h5_5 (by norm_num)
      have h5_7 : 7 ^ 40 % 6481 = 1346 := mod_pow_double (by norm_num) h5_6 (by norm_num)
      have h5_8 : 7 ^ 80 % 6481 = 3517 := mod_pow_double (by norm_num) h5_7 (by norm_num)
      have h5_9 : 7 ^ 81 % 6481 = 5176 := mod_pow_succ (by norm_num) h5_8 (by norm_num)
      have h5_10 : 7 ^ 162 % 6481 = 5003 := mod_pow_double (by norm_num) h5_9 (by norm_num)
      have h5_11 : 7 ^ 324 % 6481 = 387 := mod_pow_double (by norm_num) h5_10 (by norm_num)
      have h5_12 : 7 ^ 648 % 6481 = 706 := mod_pow_double (by norm_num) h5_11 (by norm_num)
      have h5_13 : 7 ^ 1296 % 6481 = 5880 := mod_pow_double (by norm_num) h5_12 (by norm_num)
      exact zmod_pow_ne_one h5_13 (by norm_num)

theorem disprove_main : ¬ (type_of% @OMA.S_oeis_a298076.main) := by
  intro hmain
  have hiff := hmain 80 (by norm_num) 27 (by norm_num) (by decide)
  have hrhs : (80 : ℤ).natAbs ^ 27 % 27 = (80 : ℤ).natAbs % 27 ∧
      ∀ p : ℕ, p.Prime → p ∣ 27 →
        ∀ q : ℕ, q.Prime → q ∣ (((80 : ℤ) ^ p - 1) / (80 - 1)).natAbs → q % 27 = 1 := by
    refine ⟨?_, ?_⟩
    · have hmod : 80 ^ 27 ≡ 80 [MOD 27] := by
        have h1 : 80 ≡ 26 [MOD 27] := by decide
        have h2 : 80 ^ 27 ≡ 26 ^ 27 [MOD 27] := h1.pow 27
        have h3 : 26 ^ 2 ≡ 1 [MOD 27] := by decide
        have h4 : 26 ^ 27 = (26 ^ 2) ^ 13 * 26 := by ring
        have h5 : 26 ^ 27 ≡ 1 ^ 13 * 26 [MOD 27] := by
          rw [h4]; exact (h3.pow 13).mul_right 26
        have h6 : 1 ^ 13 * 26 ≡ 80 [MOD 27] := by decide
        exact h2.trans (h5.trans h6)
      exact hmod
    · intro p hp hp_dvd q hq hq_dvd
      have hp3 : p = 3 := by
        have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
        rw [h27] at hp_dvd
        exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hp_dvd)
      subst hp3
      have hval : (((80 : ℤ) ^ 3 - 1) / (80 - 1)).natAbs = 6481 := by norm_num
      rw [hval] at hq_dvd
      have hq_eq : q = 6481 := (Nat.prime_dvd_prime_iff_eq hq prime_6481).mp hq_dvd
      rw [hq_eq]
  have hlhs := hiff.mpr hrhs
  have h19_dvd : 19 ∣ (((80 : ℤ) ^ 27 - 1) / (80 - 1)).natAbs := by
    have hfactor : ((80 : ℤ) ^ 27 - 1) =
        (80 - 1) * ((80 ^ 2 + 80 + 1) * (80 ^ 6 + 80 ^ 3 + 1) * (80 ^ 18 + 80 ^ 9 + 1)) := by
      ring
    have hdiv : ((80 : ℤ) ^ 27 - 1) / (80 - 1) =
        (80 ^ 2 + 80 + 1) * (80 ^ 6 + 80 ^ 3 + 1) * (80 ^ 18 + 80 ^ 9 + 1) := by
      rw [hfactor]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    rw [hdiv]
    have h19_mid : (19 : ℤ) ∣ (80 ^ 6 + 80 ^ 3 + 1 : ℤ) := by
      refine ⟨13797079579, ?_⟩
      norm_num
    have h19_int : (19 : ℤ) ∣
        (80 ^ 2 + 80 + 1 : ℤ) * (80 ^ 6 + 80 ^ 3 + 1) * (80 ^ 18 + 80 ^ 9 + 1) :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h19_mid _) _
    exact Int.ofNat_dvd_left.mp h19_int
  have h19_mod := hlhs 19 h19_dvd
  norm_num at h19_mod

end OMA.D_oeis_a298076

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298076.main) :=
  OMA.D_oeis_a298076.disprove_main
