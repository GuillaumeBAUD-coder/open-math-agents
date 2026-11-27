import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1
-- Shrinks step H1 (the 5-chain core with 19) of Erdos1052.erdos_1052.R1.H2.R1.H2.R1 and splits it
-- in three.  Proving all three H proves the step.
--
-- Notation as in the parent file: n unitary perfect, a = padicValNat 2 n, S = the set of odd
-- primes p with p^2 | n, S admissible (every z in S is at least 128 and at least S.card + 3, and
-- the product over S of (z + 1) / (z - 2 - S.card) is at most 2101/2097).  A prime of n is
-- SIMPLE if it divides n exactly once; the PARENT of a simple odd prime c is the simple odd prime
-- p of n with c | p + 1, if there is one.  B(x) = (x + 1) / (x - 1).
--
-- PROVED BELOW, no hypothesis needed:
--   adm_ge_2100: every prime of an admissible set is at least 2100.  So every prime of n below
--     2100 is simple.
--   two_adic_core: let S be admissible, 5 | n and 4 | a.  Then 16 | a and a is not 32 mod 64.
--     (17 | 2^a + 1 if a = 4 mod 8, 257 | 2^a + 1 if a = 8 mod 16, 641 | 2^a + 1 if a = 32 mod 64;
--     each would be a simple prime p of n with 3 | p + 1, and 5 is the only such prime.)
--     So a = 0 or a >= 16, and the weight inequality of Erdos1052.erdos_1052.R1.H2.R1 (theorem
--     master) holds with 65537/65536 in place of 1025/1024 (theorem master16 below).
--   core_with_19: let S be admissible, 4 | a, and 5, 7, 19 divide n.  Then a <= 9, or 31 | n, the
--     primes of n below 152 are exactly 2, 3, 5, 7, 19, 31, and one of 223, 433, 607 divides n.
--     None of the residue conditions of the parent step are used.
--     Method: 5 is the parent of 3 and 19 is the parent of 5.  The weight argument is applied
--     six times, twice with master and four times with master16:
--       neither 31 nor 37 divides n: the parent of 19 is at least 151, the parent of 7 at least 223;
--       37 divides n, 31, 73 and 127 do not: parent of 37 at least 2737, parent of 7 is 223 (then
--         the parent of 223 is at least 1783) or at least 433;
--       37 and 127 divide n (then every further prime is at least 263): parent of 37 at least
--         9397, parent of 7 at least 1777, parent of 127 at least 66801;
--       31 divides n (then every further prime is at least 152) and none of 223, 433, 607, 991,
--         1063 does: parent of 19 at least 5775, of 7 at least 2281, of 31 at least 3967;
--       the same with 991 | n: 991 is the parent of 31 and its parent is at least 3963;
--       31 and 1063 divide n: 1063 is the parent of 7 and of 19, its parent is at least 4251, and
--         the parent of 31 is at least 991.
--     Everything else is the abundancy bound: the product of 1 + 1/p over any set of simple odd
--     primes of n is below 2 (13 is excluded by 3, 5, 7, 19; with 37 the prime 73 is excluded).
--
-- H1 (OPEN): the step restricted to 16 | a, a not 32 mod 64, 31 | n, primes of n below 152 exactly
--    2, 3, 5, 7, 19, 31, and 223 | n (223 is then the parent of 7).
-- H2 (OPEN): the same with 433 | n (433 is then the parent of 7 and of 31).
-- H3 (OPEN): the same with 607 | n (607 is then the parent of 19).
-- None can be closed by the weight inequality alone.  The products of 1 + 1/p over
--   3, 5, 7, 19, 31, 223 (1.995813), over 3, 5, 7, 19, 31, 433, 607, 1213 (1.996417) and over
--   3, 5, 7, 19, 31, 223, 607 (1.999101) lie in the window [1.995187, 2) that the inequality
-- cannot exclude (computed with exact fractions outside Lean; these are configurations of small
-- primes, not unitary perfect numbers).  No known unitary perfect number is in any of the three
-- families.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1

-- The 2-adic valuation is bounded over the family of step H1 of the parent file restricted to
-- 16 | a, a not 32 mod 64, 31 | n, no prime of n below 152 other than 2, 3, 5, 7, 19, 31, and
-- 223 | n.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    223 ∣ n →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H1 of the parent file restricted to
-- 16 | a, a not 32 mod 64, 31 | n, no prime of n below 152 other than 2, 3, 5, 7, 19, 31, and
-- 433 | n.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    433 ∣ n →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H1 of the parent file restricted to
-- 16 | a, a not 32 mod 64, 31 | n, no prime of n below 152 other than 2, 3, 5, 7, 19, 31, and
-- 607 | n.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n →
    padicValNat 2 n ≤ A

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1 hiding H1 H2 main

-- A set of primes that is at least 2100 does not contain a number below 2100.
theorem big_notMem {N : Finset ℕ} (hNb : ∀ z ∈ N, 2100 ≤ z) {c : ℕ} (hc : c < 2100) : c ∉ N :=
  fun h => by
    have := hNb c h
    omega

-- A prime p ≠ 37 with 19 ∣ p + 1 and 3 ∤ p + 1 is at least 151.
theorem Q19 {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (hne : p ≠ 37) :
    151 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 38 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 38 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 13, 223 with 7 ∣ p + 1 and none of 3, 5, 11, 13, 49 dividing p + 1 is at least 433.
theorem Q7c {p : ℕ} (hp : p.Prime) (hd : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h11 : ¬ 11 ∣ p + 1)
    (h13 : ¬ 13 ∣ p + 1) (hsq : ¬ 7 * 7 ∣ p + 1) (hne : p ≠ 223) (hne13 : p ≠ 13) :
    433 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 31 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 73 whose least odd child is 37 is at least 2737.
theorem R37 {p : ℕ} (hp : p.Prime) (hd : 37 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 37 ≤ c') (hne : p ≠ 73) : 2737 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 7 := by
      by_contra hcon
      have : 2 ^ 7 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime whose least odd child is 223 is at least 1783.
theorem R223 {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 223 ≤ c') : 1783 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 3 := by
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp
  · omega

-- Core with 19: neither 31 nor 37 is in P.  Then the chain parent of 19 is at least 151.
theorem core19_A {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (h13 : 13 ∉ P) (h31 : 31 ∉ P) (h37 : 37 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (152 / 150))) else
      if p = 5 then 6 / 5 * (20 / 19 * (152 / 150)) else
      if p = 19 then 20 / 19 * (152 / 150) else
      if p = 7 then 8 / 7 * (224 / 222) else
      if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (152 / 150))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (152 / 150)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (152 / 150) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e19 e7 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 151 ≤ p := Q19 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h37 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 151) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 223 ≤ p := R7 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h13 (S1 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h13 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e7 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Core with 19 and 37, without 31, 73, 127.
theorem core19_C {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (h13 : 13 ∉ P) (h31 : 31 ∉ P) (h37 : 37 ∈ P) (h73 : 73 ∉ P) (h127 : 127 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (38 / 37 * (2738 / 2736)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (38 / 37 * (2738 / 2736))) else
      if p = 19 then 20 / 19 * (38 / 37 * (2738 / 2736)) else
      if p = 37 then 38 / 37 * (2738 / 2736) else
      if p = 7 then 8 / 7 * (224 / 223 * (1784 / 1782)) else
      if p = 223 then 224 / 223 * (1784 / 1782) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (38 / 37 * (2738 / 2736)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (38 / 37 * (2738 / 2736))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (38 / 37 * (2738 / 2736)) := by rw [hβ]; norm_num
  have b37 : β 37 = 38 / 37 * (2738 / 2736) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1784 / 1782)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1784 / 1782) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 37 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e37 e7 e223 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e37, if_neg e7, if_neg e223, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e37 : p = 37
    · subst e37; rw [b37]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e37 e7 e223 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 37 := S2 19 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 37 h37 hd (by norm_num)
      rw [b19, b37]; norm_num
    by_cases e37 : c = 37
    · subst e37
      have hge : 2737 ≤ p := R37 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
        (fun h => h73 (h ▸ hp))
      rw [b37]
      exact step_ge (t := 2737) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      by_cases e : p = 223
      · subst e; rw [b7, b223]; norm_num
      have hge : 433 ≤ p := Q7c (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (fun h => h13 (S1 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        e
        (fun h => h13 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 433) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e223 : c = 223
    · subst e223
      have hge : 1783 ≤ p := R223 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b223]
      exact step_ge (t := 1783) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e37 e7 e223 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num


-- Abundancy: a subset A of P and one more element q of P together have product of 1 + 1/p below 2.
theorem abund_gap {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    {A : Finset ℕ} (hA : A ⊆ P) {q : ℕ} (hq : q ∈ P) (hqA : q ∉ A) :
    (q + 1) * ∏ p ∈ A, (p + 1) < 2 * (q * ∏ p ∈ A, p) := by
  have h := S_abund hP (K_pos hN hK) hKK.1 E (Finset.insert_subset hq hA)
  rwa [Finset.prod_insert hqA, Finset.prod_insert hqA] at h


-- The master inequality of the parent file for m at least 16 (same proof, with 65537/65536 in
-- place of 1025/1024).
theorem master16 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hfin : 65537 / 65536 * (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * (2101 / 2097) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
    refine (Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)).trans ?_
    refine nleaf_bound (fun z hz => ⟨(hN z hz).1, (hN z hz).2.2⟩) _ (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    have hqP := hP q (hLP q hqL)
    refine ⟨?_, hne, hleaf q hqL⟩
    rcases hqP.1.eq_two_or_odd with h | h
    · exact absurd h hqP.2
    · omega
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  have hΛ0 : (0 : ℚ) ≤ ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
    Finset.prod_nonneg fun z hz => by
      have h3 : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z hz).2.2
      exact div_nonneg (by linarith) (by linarith)
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
        ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hΛ0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  -- the equation over ℚ
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 65537 / 65536 := by
    have h2 : (2 : ℚ) ^ 16 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 16 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hA : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤ 65537 / 65536 * ((K' : ℚ) / K) :=
    mul_le_mul_of_nonneg_right hT hKr0
  have hC := mul_le_mul hA (hpath.trans hprodL)
    (Finset.prod_nonneg fun p _ => by positivity) (mul_nonneg (by norm_num) hKr0)
  have hD : (K' : ℚ) / K * (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
      ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) ≤
      2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047)) :=
    mul_le_mul_of_nonneg_right hKK.2 hM0
  have hfinal : (2 : ℚ) ≤
      65537 / 65536 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by
    calc (2 : ℚ) = (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) := hEq.symm
      _ ≤ 65537 / 65536 * ((K' : ℚ) / K) *
          ((∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
            ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := hC
      _ = 65537 / 65536 * ((K' : ℚ) / K * (∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ)))) *
          ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) := by ring
      _ ≤ 65537 / 65536 * (2101 / 2097 * ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047))) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
  linarith

-- Variant of child_cases: c divides N exactly once and every other odd prime factor of N is at
-- least b.
theorem child_cases_c {N c b : ℕ} (hN0 : N ≠ 0) (hN : 2 ∣ N) (hc : c.Prime) (hc2 : c ≠ 2)
    (hcN : c ∣ N) (hsq : ¬ c * c ∣ N)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ c → c' ∣ N → b ≤ c') :
    (∃ i, N = c * 2 ^ i) ∨ 2 * c * b ≤ N := by
  obtain ⟨k, rfl⟩ := hcN
  have hk0 : k ≠ 0 := by rintro rfl; simp at hN0
  have hmul := Nat.ordProj_mul_ordCompl_eq_self k 2
  by_cases ho1 : k / 2 ^ k.factorization 2 = 1
  · left
    refine ⟨k.factorization 2, ?_⟩
    rw [ho1, mul_one] at hmul
    rw [hmul]
  · right
    have hq := Nat.minFac_prime ho1
    have hqo : (k / 2 ^ k.factorization 2).minFac ∣ k / 2 ^ k.factorization 2 := Nat.minFac_dvd _
    have hodd : ¬ 2 ∣ k / 2 ^ k.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hk0
    have hq2 : (k / 2 ^ k.factorization 2).minFac ≠ 2 := fun h => by
      have h' := hqo
      rw [h] at h'
      exact hodd h'
    have hok : k / 2 ^ k.factorization 2 ∣ k := Dvd.intro_left _ hmul
    have hopos : 0 < k / 2 ^ k.factorization 2 :=
      Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hk0 hmul.symm
    have hqc : (k / 2 ^ k.factorization 2).minFac ≠ c := fun h => by
      have h' := hqo.trans hok
      rw [h] at h'
      exact hsq (Nat.mul_dvd_mul_left c h')
    have hcq : b ≤ (k / 2 ^ k.factorization 2).minFac :=
      hmin _ hq hq2 hqc ((hqo.trans hok).mul_left c)
    have hco : b ≤ k / 2 ^ k.factorization 2 := hcq.trans (Nat.minFac_le hopos)
    have hcop2c : Nat.Coprime 2 c := (Nat.coprime_primes Nat.prime_two hc).mpr (Ne.symm hc2)
    have h2k : 2 ∣ k := (Nat.Coprime.dvd_mul_left hcop2c).mp hN
    have hcop : Nat.Coprime 2 (k / 2 ^ k.factorization 2) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h2o : 2 * (k / 2 ^ k.factorization 2) ≤ k :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2k hok)
    calc 2 * c * b = c * (2 * b) := by ring
      _ ≤ c * (2 * (k / 2 ^ k.factorization 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hco)
      _ ≤ c * k := Nat.mul_le_mul_left _ h2o

-- A prime p ≠ 73 with 37 dividing p + 1 exactly once and every other odd prime factor of p + 1
-- at least 127 is at least 9397.
theorem R37c {p : ℕ} (hp : p.Prime) (hd : 37 ∣ p + 1) (hsq : ¬ 37 * 37 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 37 → c' ∣ p + 1 → 127 ≤ c') (hne : p ≠ 73) : 9397 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 8 := by
      by_contra hcon
      have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime p with 127 dividing p + 1 exactly once and every other odd prime factor of p + 1 at
-- least 263 is at least 66801.
theorem R127c {p : ℕ} (hp : p.Prime) (hd : 127 ∣ p + 1) (hsq : ¬ 127 * 127 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 127 → c' ∣ p + 1 → 263 ≤ c') : 66801 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 10 := by
      by_contra hcon
      have : 2 ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp
  · omega

-- A prime p ≠ 13, 223 with 7 ∣ p + 1, 49 ∤ p + 1 and none of the listed primes dividing p + 1 is
-- at least 1777.
theorem Q7e {p : ℕ} (hp : p.Prime) (hd : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h11 : ¬ 11 ∣ p + 1) (h13 : ¬ 13 ∣ p + 1) (h19 : ¬ 19 ∣ p + 1) (h23 : ¬ 23 ∣ p + 1) (h29 : ¬ 29 ∣ p + 1) (h31 : ¬ 31 ∣ p + 1) (h43 : ¬ 43 ∣ p + 1) (h53 : ¬ 53 ∣ p + 1) (h61 : ¬ 61 ∣ p + 1) (h67 : ¬ 67 ∣ p + 1) (h73 : ¬ 73 ∣ p + 1)
    (hsq : ¬ 7 * 7 ∣ p + 1) (hne13 : p ≠ 13) (hne223 : p ≠ 223) :
    1777 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 127 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- Core with 19, 37 and 127 for m at least 16, when the elements of P below 263 are exactly
-- 3, 5, 7, 19, 37, 127: impossible.
theorem core19_C16 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (h37 : 37 ∈ P) (hs : ∀ q ∈ P, q < 263 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 37 ∨ q = 127) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := fun h => by
    have := hs 31 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (38 / 37 * (9398 / 9396)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (38 / 37 * (9398 / 9396))) else
      if p = 19 then 20 / 19 * (38 / 37 * (9398 / 9396)) else
      if p = 37 then 38 / 37 * (9398 / 9396) else
      if p = 7 then 8 / 7 * (1778 / 1776) else
      if p = 31 then 1 else
      if p = 127 then 128 / 127 * (66802 / 66800) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (38 / 37 * (9398 / 9396)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (38 / 37 * (9398 / 9396))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (38 / 37 * (9398 / 9396)) := by rw [hβ]; norm_num
  have b37 : β 37 = 38 / 37 * (9398 / 9396) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (1778 / 1776) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (66802 / 66800) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 37 → c ≠ 7 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e37 e7 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e37, if_neg e7, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e37 : p = 37
    · subst e37; rw [b37]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e19 e37 e7 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 37 := S2 19 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 37 h37 hd (by norm_num)
      rw [b19, b37]; norm_num
    by_cases e37 : c = 37
    · subst e37
      have hge : 9397 ≤ p := R37c (hP p hp).1 hd
        (S4b 37 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hlt
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 73 (h ▸ hp) (by norm_num)
          omega)
      rw [b37]
      exact step_ge (t := 9397) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 1777 ≤ p := Q7e (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by
          have := hs 11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 13 (S1 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := S2 19 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 37 h37 h (by norm_num)
          subst this
          omega)
        (fun h => by
          have := hs 23 (S1 23 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 29 (S1 29 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 31 (S1 31 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 43 (S1 43 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 53 (S1 53 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 61 (S1 61 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 67 (S1 67 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 73 (S1 73 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h) (by norm_num)
          omega)
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => by
          have := hs 13 (h ▸ hp) (by norm_num)
          omega)
        (fun h => by
          have := hs 223 (h ▸ hp) (by norm_num)
          omega)
      rw [b7]
      exact step_ge (t := 1777) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      have hge : 66801 ≤ p := R127c (hP p hp).1 hd
        (S4b 127 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hlt
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
      rw [b127]
      exact step_ge (t := 66801) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e19 e37 e7 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num


-- A prime p other than 13, 223, 433, 1063 with 7 ∣ p + 1, 49 ∤ p + 1 and none of the listed primes
-- dividing p + 1 is at least 2281.
theorem Q7f {p : ℕ} (hp : p.Prime) (hd : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h11 : ¬ 11 ∣ p + 1) (h13 : ¬ 13 ∣ p + 1) (h23 : ¬ 23 ∣ p + 1) (h29 : ¬ 29 ∣ p + 1) (h43 : ¬ 43 ∣ p + 1) (h53 : ¬ 53 ∣ p + 1) (h61 : ¬ 61 ∣ p + 1) (h67 : ¬ 67 ∣ p + 1) (h71 : ¬ 71 ∣ p + 1) (h73 : ¬ 73 ∣ p + 1) (h127 : ¬ 127 ∣ p + 1) (h151 : ¬ 151 ∣ p + 1)
    (hsq : ¬ 7 * 7 ∣ p + 1) (hne13 : p ≠ 13) (hne223 : p ≠ 223) (hne433 : p ≠ 433)
    (hne1063 : p ≠ 1063) : 2281 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 163 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p other than 37, 151, 607 with 19 dividing p + 1 exactly once, 3 ∤ p + 1 and every
-- other odd prime factor of p + 1 either 31 or at least 152 is at least 5775.
theorem Q19f {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1) (hsq : ¬ 19 * 19 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 19 → c' ∣ p + 1 → c' = 31 ∨ 152 ≤ c')
    (h37 : p ≠ 37) (h151 : p ≠ 151) (h607 : p ≠ 607) : 5775 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  by_cases h31 : 31 ∣ p + 1
  · obtain ⟨j, hj⟩ : 19 * 31 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd h31
    have hj10 : j < 10 := by
      clear hd hsq h3 h31 h2 hmin h37 h151 h607 hp2
      omega
    have hj0 : 0 < j := by
      clear hd hsq h3 h31 h2 hmin h37 h151 h607 hp2
      omega
    obtain rfl : p = 19 * 31 * j - 1 := Nat.eq_sub_of_add_eq hj
    clear hd hsq h31 h2 hmin h37 h151 h607 hp2 hj
    interval_cases j <;> first | omega | (norm_num at hp)
  · rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq
      (fun c' h1 h2' h3' h4 => by
        rcases hmin c' h1 h2' h3' h4 with rfl | h
        · exact absurd h4 h31
        · exact h) with ⟨i, hi⟩ | h
    · have hi9 : i < 9 := by
        by_contra hcon
        have : 2 ^ 9 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases i <;> first | (exfalso; omega) |
        (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
    · omega

-- A prime p other than 61 and 991 with 31 dividing p + 1 exactly once and every other odd prime
-- factor of p + 1 at least 152 is at least 3967.
theorem R31f {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1) (hsq : ¬ 31 * 31 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 31 → c' ∣ p + 1 → 152 ≤ c')
    (h61 : p ≠ 61) (h991 : p ≠ 991) : 3967 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 8 := by
      by_contra hcon
      have : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime p with 991 dividing p + 1 exactly once and every other odd prime factor of p + 1 at
-- least 991 is at least 3963.
theorem R991 {p : ℕ} (hp : p.Prime) (hd : 991 ∣ p + 1) (hsq : ¬ 991 * 991 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 991 → c' ∣ p + 1 → 991 ≤ c') : 3963 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 2 := by
      by_contra hcon
      have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime p with 1063 dividing p + 1 exactly once and every other odd prime factor of p + 1 at
-- least 1063 is at least 4251.
theorem R1063 {p : ℕ} (hp : p.Prime) (hd : 1063 ∣ p + 1) (hsq : ¬ 1063 * 1063 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 1063 → c' ∣ p + 1 → 1063 ≤ c') : 4251 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 2 := by
      by_contra hcon
      have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- Core with 19 and 31, m at least 16, elements of P below 152 exactly 3, 5, 7, 19, 31, and none
-- of 223, 433, 607, 991, 1063 in P: impossible.
theorem core19_31_a {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h223 : 223 ∉ P) (h433 : 433 ∉ P) (h607 : 607 ∉ P) (h991 : 991 ∉ P) (h1063 : 1063 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) else
      if p = 5 then 6 / 5 * (20 / 19 * (5776 / 5774)) else
      if p = 19 then 20 / 19 * (5776 / 5774) else
      if p = 7 then 8 / 7 * (2282 / 2280) else
      if p = 31 then 32 / 31 * (3968 / 3966) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (5776 / 5774)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (5776 / 5774) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (2282 / 2280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3966) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 5775 ≤ p := Q19f (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 37 (h ▸ hp) (by norm_num)
          omega)
        (fun h => by
          have := hs 151 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 5775) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 2281 ≤ p := Q7f (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun h => by
          have := hs 11 (S1 11 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 13 (S1 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 23 (S1 23 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 29 (S1 29 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 43 (S1 43 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 53 (S1 53 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 61 (S1 61 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 67 (S1 67 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 71 (S1 71 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 73 (S1 73 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 127 (S1 127 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 151 (S1 151 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (S4b 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun h => by
          have := hs 13 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h223 (h ▸ hp))
        (fun h => h433 (h ▸ hp))
        (fun h => h1063 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 2281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 3967 ≤ p := R31f (hP p hp).1 hd
        (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 61 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h991 (h ▸ hp))
      rw [b31]
      exact step_ge (t := 3967) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Core with 19 and 31, m at least 16, elements of P below 152 exactly 3, 5, 7, 19, 31, none of
-- 223, 433, 607, 1063 in P, and 991 in P: impossible.
theorem core19_31_b {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h223 : 223 ∉ P) (h433 : 433 ∉ P) (h607 : 607 ∉ P) (h1063 : 1063 ∉ P) (h991 : 991 ∈ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) else
      if p = 5 then 6 / 5 * (20 / 19 * (5776 / 5774)) else
      if p = 19 then 20 / 19 * (5776 / 5774) else
      if p = 7 then 8 / 7 * (2282 / 2280) else
      if p = 31 then 32 / 31 * (992 / 991 * (3964 / 3962)) else
      if p = 991 then 992 / 991 * (3964 / 3962) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (5776 / 5774)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (5776 / 5774) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (2282 / 2280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 991 * (3964 / 3962)) := by rw [hβ]; norm_num
  have b991 : β 991 = 992 / 991 * (3964 / 3962) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 31 → c ≠ 991 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e31 e991 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e31, if_neg e991, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e991 : p = 991
    · subst e991; rw [b991]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e31 e991 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 5775 ≤ p := Q19f (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 37 (h ▸ hp) (by norm_num)
          omega)
        (fun h => by
          have := hs 151 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 5775) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 2281 ≤ p := Q7f (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun h => by
          have := hs 11 (S1 11 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 13 (S1 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 23 (S1 23 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 29 (S1 29 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 43 (S1 43 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 53 (S1 53 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 61 (S1 61 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 67 (S1 67 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 71 (S1 71 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 73 (S1 73 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 127 (S1 127 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (fun h => by
          have := hs 151 (S1 151 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
          omega)
        (S4b 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun h => by
          have := hs 13 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h223 (h ▸ hp))
        (fun h => h433 (h ▸ hp))
        (fun h => h1063 (h ▸ hp))
      rw [b7]
      exact step_ge (t := 2281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 991 := S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 991 h991 hd (by norm_num)
      rw [b31, b991]; norm_num
    by_cases e991 : c = 991
    · subst e991
      have hge : 3963 ≤ p := R991 (hP p hp).1 hd
        (S4b 991 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b991]
      exact step_ge (t := 3963) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e31 e991 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Core with 19 and 31, m at least 16, elements of P below 152 exactly 3, 5, 7, 19, 31, and 1063
-- in P (the common parent of 7 and 19): impossible.
theorem core19_31_c {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h1063 : 1063 ∈ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19)) else
      if p = 5 then 6 / 5 * (20 / 19) else
      if p = 19 then 20 / 19 else
      if p = 7 then 8 / 7 * (1064 / 1063 * (4252 / 4250)) else
      if p = 1063 then 1064 / 1063 * (4252 / 4250) else
      if p = 31 then 32 / 31 * (992 / 990) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (1064 / 1063 * (4252 / 4250)) := by rw [hβ]; norm_num
  have b1063 : β 1063 = 1064 / 1063 * (4252 / 4250) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 990) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 1063 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e1063 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e1063, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e1063 : p = 1063
    · subst e1063; rw [b1063]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e1063 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 1063 := S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1063 h1063 hd (by norm_num)
      have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 1063 := S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1063 h1063 hd (by norm_num)
      rw [b7, b1063]; norm_num
    by_cases e1063 : c = 1063
    · subst e1063
      have hge : 4251 ≤ p := R1063 (hP p hp).1 hd
        (S4b 1063 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b1063]
      exact step_ge (t := 4251) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      by_cases e991 : p = 991
      · subst e991
        rw [b31, bd 991 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      have hge : 3967 ≤ p := R31f (hP p hp).1 hd
        (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 61 (h ▸ hp) (by norm_num)
          omega)
        e991
      rw [b31]
      exact step_ge (t := 3967) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e1063 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num


-- The core with 19, for the balance equation (E) with m at least 16 and exceptional primes at
-- least 2100: 31 is in P, the elements of P below 152 are exactly 3, 5, 7, 19, 31, and one of
-- 223, 433, 607 is in P.
theorem core_19 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h19 : 19 ∈ P) :
    31 ∈ P ∧ (∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) ∧
      (223 ∈ P ∨ 433 ∈ P ∨ 607 ∈ P) := by
  have hm10 : 10 ≤ m := by omega
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 5 h5 (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 5 h5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 19 h19 hd (by norm_num)
  have h13 : 13 ∉ P := fun hx => by
    have hsub : ({3, 5, 7, 13, 19} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact hx
      · exact h19
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  by_cases h31 : 31 ∈ P
  · have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := by
      intro q hq hlt
      by_contra hne
      have hsub : ({3, 5, 7, 19, 31} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h7
        · exact h19
        · exact h31
      have hqA : q ∉ ({3, 5, 7, 19, 31} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        intro hmem
        apply hne
        omega
      have hg := abund_gap hP hN hK hKK E hsub hq hqA
      have e1 : ∏ p ∈ ({3, 5, 7, 19, 31} : Finset ℕ), (p + 1) = 122880 := by decide
      have e2 : ∏ p ∈ ({3, 5, 7, 19, 31} : Finset ℕ), p = 61845 := by decide
      rw [e1, e2] at hg
      omega
    refine ⟨h31, hs, ?_⟩
    by_contra hno
    have h223 : 223 ∉ P := fun h => hno (Or.inl h)
    have h433 : 433 ∉ P := fun h => hno (Or.inr (Or.inl h))
    have h607 : 607 ∉ P := fun h => hno (Or.inr (Or.inr h))
    by_cases h1063 : 1063 ∈ P
    · exact core19_31_c hP hN hK hKK E hm hNb T3 T5 hs h1063
    · by_cases h991 : 991 ∈ P
      · exact core19_31_b hP hN hK hKK E hm hNb T3 T5 hs h223 h433 h607 h1063 h991
      · exact core19_31_a hP hN hK hKK E hm hNb T3 T5 hs h223 h433 h607 h991 h1063
  · by_cases h37 : 37 ∈ P
    · have h73 : 73 ∉ P := fun hx => by
        have hsub : ({3, 5, 7, 19, 37, 73} : Finset ℕ) ⊆ P := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
          · exact h3
          · exact h5
          · exact h7
          · exact h19
          · exact h37
          · exact hx
        have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
        revert h
        decide
      have h127 : 127 ∈ P := by
        by_contra h127
        exact core19_C hP hN hK hKK E hm10 hNb T3 T5 h13 h31 h37 h73 h127
      refine (core19_C16 hP hN hK hKK E hm hNb T3 T5 h37 ?_).elim
      intro q hq hlt
      by_contra hne
      have hsub : ({3, 5, 7, 19, 37, 127} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h7
        · exact h19
        · exact h37
        · exact h127
      have hqA : q ∉ ({3, 5, 7, 19, 37, 127} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        intro hmem
        apply hne
        omega
      have hg := abund_gap hP hN hK hKK E hsub hq hqA
      have e1 : ∏ p ∈ ({3, 5, 7, 19, 37, 127} : Finset ℕ), (p + 1) = 18677760 := by decide
      have e2 : ∏ p ∈ ({3, 5, 7, 19, 37, 127} : Finset ℕ), p = 9374505 := by decide
      rw [e1, e2] at hg
      omega
    · exact (core19_A hP hN hK hKK E hm10 T3 T5 h13 h31 h37).elim


-- Every prime of an admissible set is at least 2100.
theorem adm_ge_2100 {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097) :
    ∀ z ∈ N, 2100 ≤ z := by
  intro z hz
  have hNq : ∀ w ∈ N, (N.card : ℚ) + 3 ≤ w := fun w hw => by exact_mod_cast (hN w hw).2.2
  have h1 : ∀ w ∈ N, (1 : ℚ) ≤ ((w : ℚ) + 1) / ((w : ℚ) - 2 - (N.card : ℚ)) := fun w hw => by
    have := hNq w hw
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hle : ((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ)) ≤
      ∏ w ∈ N, (((w : ℚ) + 1) / ((w : ℚ) - 2 - (N.card : ℚ))) := by
    have := Finset.prod_le_prod_of_subset_of_one_le (f := fun w : ℕ =>
      ((w : ℚ) + 1) / ((w : ℚ) - 2 - (N.card : ℚ))) (Finset.singleton_subset_iff.mpr hz)
      (fun w hw => by
        rw [Finset.mem_singleton] at hw
        subst hw
        exact le_trans zero_le_one (h1 w hz))
      (fun w hw _ => h1 w hw)
    rwa [Finset.prod_singleton] at this
  have hc1 : (1 : ℚ) ≤ (N.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩
  have hzq := hNq z hz
  have h2 := hle.trans hΛ
  rw [div_le_iff₀ (by linarith)] at h2
  have h3 : (2100 : ℚ) ≤ z := by linarith
  exact_mod_cast h3

-- 17 divides 2^m + 1 when m = 4 mod 8.
theorem dvd_17 {m : ℕ} (h : m % 8 = 4) : 17 ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 8 * k + 4 := ⟨m / 8, by omega⟩
  have h1 : (2 ^ 8) ^ k % 17 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [pow_add, pow_mul]
  omega

-- 257 divides 2^m + 1 when m = 8 mod 16.
theorem dvd_257 {m : ℕ} (h : m % 16 = 8) : 257 ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 16 * k + 8 := ⟨m / 16, by omega⟩
  have h1 : (2 ^ 16) ^ k % 257 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [pow_add, pow_mul]
  omega

-- 641 divides 2^m + 1 when m = 32 mod 64.
theorem dvd_641 {m : ℕ} (h : m % 64 = 32) : 641 ∣ 2 ^ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 64 * k + 32 := ⟨m / 64, by omega⟩
  have h1 : (2 ^ 64) ^ k % 641 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [pow_add, pow_mul]
  omega

-- In the balance equation (E) with exceptional primes at least 2100, with 5 in P and 4 ∣ m:
-- 16 ∣ m and m is not 32 mod 64.  (17, 257 and 641 would be simple primes p with 3 ∣ p + 1.)
theorem core_two_adic {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h5 : 5 ∈ P) (h4 : 4 ∣ m) : 16 ∣ m ∧ m % 64 ≠ 32 := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 5 h5 hd (by norm_num)
  have a8 : m % 8 ≠ 4 := fun h => by
    have := T3 17 (S5 17 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) (dvd_17 h))
      (by norm_num)
    omega
  have a16 : m % 16 ≠ 8 := fun h => by
    have := T3 257 (S5 257 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (dvd_257 h))
      (by norm_num)
    omega
  have a64 : m % 64 ≠ 32 := fun h => by
    have := T3 641 (S5 641 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (dvd_641 h))
      (by norm_num)
    omega
  exact ⟨by omega, a64⟩

-- The balance equation (E) of a unitary perfect number, for an admissible set N outside which
-- every odd prime of n is simple; P is the set of odd primes of n outside N.
theorem exists_balance {n : ℕ} {N : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1) (h2 : 2 ∣ n) :
    ∃ (K K' : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) ∧
      (K ≤ K' ∧
        (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097) ∧
      ((2 ^ padicValNat 2 n + 1) * K' * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * K * ∏ p ∈ P, p) ∧
      (∀ q, q ∈ P ↔ q.Prime ∧ q ≠ 2 ∧ q ∣ n ∧ q ∉ N) := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  have E := kernel_balance h h2 hs
  rw [hfac] at E
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N), p.Prime ∧ p ≠ 2 :=
    fun p hp => by
      have h1 := (Finset.mem_filter.mp hp).1
      exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  have hMmem : ∀ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
      z.Prime ∧ z ∈ N ∧ 1 ≤ n.factorization z := fun z hz => by
    obtain ⟨h1, hzN⟩ := Finset.mem_filter.mp hz
    have hzpf := Finset.mem_of_mem_erase h1
    exact ⟨Nat.prime_of_mem_primeFactors hzpf, hzN,
      (Nat.prime_of_mem_primeFactors hzpf).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors hzpf)⟩
  have hK : ∀ c : ℕ, c.Prime →
      c ∣ ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z →
      c ∈ N := fun c hc hd => by
    obtain ⟨z, hz, hcz⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp hd
    obtain ⟨hzp, hzN, _⟩ := hMmem z hz
    rw [(Nat.prime_dvd_prime_iff_eq hc hzp).mp (hc.dvd_of_dvd_pow hcz)]
    exact hzN
  have hK1 : ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z ≤
      ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), (1 + z ^ n.factorization z) :=
    Finset.prod_le_prod' fun z _ => Nat.le_add_left _ _
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hNq : ∀ z ∈ N, (N.card : ℚ) + 3 ≤ z := fun z hz => by exact_mod_cast (hN z hz).2.2
  have hK2 : ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
        (1 + z ^ n.factorization z) : ℕ) : ℚ) /
      ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z : ℕ) : ℚ) *
      ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 := by
    have hΛ0 : (0 : ℚ) ≤ ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
      Finset.prod_nonneg fun z hz => by
        have := hNq z hz
        exact div_nonneg (by linarith) (by linarith)
    have hratio : ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N),
          (1 + z ^ n.factorization z) : ℕ) : ℚ) /
        ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ N), z ^ n.factorization z : ℕ) : ℚ) ≤
        ∏ z ∈ N, (1 + 1 / (z : ℚ)) := by
      push_cast
      rw [← Finset.prod_div_distrib]
      refine (Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)).trans
        (Finset.prod_le_prod_of_subset_of_one_le (fun z hz => (hMmem z hz).2.1)
          (fun z _ => by positivity)
          (fun z _ _ => by
            have : (0 : ℚ) ≤ 1 / (z : ℚ) := by positivity
            linarith))
      · positivity
      · obtain ⟨hzp, hzN, he⟩ := hMmem z hz
        have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hzp.one_lt.le
        have hpow : (z : ℚ) ≤ (z : ℚ) ^ n.factorization z := by
          calc (z : ℚ) = (z : ℚ) ^ 1 := (pow_one _).symm
            _ ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ hz1 he
        have hzpos : (0 : ℚ) < z := by linarith
        rw [div_le_iff₀ (by linarith)]
        have : 1 / (z : ℚ) * (z : ℚ) ^ n.factorization z ≥ 1 := by
          rw [ge_iff_le, one_div, ← div_eq_inv_mul, le_div_iff₀ hzpos]
          linarith
        nlinarith
    calc _ ≤ (∏ z ∈ N, (1 + 1 / (z : ℚ))) * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) :=
          mul_le_mul_of_nonneg_right hratio hΛ0
      _ = ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun z hz => ?_
          have := hNq z hz
          have hzpos : (z : ℚ) ≠ 0 := by linarith
          have hden : (z : ℚ) - 2 - (N.card : ℚ) ≠ 0 := by linarith
          field_simp
      _ ≤ 2101 / 2097 := hΛ
  refine ⟨_, _, _, hP, hK, ⟨hK1, hK2⟩, E, fun q => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hq2, hqp, hqn, _⟩, hqN⟩
    exact ⟨hqp, hq2, hqn, hqN⟩
  · rintro ⟨hqp, hq2, hqn, hqN⟩
    exact ⟨⟨hq2, hqp, hqn, hn0⟩, hqN⟩

-- The same for N = S, the set of non-simple odd primes, when S is admissible.
theorem core_setup {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) (h2 : 2 ∣ n) :
    (∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z) ∧ (∀ z ∈ S, 2100 ≤ z) ∧
    ∃ (K K' : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (∀ c : ℕ, c.Prime → c ∣ K → c ∈ S) ∧
      (K ≤ K' ∧
        (K' : ℚ) / K * ∏ z ∈ S, ((z : ℚ) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) ∧
      ((2 ^ padicValNat 2 n + 1) * K' * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * K * ∏ p ∈ P, p) ∧
      (∀ q, q ∈ P ↔ q.Prime ∧ q ≠ 2 ∧ q ∣ n ∧ q ∉ S) := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ S → n.factorization r = 1 := by
    intro r hr hr2 hrN
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hrN ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  exact ⟨hNS, adm_ge_2100 hNS hadm2, exists_balance h hNS hadm2 hs h2⟩

-- In the 5-chain core the 2-adic valuation a satisfies 16 ∣ a and a is not 32 mod 64.
theorem two_adic_core {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h5 : 5 ∣ n) (h4 : 4 ∣ padicValNat 2 n) :
    16 ∣ padicValNat 2 n ∧ padicValNat 2 n % 64 ≠ 32 := by
  by_cases h0 : padicValNat 2 n = 0
  · rw [h0]; exact ⟨dvd_zero _, by norm_num⟩
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  obtain ⟨hNS, hNb, K, K', P, hP, hK, hKK, E, hmem⟩ := core_setup h hS hadm1 hadm2 h2
  exact core_two_adic hP hNS hK E hNb ((hmem 5).mpr ⟨by norm_num, by norm_num, h5, big_notMem hNb (by norm_num)⟩) h4

-- Core with 19 (step H1 of the parent reduction): n unitary perfect, S (the non-simple odd primes)
-- admissible, 5, 7, 19 divide n and 4 divides a.  Then a ≤ 9, or 31 ∣ n, the primes of n
-- below 152 are exactly 2, 3, 5, 7, 19, 31, and one of 223, 433, 607 divides n.
theorem core_with_19 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h4 : 4 ∣ padicValNat 2 n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) :
    padicValNat 2 n ≤ 9 ∨
    (31 ∣ n ∧
      (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) ∧
      (223 ∣ n ∨ 433 ∣ n ∨ 607 ∣ n)) := by
  by_cases hm : padicValNat 2 n ≤ 9
  · exact Or.inl hm
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  obtain ⟨hNS, hNb, K, K', P, hP, hK, hKK, E, hmem⟩ := core_setup h hS hadm1 hadm2 h2
  have m5 : 5 ∈ P := (hmem 5).mpr ⟨by norm_num, by norm_num, h5, big_notMem hNb (by norm_num)⟩
  have h16 := (core_two_adic hP hNS hK E hNb m5 h4).1
  obtain ⟨a, hall, h6⟩ := core_19 hP hNS hK hKK E (by omega) hNb m5
    ((hmem 7).mpr ⟨by norm_num, by norm_num, h7, big_notMem hNb (by norm_num)⟩)
    ((hmem 19).mpr ⟨by norm_num, by norm_num, h19, big_notMem hNb (by norm_num)⟩)
  exact Or.inr ⟨((hmem 31).mp a).2.2.1, (fun q hqp hqn hlt => by
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · exact Or.inr (hall q ((hmem q).mpr ⟨hqp, hq2, hqn, big_notMem hNb (by omega)⟩) hlt)),
    h6.imp (fun h => ((hmem 223).mp h).2.2.1)
      (Or.imp (fun h => ((hmem 433).mp h).2.2.1) (fun h => ((hmem 607).mp h).2.2.1))⟩

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3'⟩
  refine ⟨max (max (max A1 A2) A3) 9, fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall => ?_⟩
  obtain ⟨h16, h64⟩ := two_adic_core h hS hadm1 hadm2 h5 h4
  rcases core_with_19 h hS hadm1 hadm2 h4 h5 h7 h19 with h9 | ⟨a, b, c | c | c⟩
  · exact h9.trans (le_max_right _ _)
  · exact (h1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall h16 h64 a b c).trans
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  · exact (h2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall h16 h64 a b c).trans
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  · exact (h3' n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall h16 h64 a b c).trans
      ((le_max_right _ _).trans (le_max_left _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1
