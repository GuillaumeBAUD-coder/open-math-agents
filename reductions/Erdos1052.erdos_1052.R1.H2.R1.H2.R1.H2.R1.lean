import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H2.R1
-- Shrinks step H2 (the 5-chain core without 19) of Erdos1052.erdos_1052.R1.H2.R1.H2.R1 and splits it
-- in two.  Proving all two H proves the step.
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
--   core_without_19: let S be admissible, 4 | a, 5 and 7 divide n, 19 does not, and some prime p
--     of n outside S has 5 | p + 1.  Then a <= 9, or 79 | n, 13 | n, the primes of n below 342 are
--     exactly 2, 3, 5, 7, 13, 79, and 631 | n or 1663 | n.
--     None of the residue conditions of the parent step are used.
--     Method: 5 is the parent of 3; let p0 be the parent of 5.  The weight argument (master, and
--     master16 in the last three cases) bounds p0 in every case:
--       13 does not divide n: p0 < 415;      13 divides n, 103 does not: p0 < 661;
--       13, 103 divide n, 823 does not: p0 < 862;      13, 103, 823 divide n: p0 < 1592.
--     A prime p0 < 1592 with 5 | p0 + 1 that is not 19 and passes the divisibility conditions of
--     the family is one of 79, 139, 619, 1039, 1279 (par5_cands).  139 is excluded by weights;
--     619 forces 31 | n, which is abundant with 3, 5, 7, 13; 1039 would be a second parent of 13;
--     79 without 13 is excluded by weights; 1279 (with 13, 103, 823) is excluded by master16.
--     With p0 = 79 and 13 | n every further prime is at least 342, and master16 excludes
--       none of 631, 1663, 2053 divides n: parent of 79 at least 10111, of 13 at least 8891;
--       2053 | n: 2053 is the parent of 13 and of 79 and its parent is at least 131391.
--
-- H1 (OPEN): the step restricted to 16 | a, a not 32 mod 64, 79 | n, 13 | n, primes of n below 342
--    exactly 2, 3, 5, 7, 13, 79, and 631 | n (631 is then the parent of 79).
-- H2 (OPEN): the same with 1663 | n (1663 is then the parent of 13).
-- Neither can be closed by the weight inequality alone.  The products of 1 + 1/p over
--   3, 5, 7, 13, 79, 631 (1.997318) and over 3, 5, 7, 13, 79, 1663 (1.995357) lie in the window
-- [1.995187, 2) that the inequality cannot exclude (computed with exact fractions outside Lean;
-- these are configurations of small primes, not unitary perfect numbers).  No known unitary
-- perfect number is in either family.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H2_R1

-- The 2-adic valuation is bounded over the family of step H2 of the parent file restricted to
-- 16 | a, a not 32 mod 64, 79 | n, 13 | n, no prime of n below 342 other than 2, 3, 5, 7, 13, 79,
-- and 631 | n.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → ¬ 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      (∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) ∧
      ∃ p, p.Prime ∧ p ∣ n ∧ p ∉ N ∧ 5 ∣ p + 1) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    79 ∣ n → 13 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 342 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79) →
    631 ∣ n →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H2 of the parent file restricted to
-- 16 | a, a not 32 mod 64, 79 | n, 13 | n, no prime of n below 342 other than 2, 3, 5, 7, 13, 79,
-- and 1663 | n.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → ¬ 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      (∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) ∧
      ∃ p, p.Prime ∧ p ∣ n ∧ p ∉ N ∧ 5 ∣ p + 1) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    79 ∣ n → 13 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 342 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79) →
    1663 ∣ n →
    padicValNat 2 n ≤ A

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1 hiding H1 H2 main

-- A set of primes that is at least 2100 does not contain a number below 2100.
theorem big_notMem {N : Finset ℕ} (hNb : ∀ z ∈ N, 2100 ≤ z) {c : ℕ} (hc : c < 2100) : c ∉ N :=
  fun h => by
    have := hNb c h
    omega

-- A prime p ≠ 823 whose least odd child is 103 is at least 13183.
theorem R103b {p : ℕ} (hp : p.Prime) (hd : 103 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 103 ≤ c') (hne : p ≠ 823) : 13183 ≤ p := by
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

-- A prime whose least odd child is 823 is at least 1354657.
set_option maxHeartbeats 2000000 in
theorem R823 {p : ℕ} (hp : p.Prime) (hd : 823 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 823 ≤ c') : 1354657 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 11 := by
      by_contra hcon
      have : 2 ^ 11 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp
  · omega

-- Graham sub-case (ii) with a parent of 5 that is at least 415: 13 is not in P.
theorem par5_ii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (H5 : ∀ p ∈ P, 5 ∣ p + 1 → 415 ≤ p)
    (h13 : 13 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (416 / 414)) else
      if p = 5 then 6 / 5 * (416 / 414) else
      if p = 7 then 8 / 7 * (224 / 222) else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (416 / 414)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (416 / 414) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      have hge : 415 ≤ p := H5 p hp hd
      rw [b5]
      exact step_ge (t := 415) (by norm_num) hge (hB p hp).2 (by norm_num)
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
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Graham sub-case (iii) with a parent of 5 that is at least 661: 13 in P, 103 not in P.
theorem par5_iii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (h5 : 5 ∈ P) (h3 : 3 ∈ P) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (H5 : ∀ p ∈ P, 5 ∣ p + 1 → 661 ≤ p)
    (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h103 : 103 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  have h17 : 17 ∉ P := fun h => by
    have := T3 17 h (by norm_num)
    omega
  have h43 : 43 ∉ P := fun h => h11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 43 h (by norm_num))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (662 / 660)) else
      if p = 5 then 6 / 5 * (662 / 660) else
      if p = 7 then 8 / 7 * (14 / 13 * (1664 / 1662)) else
      if p = 13 then 14 / 13 * (1664 / 1662) else
      if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (662 / 660)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (662 / 660) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (1664 / 1662)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (1664 / 1662) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e13 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      have hge : 661 ≤ p := H5 p hp hd
      rw [b5]
      exact step_ge (t := 661) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      have hge : 1663 ≤ p := R13 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => h17 (S1 17 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (fun h => h43 (S1 43 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp h))
        (S4b 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp)
        (fun h => h103 (h ▸ hp))
      rw [b13]
      exact step_ge (t := 1663) (by norm_num) hge (hB p hp).2 (by norm_num)
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
    exact absurd (bd c e3 e5 e7 e13 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Graham sub-case (iv) with a parent of 5 that is at least 862, when 823 (the only chain parent
-- of 103 below 13183) is not in P.
theorem par5_ivb {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (h5 : 5 ∈ P) (h3 : 3 ∈ P) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (H5 : ∀ p ∈ P, 5 ∣ p + 1 → 862 ≤ p)
    (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h103 : 103 ∈ P) (h823 : 823 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (863 / 861)) else
      if p = 5 then 6 / 5 * (863 / 861) else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (13184 / 13182))) else
      if p = 13 then 14 / 13 * (104 / 103 * (13184 / 13182)) else
      if p = 103 then 104 / 103 * (13184 / 13182) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (863 / 861)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (863 / 861) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (13184 / 13182))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (13184 / 13182)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (13184 / 13182) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      have hge : 862 ≤ p := H5 p hp hd
      rw [b5]
      exact step_ge (t := 862) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      have hge : 13183 ≤ p := R103b (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
        (fun h => h823 (h ▸ hp))
      rw [b103]
      exact step_ge (t := 13183) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Graham sub-case (iv) with a parent of 5 that is at least 1592, when 823 is in P.
theorem par5_iva {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h5 : 5 ∈ P) (h3 : 3 ∈ P) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (H5 : ∀ p ∈ P, 5 ∣ p + 1 → 1592 ≤ p)
    (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h103 : 103 ∈ P) (h823 : 823 ∈ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (1593 / 1591)) else
      if p = 5 then 6 / 5 * (1593 / 1591) else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656)))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656))) else
      if p = 103 then 104 / 103 * (824 / 823 * (1354658 / 1354656)) else
      if p = 823 then 824 / 823 * (1354658 / 1354656) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (1593 / 1591)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (1593 / 1591) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656)))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656))) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 823 * (1354658 / 1354656)) := by rw [hβ]; norm_num
  have b823 : β 823 = 824 / 823 * (1354658 / 1354656) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 823 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e823 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e823, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e823 : p = 823
    · subst e823; rw [b823]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e823 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      have hge : 1592 ≤ p := H5 p hp hd
      rw [b5]
      exact step_ge (t := 1592) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      obtain rfl : p = 823 := S2 103 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 823 h823 hd (by norm_num)
      rw [b103, b823]; norm_num
    by_cases e823 : c = 823
    · subst e823
      have hge : 1354657 ≤ p := R823 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b823]
      exact step_ge (t := 1354657) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e823 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 5 is not 139: then 7 ∣ 139 + 1 as well, so 7 is a leaf of weight exactly 8/7.
theorem par5_139 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (h139 : 139 ∈ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (140 / 138)) else
      if p = 5 then 6 / 5 * (140 / 138) else
      if p = 7 then 8 / 7 else
      if p = 31 then 32 / 31 * (62 / 61 * (488 / 486)) else
      if p = 61 then 62 / 61 * (488 / 486) else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (140 / 138)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (140 / 138) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (62 / 61 * (488 / 486)) := by rw [hβ]; norm_num
  have b61 : β 61 = 62 / 61 * (488 / 486) := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 31 → c ≠ 61 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e31 e61 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e31, if_neg e61, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e61 : p = 61
    · subst e61; rw [b61]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e7 e31 e61 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 139 := S2 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 139 h139 hd (by norm_num)
      rw [b5, bd 139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 139 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 139 h139 hd (by norm_num)
      have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) (by norm_num)
      omega
    by_cases e31 : c = 31
    · subst e31
      by_cases e : p = 61
      · subst e; rw [b31, b61]; norm_num
      have hge : 991 ≤ p := Q31 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        e
      rw [b31]
      exact step_ge (t := 991) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e61 : c = 61
    · subst e61
      have hge : 487 ≤ p := Q61 (hP p hp).1 hd
      rw [b61]
      exact step_ge (t := 487) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e7 e31 e61 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num


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

-- A prime p ≠ 157 with 79 ∣ p + 1 is at least 631.
theorem Q79 {p : ℕ} (hp : p.Prime) (hd : 79 ∣ p + 1) (hne : p ≠ 157) :
    631 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 158 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 158 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 487 with 61 ∣ p + 1 and none of 3, 5, 7 dividing p + 1 is at least 975.
theorem Q61b {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h7 : ¬ 7 ∣ p + 1)
    (hne : p ≠ 487) :
    975 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 122 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 8 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 122 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 313 whose least odd child is 157 is at least 5023.
theorem R157b {p : ℕ} (hp : p.Prime) (hd : 157 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 157 ≤ c') (hne : p ≠ 313) : 5023 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 5 := by
      by_contra hcon
      have : 2 ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime whose least odd child is 313 is at least 2503.
theorem R313 {p : ℕ} (hp : p.Prime) (hd : 313 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 313 ≤ c') : 2503 ≤ p := by
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

-- A prime p ≠ 1783 whose least odd child is 223 is at least 3567.
theorem R223b {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 223 ≤ c') (hne : p ≠ 1783) : 3567 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 4 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- A prime whose least odd child is 1783 is at least 28527.
set_option maxHeartbeats 2000000 in
theorem R1783 {p : ℕ} (hp : p.Prime) (hd : 1783 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 1783 ≤ c') : 28527 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 4 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp
  · omega

-- A prime whose least odd child is 487 is at least 15583.
theorem R487 {p : ℕ} (hp : p.Prime) (hd : 487 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∣ p + 1 → 487 ≤ c') : 15583 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases (by omega) h2 (by norm_num) (by norm_num) hd hmin with ⟨i, hi⟩ | h
  · have hi8 : i < 5 := by
      by_contra hcon
      have : 2 ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp
  · omega

-- The parent of 5 is 79 and 13 is not in P: impossible.  Every chain is taken at its largest
-- possible weight: 79, 157, 313; 7, 223, 1783; 31, 61, 487; 127.
theorem par5_79_no13 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (h79 : 79 ∈ P) (h13 : 13 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502))))) else
      if p = 5 then 6 / 5 * (80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502)))) else
      if p = 79 then 80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502))) else
      if p = 157 then 158 / 157 * (314 / 313 * (2504 / 2502)) else
      if p = 313 then 314 / 313 * (2504 / 2502) else
      if p = 7 then 8 / 7 * (224 / 223 * (1784 / 1783 * (28528 / 28526))) else
      if p = 223 then 224 / 223 * (1784 / 1783 * (28528 / 28526)) else
      if p = 1783 then 1784 / 1783 * (28528 / 28526) else
      if p = 31 then 32 / 31 * (62 / 61 * (488 / 487 * (15584 / 15582))) else
      if p = 61 then 62 / 61 * (488 / 487 * (15584 / 15582)) else
      if p = 487 then 488 / 487 * (15584 / 15582) else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502)))) := by rw [hβ]; norm_num
  have b79 : β 79 = 80 / 79 * (158 / 157 * (314 / 313 * (2504 / 2502))) := by rw [hβ]; norm_num
  have b157 : β 157 = 158 / 157 * (314 / 313 * (2504 / 2502)) := by rw [hβ]; norm_num
  have b313 : β 313 = 314 / 313 * (2504 / 2502) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1784 / 1783 * (28528 / 28526))) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1784 / 1783 * (28528 / 28526)) := by rw [hβ]; norm_num
  have b1783 : β 1783 = 1784 / 1783 * (28528 / 28526) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (62 / 61 * (488 / 487 * (15584 / 15582))) := by rw [hβ]; norm_num
  have b61 : β 61 = 62 / 61 * (488 / 487 * (15584 / 15582)) := by rw [hβ]; norm_num
  have b487 : β 487 = 488 / 487 * (15584 / 15582) := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 79 → c ≠ 157 → c ≠ 313 → c ≠ 7 → c ≠ 223 → c ≠ 1783 → c ≠ 31 → c ≠ 61 → c ≠ 487 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e79 e157 e313 e7 e223 e1783 e31 e61 e487 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e79, if_neg e157, if_neg e313, if_neg e7, if_neg e223, if_neg e1783, if_neg e31, if_neg e61, if_neg e487, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e79 : p = 79
    · subst e79; rw [b79]; norm_num
    by_cases e157 : p = 157
    · subst e157; rw [b157]; norm_num
    by_cases e313 : p = 313
    · subst e313; rw [b313]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e1783 : p = 1783
    · subst e1783; rw [b1783]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e61 : p = 61
    · subst e61; rw [b61]; norm_num
    by_cases e487 : p = 487
    · subst e487; rw [b487]; norm_num
    by_cases e127 : p = 127
    · subst e127; rw [b127]; norm_num
    rw [bd p e3 e5 e79 e157 e313 e7 e223 e1783 e31 e61 e487 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 79 := S2 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 79 h79 hd (by norm_num)
      rw [b5, b79]; norm_num
    by_cases e79 : c = 79
    · subst e79
      by_cases e : p = 157
      · subst e; rw [b79, b157]; norm_num
      have hge : 631 ≤ p := Q79 (hP p hp).1 hd e
      rw [b79]
      exact step_ge (t := 631) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e157 : c = 157
    · subst e157
      by_cases e : p = 313
      · subst e; rw [b157, b313]; norm_num
      have hge : 5023 ≤ p := R157b (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
        e
      rw [b157]
      exact step_ge (t := 5023) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e313 : c = 313
    · subst e313
      have hge : 2503 ≤ p := R313 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b313]
      exact step_ge (t := 2503) (by norm_num) hge (hB p hp).2 (by norm_num)
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
      by_cases e : p = 1783
      · subst e; rw [b223, b1783]; norm_num
      have hge : 3567 ≤ p := R223b (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
        e
      rw [b223]
      exact step_ge (t := 3567) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e1783 : c = 1783
    · subst e1783
      have hge : 28527 ≤ p := R1783 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b1783]
      exact step_ge (t := 28527) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      by_cases e : p = 61
      · subst e; rw [b31, b61]; norm_num
      have hge : 991 ≤ p := Q31 (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        e
      rw [b31]
      exact step_ge (t := 991) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e61 : c = 61
    · subst e61
      by_cases e : p = 487
      · subst e; rw [b61, b487]; norm_num
      have hge : 975 ≤ p := Q61b (hP p hp).1 hd
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        e
      rw [b61]
      exact step_ge (t := 975) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e487 : c = 487
    · subst e487
      have hge : 15583 ≤ p := R487 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b487]
      exact step_ge (t := 15583) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      have hge : 32257 ≤ p := R127 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b127]
      exact step_ge (t := 32257) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e5 e79 e157 e313 e7 e223 e1783 e31 e61 e487 e127) hne
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

-- For m at least 16 the parent of 5 is not 1279 (with 13, 103, 823 in P).
theorem par5_1279_16 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h5 : 5 ∈ P) (h3 : 3 ∈ P) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5)
    (h7 : 7 ∈ P) (h13 : 13 ∈ P) (h103 : 103 ∈ P) (h823 : 823 ∈ P) (h1279 : 1279 ∈ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := by
    intro h31
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h127 : 127 ∉ P := by
    intro h127
    have hsub : ({3, 5, 7, 13, 103, 127} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h103
      · exact h127
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (1280 / 1278)) else
      if p = 5 then 6 / 5 * (1280 / 1278) else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656)))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656))) else
      if p = 103 then 104 / 103 * (824 / 823 * (1354658 / 1354656)) else
      if p = 823 then 824 / 823 * (1354658 / 1354656) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (1280 / 1278)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (1280 / 1278) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656)))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 823 * (1354658 / 1354656))) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 823 * (1354658 / 1354656)) := by rw [hβ]; norm_num
  have b823 : β 823 = 824 / 823 * (1354658 / 1354656) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 823 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e13 e103 e823 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e13, if_neg e103, if_neg e823, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e823 : p = 823
    · subst e823; rw [b823]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e7 e13 e103 e823 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 1279 := S2 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 1279 h1279 hd (by norm_num)
      rw [b5, bd 1279 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 103 := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 103 h103 hd (by norm_num)
      rw [b13, b103]; norm_num
    by_cases e103 : c = 103
    · subst e103
      obtain rfl : p = 823 := S2 103 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 823 h823 hd (by norm_num)
      rw [b103, b823]; norm_num
    by_cases e823 : c = 823
    · subst e823
      have hge : 1354657 ≤ p := R823 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b823]
      exact step_ge (t := 1354657) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e823 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- A prime p other than 157 and 631 with 79 dividing p + 1 exactly once and every other odd prime
-- factor of p + 1 at least 342 is at least 10111.
theorem R79c {p : ℕ} (hp : p.Prime) (hd : 79 ∣ p + 1) (hsq : ¬ 79 * 79 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 79 → c' ∣ p + 1 → 342 ≤ c')
    (h157 : p ≠ 157) (h631 : p ≠ 631) : 10111 ≤ p := by
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

-- A prime p other than 103, 1663, 2053 with 13 dividing p + 1 exactly once and every other odd
-- prime factor of p + 1 either 79 or at least 342 is at least 8891.
theorem Q13c {p : ℕ} (hp : p.Prime) (hd : 13 ∣ p + 1) (hsq : ¬ 13 * 13 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 13 → c' ∣ p + 1 → c' = 79 ∨ 342 ≤ c')
    (h103 : p ≠ 103) (h1663 : p ≠ 1663) (h2053 : p ≠ 2053) : 8891 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  by_cases h79 : 79 ∣ p + 1
  · obtain ⟨j, hj⟩ : 13 * 79 ∣ p + 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd h79
    have hj9 : j < 9 := by omega
    interval_cases j <;> first | (exfalso; omega) |
      (norm_num at hj <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hj) <;> norm_num at hp)
  · rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq
      (fun c' h1 h2' h3 h4 => by
        rcases hmin c' h1 h2' h3 h4 with rfl | h
        · exact absurd h4 h79
        · exact h) with ⟨i, hi⟩ | h
    · have hi10 : i < 10 := by
        by_contra hcon
        have : 2 ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases i <;> first | (exfalso; omega) |
        (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
    · omega

-- A prime p with 2053 dividing p + 1 exactly once and every other odd prime factor of p + 1 at
-- least 2053 is at least 131391.
set_option maxHeartbeats 2000000 in
theorem R2053c {p : ℕ} (hp : p.Prime) (hd : 2053 ∣ p + 1) (hsq : ¬ 2053 * 2053 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ≠ 2053 → c' ∣ p + 1 → 2053 ≤ c') : 131391 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  rcases child_cases_c (by omega) h2 (by norm_num) (by norm_num) hd hsq hmin with ⟨i, hi⟩ | h
  · have hi6 : i < 6 := by
      by_contra hcon
      have : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases i <;> first | (exfalso; omega) |
      (norm_num at hi <;> (obtain rfl : p = _ := Nat.eq_sub_of_add_eq hi) <;> norm_num at hp)
  · omega

-- Core without 19, parent of 5 equal to 79, m at least 16, elements of P below 342 exactly
-- 3, 5, 7, 13, 79, and none of 631, 1663, 2053 in P: impossible.
theorem par5_79_A {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (h79 : 79 ∈ P) (h13 : 13 ∈ P)
    (hs : ∀ q ∈ P, q < 342 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79)
    (h631 : 631 ∉ P) (h1663 : 1663 ∉ P) (h2053 : 2053 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := fun h => by
    have := hs 31 h (by norm_num)
    omega
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (80 / 79 * (10112 / 10110))) else
      if p = 5 then 6 / 5 * (80 / 79 * (10112 / 10110)) else
      if p = 79 then 80 / 79 * (10112 / 10110) else
      if p = 7 then 8 / 7 * (14 / 13 * (8892 / 8890)) else
      if p = 13 then 14 / 13 * (8892 / 8890) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (80 / 79 * (10112 / 10110))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (80 / 79 * (10112 / 10110)) := by rw [hβ]; norm_num
  have b79 : β 79 = 80 / 79 * (10112 / 10110) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (8892 / 8890)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (8892 / 8890) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 79 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e79 e7 e13 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e79, if_neg e7, if_neg e13, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e79 : p = 79
    · subst e79; rw [b79]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e79 e7 e13 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 79 := S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 79 h79 hd (by norm_num)
      rw [b5, b79]; norm_num
    by_cases e79 : c = 79
    · subst e79
      have hge : 10111 ≤ p := R79c (hP p hp).1 hd
        (S4b 79 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hlt
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 157 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h631 (h ▸ hp))
      rw [b79]
      exact step_ge (t := 10111) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      have hge : 8891 ≤ p := Q13c (hP p hp).1 hd
        (S4b 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 103 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h1663 (h ▸ hp))
        (fun h => h2053 (h ▸ hp))
      rw [b13]
      exact step_ge (t := 8891) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e79 e7 e13 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Core without 19, parent of 5 equal to 79, m at least 16, elements of P below 342 exactly
-- 3, 5, 7, 13, 79, and 2053 in P (the common parent of 13 and 79): impossible.
theorem par5_79_B {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (h79 : 79 ∈ P) (h13 : 13 ∈ P)
    (hs : ∀ q ∈ P, q < 342 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79)
    (h2053 : 2053 ∈ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h31 : 31 ∉ P := fun h => by
    have := hs 31 h (by norm_num)
    omega
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (80 / 79)) else
      if p = 5 then 6 / 5 * (80 / 79) else
      if p = 79 then 80 / 79 else
      if p = 7 then 8 / 7 * (14 / 13 * (2054 / 2053 * (131392 / 131390))) else
      if p = 13 then 14 / 13 * (2054 / 2053 * (131392 / 131390)) else
      if p = 2053 then 2054 / 2053 * (131392 / 131390) else
      if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (80 / 79)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (80 / 79) := by rw [hβ]; norm_num
  have b79 : β 79 = 80 / 79 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (2054 / 2053 * (131392 / 131390))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (2054 / 2053 * (131392 / 131390)) := by rw [hβ]; norm_num
  have b2053 : β 2053 = 2054 / 2053 * (131392 / 131390) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 79 → c ≠ 7 → c ≠ 13 → c ≠ 2053 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e79 e7 e13 e2053 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e79, if_neg e7, if_neg e13, if_neg e2053, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e79 : p = 79
    · subst e79; rw [b79]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e2053 : p = 2053
    · subst e2053; rw [b2053]; norm_num
    by_cases e31 : p = 31
    · subst e31; exact absurd hp h31
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e79 e7 e13 e2053 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master16 hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 79 := S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 79 h79 hd (by norm_num)
      rw [b5, b79]; norm_num
    by_cases e79 : c = 79
    · subst e79
      obtain rfl : p = 2053 := S2 79 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 2053 h2053 hd (by norm_num)
      have := hmin 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 13 := S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 13 h13 hd (by norm_num)
      rw [b7, b13]; norm_num
    by_cases e13 : c = 13
    · subst e13
      obtain rfl : p = 2053 := S2 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 2053 h2053 hd (by norm_num)
      rw [b13, b2053]; norm_num
    by_cases e2053 : c = 2053
    · subst e2053
      have hge : 131391 ≤ p := R2053c (hP p hp).1 hd
        (S4b 2053 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega
          else hmin c' h1 h2 hcN h3)
      rw [b2053]
      exact step_ge (t := 131391) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e79 e7 e13 e2053 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num


-- The primes p below 1592 with 5 ∣ p + 1 that survive the local rules of the core without 19.
theorem par5_cands {p : ℕ} (hp : p.Prime) (hd : 5 ∣ p + 1) (hlt : p < 1592) (hne : p ≠ 19)
    (h3 : ¬ 3 ∣ p + 1) (h25 : ¬ 5 * 5 ∣ p + 1)
    (h11 : ¬ 11 ∣ p + 1) (h19 : ¬ 19 ∣ p + 1) (h23 : ¬ 23 ∣ p + 1) (h37 : ¬ 37 ∣ p + 1) (h41 : ¬ 41 ∣ p + 1) (h43 : ¬ 43 ∣ p + 1) (h71 : ¬ 71 ∣ p + 1) (h73 : ¬ 73 ∣ p + 1) (h79 : ¬ 79 ∣ p + 1) (h83 : ¬ 83 ∣ p + 1) (h101 : ¬ 101 ∣ p + 1) (h107 : ¬ 107 ∣ p + 1) (h113 : ¬ 113 ∣ p + 1) (h149 : ¬ 149 ∣ p + 1) :
    p = 79 ∨ p = 139 ∨ p = 619 ∨ p = 1039 ∨ p = 1279 := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 10 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 160 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 10 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- The core without 19, for the balance equation (E) with m at least 16 and exceptional primes
-- at least 2100.  Let p₀ be the parent of 5.  Then p₀ = 79, 13 is in P, the elements of P
-- below 342 are exactly 3, 5, 7, 13, 79, and 631 or 1663 is in P.
theorem core_no19 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm16 : 16 ≤ m)
    (hNb : ∀ z ∈ N, 2100 ≤ z) (h5 : 5 ∈ P) (h7 : 7 ∈ P) (h19 : 19 ∉ P)
    {p₀ : ℕ} (hp₀ : p₀ ∈ P) (hd₀ : 5 ∣ p₀ + 1) :
    p₀ = 79 ∧ 13 ∈ P ∧ (∀ q ∈ P, q < 342 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79) ∧
      (631 ∈ P ∨ 1663 ∈ P) := by
  have hm : 10 ≤ m := by omega
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 5 h5 (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 5 h5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = p₀ := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp p₀ hp₀ hd hd₀
  have n11 : 11 ∉ P := fun h => by
    have := T3 11 h (by norm_num)
    omega
  have n23 : 23 ∉ P := fun h => by
    have := T3 23 h (by norm_num)
    omega
  have n41 : 41 ∉ P := fun h => by
    have := T3 41 h (by norm_num)
    omega
  have n71 : 71 ∉ P := fun h => by
    have := T3 71 h (by norm_num)
    omega
  have n83 : 83 ∉ P := fun h => by
    have := T3 83 h (by norm_num)
    omega
  have n101 : 101 ∉ P := fun h => by
    have := T3 101 h (by norm_num)
    omega
  have n107 : 107 ∉ P := fun h => by
    have := T3 107 h (by norm_num)
    omega
  have n113 : 113 ∉ P := fun h => by
    have := T3 113 h (by norm_num)
    omega
  have n149 : 149 ∉ P := fun h => by
    have := T3 149 h (by norm_num)
    omega
  have n37 : 37 ∉ P := fun h => h19 (S1 19 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 37 h (by norm_num))
  have n43 : 43 ∉ P := fun h => n11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 43 h (by norm_num))
  have n73 : 73 ∉ P := fun h => n37 (S1 37 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 73 h (by norm_num))
  have c79 : ¬ 79 ∣ p₀ + 1 := fun h => by
    have h79 := S1 79 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h
    have := T5 79 h79 (by norm_num)
    subst this
    omega
  have hne19 : p₀ ≠ 19 := fun h => h19 (h ▸ hp₀)
  have c3 : ¬ 3 ∣ p₀ + 1 := fun h => by
    have := T3 p₀ hp₀ h
    subst this
    omega
  have cands : p₀ < 1592 → p₀ = 79 ∨ p₀ = 139 ∨ p₀ = 619 ∨ p₀ = 1039 ∨ p₀ = 1279 := fun hlt =>
    par5_cands (hP p₀ hp₀).1 hd₀ hlt hne19 c3
      (S4b 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀)
      (fun h => n11 (S1 11 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => h19 (S1 19 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n23 (S1 23 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n37 (S1 37 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n41 (S1 41 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n43 (S1 43 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n71 (S1 71 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n73 (S1 73 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      c79
      (fun h => n83 (S1 83 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n101 (S1 101 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n107 (S1 107 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n113 (S1 113 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p₀ hp₀ h))
      (fun h => n149 (S1 149 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p₀ hp₀ h))
  have H5 : ∀ t : ℕ, t ≤ p₀ → ∀ p ∈ P, 5 ∣ p + 1 → t ≤ p := fun t ht p hp hd => by
    rw [T5 p hp hd]; exact ht
  have no139 : p₀ ≠ 139 := fun h => par5_139 hP hN hK hKK E hm T3 (h ▸ hp₀)
  have no619 : 13 ∈ P → p₀ ≠ 619 := fun h13 h => by
    subst h
    have h31 : 31 ∈ P := S1 31 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 619 hp₀ (by norm_num)
    have hsub : ({3, 5, 7, 13, 31} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h5
      · exact h7
      · exact h13
      · exact h31
    have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
    revert h
    decide
  have h13 : 13 ∈ P := by
    by_contra h13
    have hlt : p₀ < 415 := by
      by_contra hc
      exact par5_ii hP hN hK hKK E hm T3 (H5 415 (by omega)) h13
    rcases cands (by omega) with h | h | h | h | h
    · exact par5_79_no13 hP hN hK hKK E hm hNb T3 (h ▸ hp₀) h13
    · exact absurd h no139
    · omega
    · omega
    · omega
  by_cases h103 : 103 ∈ P
  · have no79 : p₀ ≠ 79 := fun h => by
      subst h
      have hsub : ({3, 5, 7, 13, 79, 103} : Finset ℕ) ⊆ P := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h3
        · exact h5
        · exact h7
        · exact h13
        · exact hp₀
        · exact h103
      have h := S_abund hP (K_pos hN hK) hKK.1 E hsub
      revert h
      decide
    have no1039 : p₀ ≠ 1039 := fun h => by
      subst h
      have := S2 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 1039 hp₀ 103 h103
        (by norm_num) (by norm_num)
      omega
    by_cases h823 : 823 ∈ P
    · have hlt : p₀ < 1592 := by
        by_contra hc
        exact par5_iva hP hN hK hKK E hm hNb h5 h3 T3 (H5 1592 (by omega)) h7 h13 h103 h823
      rcases cands hlt with h | h | h | h | h
      · exact absurd h no79
      · exact absurd h no139
      · exact absurd h (no619 h13)
      · exact absurd h no1039
      · subst h
        exact (par5_1279_16 hP hN hK hKK E hm16 hNb h5 h3 T3 h7 h13 h103 h823 hp₀).elim
    · have hlt : p₀ < 862 := by
        by_contra hc
        exact par5_ivb hP hN hK hKK E hm h5 h3 T3 (H5 862 (by omega)) h7 h13 h103 h823
      rcases cands (by omega) with h | h | h | h | h
      · exact absurd h no79
      · exact absurd h no139
      · exact absurd h (no619 h13)
      · omega
      · omega
  · have hlt : p₀ < 661 := by
      by_contra hc
      exact par5_iii hP hN hK hKK E hm h5 h3 T3 (H5 661 (by omega)) h7 h13 h103
    rcases cands (by omega) with h | h | h | h | h
    · subst h
      have hs : ∀ q ∈ P, q < 342 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79 := by
        intro q hq hlt
        by_contra hne
        have hsub : ({3, 5, 7, 13, 79} : Finset ℕ) ⊆ P := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl
          · exact h3
          · exact h5
          · exact h7
          · exact h13
          · exact hp₀
        have hqA : q ∉ ({3, 5, 7, 13, 79} : Finset ℕ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          intro hmem
          apply hne
          omega
        have hg := abund_gap hP hN hK hKK E hsub hq hqA
        have e1 : ∏ p ∈ ({3, 5, 7, 13, 79} : Finset ℕ), (p + 1) = 215040 := by decide
        have e2 : ∏ p ∈ ({3, 5, 7, 13, 79} : Finset ℕ), p = 107835 := by decide
        rw [e1, e2] at hg
        omega
      refine ⟨rfl, h13, hs, ?_⟩
      by_contra hno
      have h631 : 631 ∉ P := fun h => hno (Or.inl h)
      have h1663 : 1663 ∉ P := fun h => hno (Or.inr h)
      by_cases h2053 : 2053 ∈ P
      · exact par5_79_B hP hN hK hKK E hm16 hNb T3 hp₀ h13 hs h2053
      · exact par5_79_A hP hN hK hKK E hm16 hNb T3 hp₀ h13 hs h631 h1663 h2053
    · exact absurd h no139
    · exact absurd h (no619 h13)
    · omega
    · omega


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

-- Core without 19 (step H2 of the parent reduction): n unitary perfect, S admissible, 4 divides a,
-- 5 and 7 divide n, 19 does not, and some prime p of n outside S has 5 ∣ p + 1.  Then a ≤ 9, or
-- 79 ∣ n, 13 ∣ n, the primes of n below 342 are exactly 2, 3, 5, 7, 13, 79, and 631 ∣ n or 1663 ∣ n.
theorem core_without_19 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h4 : 4 ∣ padicValNat 2 n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : ¬ 19 ∣ n)
    (hpar : ∃ p, p.Prime ∧ p ∣ n ∧ p ∉ S ∧ 5 ∣ p + 1) :
    padicValNat 2 n ≤ 9 ∨
    (79 ∣ n ∧ 13 ∣ n ∧
      (∀ q : ℕ, q.Prime → q ∣ n → q < 342 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 ∨ q = 79) ∧
      (631 ∣ n ∨ 1663 ∣ n)) := by
  by_cases hm : padicValNat 2 n ≤ 9
  · exact Or.inl hm
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  obtain ⟨hNS, hNb, K, K', P, hP, hK, hKK, E, hmem⟩ := core_setup h hS hadm1 hadm2 h2
  obtain ⟨p₀, hp₀p, hp₀n, hp₀S, hd₀⟩ := hpar
  have hp₀2 : p₀ ≠ 2 := by rintro rfl; omega
  have m5 : 5 ∈ P := (hmem 5).mpr ⟨by norm_num, by norm_num, h5, big_notMem hNb (by norm_num)⟩
  have h16 := (core_two_adic hP hNS hK E hNb m5 h4).1
  obtain ⟨rfl, h13, hall, h6⟩ := core_no19 hP hNS hK hKK E (by omega) hNb m5
    ((hmem 7).mpr ⟨by norm_num, by norm_num, h7, big_notMem hNb (by norm_num)⟩)
    (fun hc => h19 ((hmem 19).mp hc).2.2.1) ((hmem p₀).mpr ⟨hp₀p, hp₀2, hp₀n, hp₀S⟩) hd₀
  exact Or.inr ⟨hp₀n, ((hmem 13).mp h13).2.2.1, (fun q hqp hqn hlt => by
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · exact Or.inr (hall q ((hmem q).mpr ⟨hqp, hq2, hqn, big_notMem hNb (by omega)⟩) hlt)),
    h6.imp (fun h => ((hmem 631).mp h).2.2.1) (fun h => ((hmem 1663).mp h).2.2.1)⟩


theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max (max A1 A2) 9, fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall => ?_⟩
  obtain ⟨h16, h64⟩ := two_adic_core h hS hadm1 hadm2 h5 h4
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hpar := (hall S (Finset.Subset.refl S) hNS hadm2).2.2
  rcases core_without_19 h hS hadm1 hadm2 h4 h5 h7 h19 hpar with h9 | ⟨a, b, c, d | d⟩
  · exact h9.trans (le_max_right _ _)
  · exact (h1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall h16 h64 a b c d).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall h16 h64 a b c d).trans
      ((le_max_right _ _).trans (le_max_left _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H2_R1
