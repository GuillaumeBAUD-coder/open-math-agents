import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1
-- Shrinks step H2 (the residue) of Erdos1052.erdos_1052.R1.H2.R1 to its 5-chain core and splits
-- the core in two.  Proving both H proves the step.
--
-- Notation as in the parent file: n unitary perfect, a = padicValNat 2 n, S = the set of odd
-- primes p with p^2 | n, N an ADMISSIBLE finite set of primes (every z in N is at least 128 and
-- at least N.card + 3, and the product over N of (z + 1) / (z - 2 - N.card) is at most
-- 2101/2097).  A prime of n is SIMPLE if it divides n exactly once.  For an odd prime c outside
-- N dividing n, the PARENT of c is the simple odd prime p of n outside N with c | p + 1, if
-- there is one (it is then unique: c has exactly one source in the balance equation).
--
-- PROVED BELOW, no hypothesis needed (two_adic_le_nine_of_no_five_chain): let N be admissible
-- and contain S.  Then a <= 9 unless
--     5 | n,  7 | n,  and 5 | p + 1 for some simple odd prime p of n outside N.
-- No condition modulo 4 on a and no condition on the primes 2 mod 3 of N is used, so this
-- theorem is independent of the parent theorem and covers every unitary perfect number with an
-- admissible kernel, not only the residue.  Method: the weight argument of Graham 1989 as set
-- up in the parent file (theorem master), with a case analysis on the parent r of 3:
--     no parent (3 divides 2^a + 1 or the kernel factor): case_top3 of the parent file;
--     r >= 59: the weight of 3 is at most (4/3) * B(59), B(x) = (x + 1) / (x - 1);
--     r = 17, 53: impossible, 9 | r + 1;   r = 29: impossible, 5 | 30 would be a second parent of 3;
--     r = 47: a prime p with 47 | p + 1 is at least 187;
--     r = 41: 7 | 42, so the Mersenne leaf 7 has weight exactly 8/7;
--     r = 23: chain 7, 13, then at least 103;
--     r = 11: chains 3, 11, 43, then at least 3697;  7, 13, 103, then at least 823;  31, 61,
--             then at least 487 (worst case 1.99211 < 2);
--     r = 5 and no prime of n outside N has 5 as a child: the three sub-cases of the case
--             a = 2 mod 4 of Graham (case3_ii, case3_iii, case3_iv of the parent file, which use
--             a = 2 mod 4 only to know exactly this);
--     r = 5 and 7 does not divide n: the weight of 3 is at most (4/3) * (6/5) * B(19).
-- What is left is r = 5 with a parent of 5 and with 7.  There the weights alone do not decide:
-- for instance 3, 5, 79, 631 (80 = 16 * 5, 632 = 8 * 79) together with 7, 13 has weight
-- 1.99732, inside the window [1.99327, 2) that the inequality cannot exclude (hand arithmetic,
-- not a Lean statement; it is not a unitary perfect number, only a configuration of small
-- primes that the weights cannot rule out).
--
-- For the residue this gives (theorem main): since 5 = 2 mod 3 is a simple prime below 128, the
-- parent of 3 in the core is 5, and the core is cut by whether the parent of 5 is 19.
-- H1 (OPEN, core with 19): the residue with 5 | n, 7 | n and 19 | n.  Then 19 is the parent of 5
--    (20 = 4 * 5), the primes 3, 5, 7, 19 are simple, and 13 does not divide n (hand
--    arithmetic: (4/3)(6/5)(8/7)(20/19)(14/13) > 2).
-- H2 (OPEN, core without 19): the residue with 5 | n, 7 | n, 19 not dividing n, such that for
--    EVERY admissible N containing S some prime p of n outside N has 5 | p + 1.  So the parent
--    of 5 is a simple prime p = 19 mod 30, p >= 79 (hand arithmetic), and it cannot be moved
--    into an admissible N.
-- No known unitary perfect number is in either family.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1

-- The 2-adic valuation is bounded over the residue family of the parent file restricted to the
-- n divisible by 5, 7 and 19.
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
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the residue family of the parent file restricted to the
-- n divisible by 5 and 7 but not by 19, for which every admissible N containing S leaves a
-- prime p of n outside N with 5 dividing p + 1.
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
    padicValNat 2 n ≤ A

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main

-- Section 1. Lower bounds for a prime p with c ∣ p + 1 (finite checks).

theorem Q5 {p : ℕ} (hp : p.Prime) (hd : 5 ∣ p + 1) :
    19 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 10 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 2 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 10 * j - 1 := by omega
  interval_cases j
  norm_num at hp

theorem Q47 {p : ℕ} (hp : p.Prime) (hd : 47 ∣ p + 1) :
    187 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 94 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 2 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 94 * j - 1 := by omega
  interval_cases j
  norm_num at hp

theorem Q61 {p : ℕ} (hp : p.Prime) (hd : 61 ∣ p + 1) :
    487 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 122 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 122 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q13a {p : ℕ} (hp : p.Prime) (hd : 13 ∣ p + 1) :
    103 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 26 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 26 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q13b {p : ℕ} (hp : p.Prime) (hd : 13 ∣ p + 1) (hne : p ≠ 103) :
    181 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 26 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 7 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 26 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q7 {p : ℕ} (hp : p.Prime) (hd : 7 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (hsq : ¬ 7 * 7 ∣ p + 1) (hne : p ≠ 13) :
    181 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 14 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 13 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 14 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q11 {p : ℕ} (hp : p.Prime) (hd : 11 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (hne : p ≠ 43) :
    241 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 22 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 11 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 22 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q31 {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h7 : ¬ 7 ∣ p + 1) (hne : p ≠ 61) :
    991 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 62 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 16 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 62 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

theorem Q43 {p : ℕ} (hp : p.Prime) (hd : 43 ∣ p + 1) (h3 : ¬ 3 ∣ p + 1) (h5 : ¬ 5 ∣ p + 1) (h7 : ¬ 7 ∣ p + 1) (h13 : ¬ 13 ∣ p + 1) (h37 : ¬ 37 ∣ p + 1) :
    3697 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hcc : 86 ∣ p + 1 := by omega
  obtain ⟨j, hj⟩ := hcc
  have hjlt : j < 43 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 86 * j - 1 := by omega
  interval_cases j <;> first | omega | (norm_num at hp)

-- Section 2. The cases for the parent of 3 (m at least 10).

-- The parent of 3 (the prime r of P with 3 ∣ r + 1) is at least 59: the weight of 3 is at most
-- (4/3) * B(59), the same number as in the 4 ∣ m case of Graham.
theorem case_parent_ge59 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (h59 : ∀ p ∈ P, 3 ∣ p + 1 → 59 ≤ p) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (60 / 58) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (60 / 58) := by rw [hβ]; norm_num
  have b7 : β 7 = 4 / 3 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 => by
      rw [hβ, if_neg e3]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    rw [bd p e3]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      have hge := h59 p hp hd
      rw [b3]
      exact step_ge (t := 59) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 47: a prime p with 47 ∣ p + 1 is at least 187.
theorem case_parent47 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 47) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (48 / 47 * (188 / 186)) else
      if p = 47 then 48 / 47 * (188 / 186) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (48 / 47 * (188 / 186)) := by rw [hβ]; norm_num
  have b47 : β 47 = 48 / 47 * (188 / 186) := by rw [hβ]; norm_num
  have b7 : β 7 = 4 / 3 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 47 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e47 => by
      rw [hβ, if_neg e3, if_neg e47]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e47 : p = 47
    · subst e47; rw [b47]; norm_num
    rw [bd p e3 e47]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 47 := T3 p hp hd
      rw [b3, b47]; norm_num
    by_cases e47 : c = 47
    · subst e47
      have hge : 187 ≤ p := Q47 (hP p hp).1 hd
      rw [b47]
      exact step_ge (t := 187) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e47) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 41: then 7 ∣ 41 + 1 as well, so no prime of P has 7 as its least odd
-- child and the weight of 7 is exactly 8/7.
theorem case_parent41 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (h41 : 41 ∈ P) (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 41) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (42 / 40) else
      if p = 7 then 8 / 7 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (42 / 40) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 7 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e7 => by
      rw [hβ, if_neg e3, if_neg e7]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    rw [bd p e3 e7]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 41 := T3 p hp hd
      rw [b3, bd 41 (by norm_num) (by norm_num)]; norm_num
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 41 := S2 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp 41 h41 hd (by norm_num)
      have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) (by norm_num)
      omega
    exact absurd (bd c e3 e7) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 23: refine the weight of 7 through 13 (parent of 13 at least 103).
theorem case_parent23 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 23) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (24 / 22) else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 102)) else
      if p = 13 then 14 / 13 * (104 / 102) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (24 / 22) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 102)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 102) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 7 → c ≠ 13 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e7 e13 => by
      rw [hβ, if_neg e3, if_neg e7, if_neg e13]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    rw [bd p e3 e7 e13]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 23 := T3 p hp hd
      rw [b3, bd 23 (by norm_num) (by norm_num) (by norm_num)]; norm_num
    by_cases e7 : c = 7
    · subst e7
      by_cases e : p = 13
      · subst e; rw [b7, b13]; norm_num
      have hge : 181 ≤ p := Q7 (hP p hp).1 hd (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp) e
      rw [b7]
      exact step_ge (t := 181) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e13 : c = 13
    · subst e13
      have hge : 103 ≤ p := Q13a (hP p hp).1 hd
      rw [b13]
      exact step_ge (t := 103) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e7 e13) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 11: chains 3, 11, 43, ..; 7, 13, 103, ..; 31, 61, .. .
theorem case_parent11 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 11) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (12 / 11 * (44 / 43 * (3698 / 3696))) else
      if p = 11 then 12 / 11 * (44 / 43 * (3698 / 3696)) else
      if p = 43 then 44 / 43 * (3698 / 3696) else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else
      if p = 103 then 104 / 103 * (824 / 822) else
      if p = 31 then 32 / 31 * (62 / 61 * (488 / 486)) else
      if p = 61 then 62 / 61 * (488 / 486) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (12 / 11 * (44 / 43 * (3698 / 3696))) := by rw [hβ]; norm_num
  have b11 : β 11 = 12 / 11 * (44 / 43 * (3698 / 3696)) := by rw [hβ]; norm_num
  have b43 : β 43 = 44 / 43 * (3698 / 3696) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 822)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 822) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (62 / 61 * (488 / 486)) := by rw [hβ]; norm_num
  have b61 : β 61 = 62 / 61 * (488 / 486) := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 11 → c ≠ 43 → c ≠ 7 → c ≠ 13 → c ≠ 103 → c ≠ 31 → c ≠ 61 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e11 e43 e7 e13 e103 e31 e61 => by
      rw [hβ, if_neg e3, if_neg e11, if_neg e43, if_neg e7, if_neg e13, if_neg e103, if_neg e31, if_neg e61]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e11 : p = 11
    · subst e11; rw [b11]; norm_num
    by_cases e43 : p = 43
    · subst e43; rw [b43]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e13 : p = 13
    · subst e13; rw [b13]; norm_num
    by_cases e103 : p = 103
    · subst e103; rw [b103]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e61 : p = 61
    · subst e61; rw [b61]; norm_num
    rw [bd p e3 e11 e43 e7 e13 e103 e31 e61]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 11 := T3 p hp hd
      rw [b3, b11]; norm_num
    by_cases e11 : c = 11
    · subst e11
      by_cases e : p = 43
      · subst e; rw [b11, b43]; norm_num
      have hge : 241 ≤ p := Q11 (hP p hp).1 hd (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega) e
      rw [b11]
      exact step_ge (t := 241) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e43 : c = 43
    · subst e43
      have hge : 3697 ≤ p := Q43 (hP p hp).1 hd (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 13 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 37 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
      rw [b43]
      exact step_ge (t := 3697) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      by_cases e : p = 13
      · subst e; rw [b7, b13]; norm_num
      have hge : 181 ≤ p := Q7 (hP p hp).1 hd (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (S4b 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp) e
      rw [b7]
      exact step_ge (t := 181) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e13 : c = 13
    · subst e13
      by_cases e : p = 103
      · subst e; rw [b13, b103]; norm_num
      have hge : 181 ≤ p := Q13b (hP p hp).1 hd e
      rw [b13]
      exact step_ge (t := 181) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e103 : c = 103
    · subst e103
      have hge : 823 ≤ p := R103 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b103]
      exact step_ge (t := 823) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      by_cases e : p = 61
      · subst e; rw [b31, b61]; norm_num
      have hge : 991 ≤ p := Q31 (hP p hp).1 hd (fun h => by have := hmin 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega)
        (fun h => by have := hmin 7 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) h; omega) e
      rw [b31]
      exact step_ge (t := 991) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e61 : c = 61
    · subst e61
      have hge : 487 ≤ p := Q61 (hP p hp).1 hd
      rw [b61]
      exact step_ge (t := 487) (by norm_num) hge (hB p hp).2 (by norm_num)
    exact absurd (bd c e3 e11 e43 e7 e13 e103 e31 e61) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 5 and 7 is not in P: a prime p with 5 ∣ p + 1 is at least 19, and the
-- Mersenne leaf 7 is absent.
theorem case_five_no7 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (hn7 : 7 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 18)) else
      if p = 5 then 6 / 5 * (20 / 18) else
      if p = 7 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 18)) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 18) := by rw [hβ]; norm_num
  have b7 : β 7 = 1 := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 64 / 63 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e7]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e7 : p = 7
    · subst e7; exact absurd hp hn7
    rw [bd p e3 e5 e7]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine master hP hN hK hKK E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      have hge : 19 ≤ p := Q5 (hP p hp).1 hd
      rw [b5]
      exact step_ge (t := 19) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      exact absurd hc hn7
    exact absurd (bd c e3 e5 e7) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The parent of 3 is 5 and no prime of P has 5 as a child: the case m = 2 mod 4 of Graham.
theorem five_top_ii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, ¬ 5 ∣ p + 1) (h13 : 13 ∉ P) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (224 / 222) else if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 222) := by rw [hβ]; norm_num
  have b31 : β 31 = 16 / 15 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e7 e127 => by rw [hβ, if_neg e3, if_neg e5, if_neg e7, if_neg e127]
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
    · subst e5; exact absurd hd (T5 p hp)
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

theorem five_top_iii {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h5 : 5 ∈ P) (h3 : 3 ∈ P)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, ¬ 5 ∣ p + 1) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∉ P) : False := by
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
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (1664 / 1662)) else
      if p = 13 then 14 / 13 * (1664 / 1662) else if p = 31 then 1 else
      if p = 127 then 128 / 127 * (32258 / 32256) else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (1664 / 1662)) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (1664 / 1662) := by rw [hβ]; norm_num
  have b31 : β 31 = 1 := by rw [hβ]; norm_num
  have b127 : β 127 = 128 / 127 * (32258 / 32256) := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 7 → c ≠ 13 → c ≠ 31 → c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
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
    · subst e5; exact absurd hd (T5 p hp)
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
    · subst e31; exact absurd hc h31
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

theorem five_top_iv {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m) (h5 : 5 ∈ P) (h3 : 3 ∈ P)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, ¬ 5 ∣ p + 1) (h7 : 7 ∈ P) (h13 : 13 ∈ P)
    (h103 : 103 ∈ P) : False := by
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
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p = if p = 3 then 8 / 5 else if p = 5 then 6 / 5 else
      if p = 7 then 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) else
      if p = 13 then 14 / 13 * (104 / 103 * (824 / 822)) else
      if p = 103 then 104 / 103 * (824 / 822) else if p = 31 then 1 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 8 / 5 := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (14 / 13 * (104 / 103 * (824 / 822))) := by rw [hβ]; norm_num
  have b13 : β 13 = 14 / 13 * (104 / 103 * (824 / 822)) := by rw [hβ]; norm_num
  have b103 : β 103 = 104 / 103 * (824 / 822) := by rw [hβ]; norm_num
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
    · subst e5; exact absurd hd (T5 p hp)
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
      have hge : 823 ≤ p := R103 (hP p hp).1 hd
        (fun c' h1 h2 h3 => if hcN : c' ∈ N then by have := (hN c' hcN).2.1; omega
          else hmin c' h1 h2 hcN h3)
      rw [b103]
      exact step_ge (t := 823) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31; exact absurd hc h31
    by_cases e127 : c = 127
    · subst e127; exact absurd hc h127
    exact absurd (bd c e3 e5 e7 e13 e103 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- A prime r below 59 with 3 ∣ r + 1 and 9 ∤ r + 1.
theorem small_parent {r : ℕ} (hrp : r.Prime) (hr2 : r ≠ 2) (h3r : 3 ∣ r + 1)
    (h9 : ¬ 3 * 3 ∣ r + 1) (hlt : r < 59) :
    r = 5 ∨ r = 11 ∨ r = 23 ∨ r = 29 ∨ r = 41 ∨ r = 47 := by
  have h2le := hrp.two_le
  interval_cases r <;> first | omega | (norm_num at hrp)

-- Section 3. The combined statement for the balance equation (E).

-- With m at least 10, equation (E) forces: 5 and 7 are in P and 5 divides p + 1 for some p in P.
theorem big_core {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKK : K ≤ K' ∧
      (K' : ℚ) / K * ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hm : 10 ≤ m)
    (hcore : 5 ∈ P → 7 ∈ P → ∀ p ∈ P, 5 ∣ p + 1 → False) : False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  by_cases hex : ∃ r ∈ P, 3 ∣ r + 1
  swap
  · exact case_top3 hP hN hK hKK E hm (fun p hp hd => hex ⟨p, hp, hd⟩)
  obtain ⟨r, hr, h3r⟩ := hex
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = r := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) p hp r hr hd h3r
  have h3 : 3 ∈ P := S1 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) r hr h3r
  by_cases h59 : 59 ≤ r
  · exact case_parent_ge59 hP hN hK hKK E hm (fun p hp hd => by rw [T3 p hp hd]; exact h59)
  have h9 : ¬ 3 * 3 ∣ r + 1 := S4b 3 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) r hr
  rcases small_parent (hP r hr).1 (hP r hr).2 h3r h9 (by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases h7 : 7 ∈ P
    swap
    · exact case_five_no7 hP hN hK hKK E hm T3 h7
    by_cases hpar : ∃ p ∈ P, 5 ∣ p + 1
    · obtain ⟨p, hp, hd⟩ := hpar
      exact hcore hr h7 p hp hd
    have T5 : ∀ p ∈ P, ¬ 5 ∣ p + 1 := fun p hp hd => hpar ⟨p, hp, hd⟩
    by_cases h13 : 13 ∈ P
    · by_cases h103 : 103 ∈ P
      · exact five_top_iv hP hN hK hKK E hm hr h3 T3 T5 h7 h13 h103
      · exact five_top_iii hP hN hK hKK E hm hr h3 T3 T5 h7 h13 h103
    · exact five_top_ii hP hN hK hKK E hm T3 T5 h13
  · exact case_parent11 hP hN hK hKK E hm T3
  · exact case_parent23 hP hN hK hKK E hm T3
  · have h5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (small_notMem hN (by norm_num)) 29 hr (by norm_num)
    have := T3 5 h5 (by norm_num)
    omega
  · exact case_parent41 hP hN hK hKK E hm hr T3
  · exact case_parent47 hP hN hK hKK E hm T3

-- Section 4. Back to unitary perfect numbers.

-- Let n be unitary perfect and N an admissible set of primes such that every odd prime of n
-- outside N divides n exactly once.  Then the 2-adic valuation of n is at most 9, unless 5 and 7
-- divide n and 5 divides p + 1 for some prime p of n outside N.
theorem two_adic_le_nine_of_no_five_chain {n : ℕ} {N : Finset ℕ}
    (h : Erdos1052.IsUnitaryPerfect n)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097)
    (hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1)
    (hcore : 5 ∣ n → 7 ∣ n → ∀ p : ℕ, p.Prime → p ∣ n → p ∉ N → 5 ∣ p + 1 → False) :
    padicValNat 2 n ≤ 9 := by
  by_contra hcon
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  rw [← hfac] at hcon
  have hm : 10 ≤ n.factorization 2 := by omega
  have h2 : 2 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have E := kernel_balance h h2 hs
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
  have hmemP : ∀ q ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ N),
      q.Prime ∧ q ∣ n ∧ q ∉ N := fun q hq => by
    obtain ⟨h1, hqN⟩ := Finset.mem_filter.mp hq
    have hq' := Finset.mem_of_mem_erase h1
    exact ⟨Nat.prime_of_mem_primeFactors hq', Nat.dvd_of_mem_primeFactors hq', hqN⟩
  exact big_core hP hN hK ⟨hK1, hK2⟩ E hm (fun h5 h7 p hp hd =>
    hcore (hmemP 5 h5).2.1 (hmemP 7 h7).2.1 p (hmemP p hp).1 (hmemP p hp).2.1 (hmemP p hp).2.2 hd)

-- Section 5. The reduction.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max (max A1 A2) 9, fun n h hsq S hS hadm1 hadm2 h4 h3 hall => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hsN : ∀ N : Finset ℕ, S ⊆ N →
      ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ N → n.factorization r = 1 := by
    intro N hSN r hr hr2 hrN
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hrN (hSN ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩))
    omega
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z :=
    fun z hz => ⟨((hS z).mp hz).1, hadm1 z hz⟩
  by_cases h5 : 5 ∣ n
  swap
  · exact (two_adic_le_nine_of_no_five_chain h hNS hadm2 (hsN S subset_rfl)
      (fun h5' _ _ _ _ _ _ => h5 h5')).trans (le_max_right _ _)
  by_cases h7 : 7 ∣ n
  swap
  · exact (two_adic_le_nine_of_no_five_chain h hNS hadm2 (hsN S subset_rfl)
      (fun _ h7' _ _ _ _ _ => h7 h7')).trans (le_max_right _ _)
  by_cases hpar : ∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      ∃ p, p.Prime ∧ p ∣ n ∧ p ∉ N ∧ 5 ∣ p + 1
  · by_cases h19 : 19 ∣ n
    · exact (h1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hall).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 (fun N hSN hN hΛ =>
        ⟨(hall N hSN hN hΛ).1, (hall N hSN hN hΛ).2, hpar N hSN hN hΛ⟩)).trans
        ((le_max_right _ _).trans (le_max_left _ _))
  · simp only [not_forall] at hpar
    obtain ⟨N, hSN, hN, hΛ, hno⟩ := hpar
    exact (two_adic_le_nine_of_no_five_chain h hN hΛ (hsN N hSN)
      (fun _ _ p hp hpn hpN hd => hno ⟨p, hp, hpn, hpN, hd⟩)).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1
