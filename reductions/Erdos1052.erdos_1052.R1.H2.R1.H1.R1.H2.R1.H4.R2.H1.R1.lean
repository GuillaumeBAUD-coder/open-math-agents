import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H1.R1 of step
-- Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H1
-- Credit: @hafidh561
--
-- Splits the z = 257 leaf (only repeated odd prime 257, a = padicValNat 2 n = 8 mod 16, exponent of
-- 257 even) by the two conditions that every successful attack in this tree uses:
--   (i) whether 3 divides n, and (ii) among the instances with 3 not dividing n, whether a is the
--   smallest allowed value 8 or already at least 24.
-- Proving H1, H2 and H3 proves the step.
--
-- Why the split is the natural one.  Clearing the unitary perfect equation
--   (2^a + 1)(257^e + 1) prod_{p in P} (p + 1) = 2^(a+1) * 257^e * prod_{p in P} p
-- (P the simple odd primes of n, e = n.factorization 257) and reducing it modulo 3 gives, because a
-- and e are even and 257 = 2 mod 3,
--   prod_{p in P} (p + 1) = 2 * prod_{p in P} p   (mod 3).
-- If 3 does not divide n then prod_{p in P} p is not 0 mod 3, so no p in P can be 2 mod 3 (that would
-- make the left side 0), hence EVERY simple odd prime of n is 1 mod 3 in H1 and H2; in particular
-- 5, 11, 17, 23, 29, 41, 47, ... are not primes of n there, which is what removes the heavy small
-- leaves of the weight argument.  Branch H3 keeps 3 as a simple prime, where the congruence is
-- satisfied by a prime 2 mod 3 and no such restriction is available.
-- Within H1/H2 the parity hypothesis a = 8 mod 16 leaves a in {8, 24, 40, ...}; H1 is the single
-- smallest value, where the 2-adic budget sum_{p in P} v_2(p + 1) = a = 8 allows very few leaves,
-- and H2 is the tail 24 <= a.
--
-- The modulo 3 statement above is an argument, not a Lean theorem in this file: it is the reason the
-- cut is useful, and it is NOT used in the proof of main.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1

-- H1: the z = 257 leaf with 3 not dividing n and a at its smallest allowed value 8.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) → ¬ 3 ∣ n →
    padicValNat 2 n = 8 → padicValNat 2 n ≤ A

-- H2: the z = 257 leaf with 3 not dividing n and 24 <= a.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) → ¬ 3 ∣ n →
    24 ≤ padicValNat 2 n → padicValNat 2 n ≤ A

-- H3: the z = 257 leaf with 3 dividing n.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 257) →
    padicValNat 2 n % 16 = 8 → Even (n.factorization 257) → 3 ∣ n →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), ?_⟩
  intro n hn hS ha he
  have h1le : A1 ≤ max A1 (max A2 A3) := le_max_left _ _
  have h2le : A2 ≤ max A1 (max A2 A3) :=
    le_trans (le_max_left A2 A3) (le_max_right A1 (max A2 A3))
  have h3le : A3 ≤ max A1 (max A2 A3) :=
    le_trans (le_max_right A2 A3) (le_max_right A1 (max A2 A3))
  by_cases h3n : 3 ∣ n
  · exact le_trans (h3 n hn hS ha he h3n) h3le
  · by_cases ha8 : padicValNat 2 n = 8
    · exact le_trans (h1 n hn hS ha he h3n ha8) h1le
    · have h24 : 24 ≤ padicValNat 2 n := by omega
      exact le_trans (h2 n hn hS ha he h3n h24) h2le

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H1_R1
