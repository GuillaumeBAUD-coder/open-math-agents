import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H2.R1.H1.R1.H2
-- Credit: @hafidh561
--
-- Splits the step (3 is the only repeated odd prime of the unitary perfect number n and its
-- exponent is 11, a = padicValNat 2 n is 2 mod 4 and at least 262) by whether 269 divides a.
--
-- Why this split: the sieve of the parent reduction excludes a being an odd multiple of every
-- d from 1 to 400 except the sixteen exceptions
--   {1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383}.
-- For a = 2 mod 4 the odd d are automatic (a is even), and d = 2 is excluded by hypothesis, so the
-- only surviving sieve classes are d = 8 (a = 8 mod 16, a different step) and the seven primes
-- 269, 271, 311, 313, 347, 353, 383.  269 is the smallest of them: the odd prime factors of
-- 2 ^ 269 + 1 that the parent chain does not already kill are exactly what keeps the class alive,
-- so the class 269 | a is worth its own statement, and every a with 269 not dividing a inherits one
-- more exclusion than the parent step gave.
--
-- H1 (OPEN): 269 divides a.   H2 (OPEN): 269 does not divide a.
--
-- The split itself is unconditional: in the branch 269 divided a the hypotheses of H1 hold, and in
-- the other branch those of H2.  Both H1 and H2 keep every hypothesis of the step.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1

-- The class 269 | a.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 4 = 2 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 →
      d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    269 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

-- The complementary class.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 11 →
    padicValNat 2 n % 4 = 2 →
    262 ≤ padicValNat 2 n →
    (∀ d, 1 ≤ d → d ≤ 400 →
      d ∉ ({1, 2, 3, 5, 7, 8, 9, 11, 13, 269, 271, 311, 313, 347, 353, 383} : Finset ℕ) →
      padicValNat 2 n % (2 * d) ≠ d) →
    ¬ 269 ∣ padicValNat 2 n →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 →
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1.H2 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩
  refine ⟨max A1 A2, fun n hn h3 he h4 h262 hs => ?_⟩
  by_cases h : 269 ∣ padicValNat 2 n
  · exact (hA1 n hn h3 he h4 h262 hs h).trans (le_max_left _ _)
  · exact (hA2 n hn h3 he h4 h262 hs h).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H2_R1_H1_R1_H2_R1
