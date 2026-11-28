import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2.R1.H2
-- Credit: @zangetsu787
--
-- The step bounds a = padicValNat 2 n when n is unitary perfect, 3 is its only repeated odd prime
-- with exponent 7, a >= 262 is even, 16 does not divide a, and two finite residue sieves hold.
-- Under those last two conditions a has one of exactly three dyadic valuations:
--     v2(a) = 1  <=>  a % 4 = 2,     v2(a) = 2  <=>  a % 8 = 4,     v2(a) = 3  <=>  a % 16 = 8.
-- H1, H2, H3 bound a in these three cases (from the core unitary-perfect hypotheses alone, so each
-- subgoal is strictly easier than the step), and main takes the largest of the three bounds.
-- This is the same three-case split as the lead's PLAN #194651 (extending the even-a sieve for the
-- three allowed positive dyadic valuations of a).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1

-- H1: a is bounded in the v2(a) = 1 branch (a % 4 = 2).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n ≤ A

-- H2: a is bounded in the v2(a) = 2 branch (a % 8 = 4).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n →
    padicValNat 2 n % 8 = 4 →
    padicValNat 2 n ≤ A

-- H3: a is bounded in the v2(a) = 3 branch (a % 16 = 8).
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n →
    padicValNat 2 n % 16 = 8 →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 h3
  rcases h1 with ⟨A1, h1⟩
  rcases h2 with ⟨A2, h2⟩
  rcases h3 with ⟨A3, h3⟩
  refine ⟨max A1 (max A2 A3), ?_⟩
  intro n hn hs hf hbig heven h16 hr1 hr2
  have hcases : padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 8 = 4 ∨
      padicValNat 2 n % 16 = 8 := by
    omega
  rcases hcases with h | h | h
  · exact (h1 n hn hs hf hbig h).trans (Nat.le_max_left A1 (max A2 A3))
  · exact (h2 n hn hs hf hbig h).trans
      (le_trans (Nat.le_max_left A2 A3) (Nat.le_max_right A1 (max A2 A3)))
  · exact (h3 n hn hs hf hbig h).trans
      (le_trans (Nat.le_max_right A2 A3) (Nat.le_max_right A1 (max A2 A3)))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1
