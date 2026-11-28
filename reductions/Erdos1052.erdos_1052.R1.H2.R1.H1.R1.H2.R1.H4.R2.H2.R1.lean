import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R2.H2
-- Credit: @hafidh561
--
-- The step bounds a = padicValNat 2 n for the 43 primes z of its list.  The split below is at 127, the
-- largest prime of the list below 128, and separates the two halves at the place where the parent
-- reduction has two different instruments:
--
--   z >= 131 (H2 here; stated as `not (z <= 127)`, which is the same on this list, the next prime
--   after 127 in it being 131).  le_nine_of_leaf (section 4 of the merged reduction H4.R2) applies: its
--     residue hypothesis is 4 | a -> z | 2 ^ a + 1 -> z % 3 = 2 -> Odd (n.factorization z), which is
--     discharged outright by the step's (z % 3 = 2 -> Even (n.factorization z)).  What such z needs is
--     the leaf mass bound 2101/2097 on the z-leaves q + 1 = 2 ^ k * z ^ j; that is a computation on
--     the list 2 ^ k * z - 1 (and 2 ^ k * z ^ 2 - 1) for each z, independent of a.
--
--   z <= 127 (H1 here).  le_nine_of_leaf does not apply (z < 128), and le_nine_three_top does not
--     either: its hypothesis is 3 | 2 ^ a + 1 or 3 | 1 + z ^ e, and here a is even (3 does not divide
--     2 ^ a + 1) while z % 3 = 2 comes with Even e (so 3 does not divide 1 + z ^ e).  These 23 primes
--     need the 311/300 three-top weight argument in the admissible residue 4 | a for the primes that
--     are 1 mod 3, and the explicit chains through z + 1 for the primes that are 3 mod 4.
--
-- Both halves remain open research cases; neither is a trivial hypothesis, and the two need disjoint
-- arguments.  The split of the step's prime list 13..127 / 131..619 is the one that lets each half be
-- attacked with its own paper (leaf masses vs. three-top weights) instead of both at once.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H2_R1

-- H1: a is bounded when the only odd prime z with z ^ 2 | n is at most 127 (the 23 primes 13..127).
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
      109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337,
      367, 379, 439, 499, 619} : Finset ℕ),
    z ≤ 127 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    padicValNat 2 n % 2 = 0 → (z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    padicValNat 2 n % 8 ≠ 4 → (z ≠ 43 → padicValNat 2 n % 16 ≠ 8) → padicValNat 2 n % 4096 ≠ 2048 →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

-- H2: a is bounded when the only odd prime z with z ^ 2 | n is at least 131 (the 20 primes 131..619).
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ z ∈ ({13, 23, 29, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
      109, 113, 127, 131, 137, 139, 157, 173, 197, 199, 211, 227, 229, 263, 271, 307, 331, 337,
      367, 379, 439, 499, 619} : Finset ℕ),
    ¬ z ≤ 127 →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = z) →
    padicValNat 2 n % 2 = 0 → (z % 3 = 2 → Even (n.factorization z)) →
    padicValNat 2 n % 20 ≠ 10 → (z ≠ 29 → padicValNat 2 n % 28 ≠ 14) →
    padicValNat 2 n % 8 ≠ 4 → (z ≠ 43 → padicValNat 2 n % 16 ≠ 8) → padicValNat 2 n % 4096 ≠ 2048 →
    (∀ r ∈ ({4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, ?_⟩
  intro n hn z hz hS ha hz3 h20 h28 h8 h16 h4096 hr
  by_cases hle : z ≤ 127
  · exact (h1 n hn z hz hle hS ha hz3 h20 h28 h8 h16 h4096 hr).trans (le_max_left _ _)
  · exact (h2 n hn z hz hle hS ha hz3 h20 h28 h8 h16 h4096 hr).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R2_H2_R1
