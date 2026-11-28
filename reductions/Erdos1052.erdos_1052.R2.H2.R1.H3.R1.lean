import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R1

-- Reduction Erdos1052.erdos_1052.R2.H2.R1.H3.R1 of step Erdos1052.erdos_1052.R2.H2.R1.H3
-- Credit: @zangetsu787
-- The parent hypotheses of H3 already give 2 <= c.primeFactors.card.  Split on the exact
-- number of distinct odd prime factors of the powerful core c: H1 handles card = 2 and
-- H2 handles 3 <= card.  These two cases exhaust H3, and `main` is their combination.

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R1

def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    c.primeFactors.card = 2 →
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite

def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    3 ≤ c.primeFactors.card →
    {a : ℕ | let b := 2 ^ a * c
             let u := ∏ q ∈ b.primeFactors, (1 + q ^ b.factorization q)
             5 ≤ a ∧ ∃ S : Finset ℕ, 4 ≤ S.card ∧ S ⊆ Finset.Icc 3 u ∧
               (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) ∧
               u * (∏ p ∈ S, (1 + p)) = (2 * b) * ∏ p ∈ S, p}.Finite

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R1.H3 := by
  intro h1 h2 c hodd hp hcard
  by_cases h : c.primeFactors.card = 2
  · exact h1 c hodd hp h
  · have hlt : 2 < c.primeFactors.card := lt_of_le_of_ne hcard (Ne.symm h)
    exact h2 c hodd hp (Nat.succ_le_of_lt hlt)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R1_H3_R1
