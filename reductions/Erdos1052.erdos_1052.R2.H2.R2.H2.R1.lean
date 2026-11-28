import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2

-- Reduction Erdos1052.erdos_1052.R2.H2.R2.H2.R1 of step Erdos1052.erdos_1052.R2.H2.R2.H2
-- Credit: @zangetsu787

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R1

/-- Easy configurations: the two prime factors coincide, one is 2, or one divides the fixed odd core c. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ q ∈ S, ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 1+q →
      (p = r ∨ p = 2 ∨ r = 2 ∨ p ∣ c ∨ r ∣ c) → min p r ≤ B

/-- Hard configurations: two distinct odd primes outside the core c both divide 1+q. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ q ∈ S, ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 1+q →
      (p ≠ r ∧ p ≠ 2 ∧ r ≠ 2 ∧ ¬p ∣ c ∧ ¬r ∣ c) → min p r ≤ B

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2.H2 := by
  intro h1 h2 c hc hcpow
  obtain ⟨B1, hB1⟩ := h1 c hc hcpow
  obtain ⟨B2, hB2⟩ := h2 c hc hcpow
  refine ⟨max B1 B2, ?_⟩
  intro a S
  dsimp only
  intro ha hcard hsub hprime hbal q hq p r hp hr hpq
  by_cases hcase : p = r ∨ p = 2 ∨ r = 2 ∨ p ∣ c ∨ r ∣ c
  · exact (hB1 a S ha hcard hsub hprime hbal q hq p r hp hr hpq hcase).trans (Nat.le_max_left B1 B2)
  · have hhard : p ≠ r ∧ p ≠ 2 ∧ r ≠ 2 ∧ ¬p ∣ c ∧ ¬r ∣ c := by
      push_neg at hcase
      exact hcase
    exact (hB2 a S ha hcard hsub hprime hbal q hq p r hp hr hpq hhard).trans (Nat.le_max_right B1 B2)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R1
