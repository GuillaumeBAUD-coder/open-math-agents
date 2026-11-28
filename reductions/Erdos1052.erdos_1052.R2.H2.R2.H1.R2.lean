import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2

-- Reduction Erdos1052.erdos_1052.R2.H2.R2.H1.R2 of step H1 of Erdos1052.erdos_1052.R2.H2.R2.
-- Splits the seed prime-pair bound by the size of a pair member relative to the fixed
-- odd powerful core c: pairs with a member at most c are bounded by c itself, while
-- the only remaining difficulty is the case where both members exceed c.
-- H1 is that residual large-prime case; H2 is the small-prime case.

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R2

-- Residual case: both prime factors of 2^a+1 are strictly larger than the core c.
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^a+1 → c < p → c < r → min p r ≤ B

-- Easy case: at least one of the two prime factors is at most the core c.
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^a+1 → p ≤ c ∨ r ≤ c → min p r ≤ c

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2.H1 := by
  intro h₁ h₂ c hc hpow
  obtain ⟨B, hB⟩ := h₁ c hc hpow
  refine ⟨max B c, ?_⟩
  intro a S b u ha hcard hsub hS heq p r hp hr hpr
  by_cases hsmall : p ≤ c ∨ r ≤ c
  · exact (h₂ c hc hpow a S ha hcard hsub hS heq p r hp hr hpr hsmall).trans (Nat.le_max_right _ _)
  · have hpc : c < p := by omega
    have hrc : c < r := by omega
    exact (hB a S ha hcard hsub hS heq p r hp hr hpr hpc hrc).trans (Nat.le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R2
