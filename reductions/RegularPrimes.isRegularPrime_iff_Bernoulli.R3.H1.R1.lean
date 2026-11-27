import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3

/-! The Teichmüller lift of a unit a is a^p modulo p². Thus the degree-one
generalized Bernoulli sum for the character ω^(k-1) reduces to a finite
power sum divided by p. Split the relative class-number formula from the
Kummer congruence for each of these rational integer residues. -/
namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1
open NumberField

/-- Relative class-number formula modulo p, with the exceptional character
removed. Multiplication by 2 for each remaining character clears its half. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime],
  let K := CyclotomicField p ℚ
  let S := (Finset.Icc 2 (p - 3)).filter Even
  let h := classNumber K / classNumber (maximalRealSubfield K)
  (h : ZMod p) * (2 : ZMod p) ^ S.card = ∏ k ∈ S, -((((∑ a ∈ Finset.Ico 1 p, a ^ (1 + p * (k - 1))) / p : ℕ) : ZMod p))

/-- The Kummer congruence for the power-sum representative of B_k/k. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2 ≤ k → k ≤ p - 3 → Even k →
  ((((∑ a ∈ Finset.Ico 1 p, a ^ (1 + p * (k - 1))) / p : ℕ) : ZMod p)) * (k * (bernoulli' k).den : ZMod p) = ((bernoulli' k).num : ZMod p)

theorem main : H1 → H2 → OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3.H1 := by
  intro h1 h2 p hp
  let K := CyclotomicField p ℚ
  let S := (Finset.Icc 2 (p - 3)).filter Even
  let h := classNumber K / classNumber (maximalRealSubfield K)
  have hc := h1 p
  change (h : ZMod p) * 2 ^ S.card = ∏ k ∈ S, -((((∑ a ∈ Finset.Ico 1 p, a ^ (1 + p * (k - 1))) / p : ℕ) : ZMod p)) at hc
  change (h : ZMod p) * (∏ k ∈ S, (2 : ZMod p) * k * (bernoulli' k).den) = _
  simp_rw [mul_assoc (2 : ZMod p)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, hc, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  obtain ⟨hkI, he⟩ := Finset.mem_filter.mp hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hkI
  rw [neg_mul, h2 p k hlo hhi he]
end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H1_R1
