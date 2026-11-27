import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1

def H1 : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card = 4 → (∃ p ∈ n.primeFactors, p < 16 * (2 ^ n.primeFactors.card) ^ 3) → n ^ 2 ≡ 1 [MOD OeisA224.a n * (OeisA224.a n - 1)] → ∃ k : ℕ, 16 < k ∧ n ^ 2 = k * OeisA224.a n * (OeisA224.a n - 1) + 1

def H2 : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card = 4 → (∃ p ∈ n.primeFactors, p < 16 * (2 ^ n.primeFactors.card) ^ 3) → n ^ 2 ≡ 1 [MOD OeisA224.a n * (OeisA224.a n - 1)] → ∀ k : ℕ, n ^ 2 = k * OeisA224.a n * (OeisA224.a n - 1) + 1 → k < 256

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro h1 h2 n ho hcard hexists hmod
  obtain ⟨k, hk16, heq⟩ := h1 n ho hcard hexists hmod
  exact ⟨k, hk16, h2 n ho hcard hexists hmod k heq, heq⟩

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1
