import FormalConjectures.ErdosProblems.«479»

-- Reduction Erdos479.erdos_479.R1 of Erdős Problem 479
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1: the known cases k = 0, k = -1, k = -2 and k = 2^i (i ≥ 1). Erdős and Graham credit k = 2^i and k = -1 to Graham, Lehmer and Lehmer; see also a note by Tang. k = -2 follows from the chain n -> 2^n + 2. H1 has a short elementary proof.
-- Note: the upstream binder ∀ᵉ (k : ℤ) (k ≠ 1) elaborates to ∀ (k k : ℤ), k ≠ 1 → ..., with an unused first k.
-- H2: every other k ≠ 1 (open; for k = 3 the least solution is n = 4700063497).

namespace OMA.R_Erdos479_erdos_479_R1

def H1 : Prop := ∀ k : ℤ, (k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) →
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite

def H2 : Prop := ∀ k : ℤ, k ≠ 1 → ¬ (k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i) →
    { n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)] }.Infinite

theorem main : H1 → H2 → type_of% @Erdos479.erdos_479 := by
  intro h1 h2 _ k hk
  by_cases h : k = 0 ∨ k = -1 ∨ k = -2 ∨ ∃ i : ℕ, 1 ≤ i ∧ k = 2 ^ i
  · exact h1 k h
  · exact h2 k hk h

end OMA.R_Erdos479_erdos_479_R1
