import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1
import Mathlib.Tactic

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H1.R1.H1
-- Credit: @zangetsu787

/-!
# Splitting the uniform exponent bound by the size of the repeated-odd-prime kernel

The step asks for a uniform bound on a = v₂(n) when S, the set of odd primes whose
square divides n, contains 3 and has at least two elements. The two cases |S| = 2
and |S| ≥ 3 are handled separately; the global bound is their maximum.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1

/-- A uniform bound on v₂(n) when the repeated odd primes are exactly 3 and one other. -/
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    S.card = 2 → 3 ∈ S → padicValNat 2 n ≤ A

/-- A uniform bound on v₂(n) when at least three odd primes occur to exponent ≥ 2. -/
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    3 ≤ S.card → 3 ∈ S → padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1 := by
  intro hTwo hMany
  obtain ⟨A2, hA2⟩ := hTwo
  obtain ⟨A3, hA3⟩ := hMany
  unfold OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1.H1
  refine ⟨max A2 A3, ?_⟩
  intro n hn S hS hcard hnon h3S hE hf3 hf5 hf7
  by_cases hs : S.card = 2
  · exact (hA2 n hn S hS hs h3S).trans (Nat.le_max_left _ _)
  · have hs3 : 3 ≤ S.card := by omega
    exact (hA3 n hn S hS hs3 h3S).trans (Nat.le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H1_R1_H1_R1
