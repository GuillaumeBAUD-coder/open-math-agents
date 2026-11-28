import OMAReductions.R_Erdos1052_erdos_1052_R2
import Mathlib

/-!
# Radical versus maximum exponent decomposition of the repeated odd core

Splits the uniform bound on the repeated odd powerful part
`∏ p ∈ R, p ^ n.factorization p` of a unitary perfect number with at least four simple
odd prime factors into:
- `H1`: a uniform bound on the radical `∏ p ∈ R, p` of the repeated odd primes.
- `H2`: a uniform bound on each repeated odd prime exponent `n.factorization p`.
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H1_R2

/-- Uniform bound on the radical of the repeated odd prime factors. -/
def H1 : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    4 ≤ (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card →
    (∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1), p) ≤ B

/-- Uniform bound on the maximum exponent among repeated odd prime factors. -/
def H2 : Prop :=
  ∃ E : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    4 ≤ (n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p = 1)).card →
    ∀ p ∈ n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1),
      n.factorization p ≤ E

/-- Combining bounds on the radical and maximum exponent bounds the repeated odd core. -/
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2.H1 := by
  intro h1 h2
  obtain ⟨B, hB⟩ := h1
  obtain ⟨E, hE⟩ := h2
  refine ⟨B ^ E, fun n hn hcard => ?_⟩
  let R := n.primeFactors.filter (fun p => p ≠ 2 ∧ n.factorization p ≠ 1)
  have hterm : ∀ p ∈ R, p ^ n.factorization p ≤ p ^ E := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    exact Nat.pow_le_pow_right hp_prime.pos (hE n hn hcard p hp)
  calc
    (∏ p ∈ R, p ^ n.factorization p)
        ≤ ∏ p ∈ R, p ^ E := Finset.prod_le_prod' hterm
    _ = (∏ p ∈ R, p) ^ E := Finset.prod_pow R E (fun p => p)
    _ ≤ B ^ E := Nat.pow_le_pow_left (hB n hn hcard) E

end OMA.R_Erdos1052_erdos_1052_R2_H1_R2
