import FormalConjectures.ErdosProblems.«931»

-- Reduction Erdos931.erdos_931.R1 of Erdős Problem 931
-- Credit: @RainRat
-- H1 is a linear gap bound for all solutions; H2 is finiteness inside such a bound.
-- Neither mentions the target or the other hypothesis. Together they close the problem.

namespace OMA.R_Erdos931_erdos_931_R1

/-- For all admissible k1 and k2 there is a constant C such that every solution has
    n2 at most C times n1 + k1 + 1. -/
def H1 : Prop :=
  ∀ (k₁ k₂ : ℕ), 3 ≤ k₂ → k₂ ≤ k₁ →
    ∃ C : ℕ, ∀ (n₁ n₂ : ℕ), n₁ + k₁ ≤ n₂ →
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
        (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors →
      n₂ ≤ C * (n₁ + k₁ + 1)

/-- For fixed k1, k2 and C, only finitely many pairs satisfy the same factor condition
    and the linear bound. -/
def H2 : Prop :=
  ∀ (k₁ k₂ C : ℕ), 3 ≤ k₂ → k₂ ≤ k₁ →
    { (n₁, n₂) | n₁ + k₁ ≤ n₂ ∧ n₂ ≤ C * (n₁ + k₁ + 1) ∧
      (∏ i ∈ Finset.Icc 1 k₁, (n₁ + i)).primeFactors =
        (∏ j ∈ Finset.Icc 1 k₂, (n₂ + j)).primeFactors }.Finite

theorem main : H1 → H2 → type_of% @Erdos931.erdos_931 := by
  intro h1 h2 k₁ k₂ hk₂ hk₁
  obtain ⟨C, hC⟩ := h1 k₁ k₂ hk₂ hk₁
  have hf := h2 k₁ k₂ C hk₂ hk₁
  apply hf.subset
  intro p hp
  exact ⟨hp.1, hC p.1 p.2 hp.1 hp.2, hp.2⟩

end OMA.R_Erdos931_erdos_931_R1
