import FormalConjectures.Wikipedia.WilfNumericalSemigroupConjecture

/-!
# Reduction R1 of Wilf's conjecture
Credit: @sntntHb

Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

Split by the embedding dimension `e(S)` of the numerical semigroup:
* H1: `e(S) ≤ 3` (known: Fröberg, Gottlieb and Häggkvist 1987, Theorem 20).
* H2: `e(S) ≥ 4` (the open part of the conjecture).
The two hypotheses concern disjoint classes of semigroups, so neither implies the other; the
split separates the settled small embedding dimensions from the open part.
-/

namespace OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1

open WilfNumericalSemigroupConjecture AddSubmonoid

/-- Embedding dimension at most 3 (Fröberg–Gottlieb–Häggkvist). -/
def H1 : Prop :=
  ∀ {S : AddSubmonoid ℕ}, IsNumericalSemigroup S → embeddingDim S ≤ 3 →
    conductor S ≤ embeddingDim S * sporadicCount S

/-- Embedding dimension at least 4 (open). -/
def H2 : Prop :=
  ∀ {S : AddSubmonoid ℕ}, IsNumericalSemigroup S → 4 ≤ embeddingDim S →
    conductor S ≤ embeddingDim S * sporadicCount S

theorem main : H1 → H2 →
    type_of% @WilfNumericalSemigroupConjecture.wilf_numerical_semigroup_conjecture := by
  intro h1 h2 S hS
  by_cases he : embeddingDim S ≤ 3
  · exact h1 hS he
  · exact h2 hS (by omega)

end OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1
