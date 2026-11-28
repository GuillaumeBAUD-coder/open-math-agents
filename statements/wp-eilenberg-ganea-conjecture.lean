import Mathlib

/-!
# Eilenberg–Ganea conjecture

Source: https://en.wikipedia.org/wiki/Eilenberg–Ganea_conjecture
Credit: @my-other-github-account (catalogue submission)

A group with cohomological dimension 2 also has a 2-dimensional Eilenberg–MacLane space K(G, 1).

Definitions adapted from OpenAI, openai/math at 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/ComparatorChallenges/EilenbergGanea.lean (Apache-2.0). That project formalizes a finitely
generated counterexample (OAI.EilenbergGanea.source_main), so this statement is expected to be false.

Conventions (standard reading of the source):
* cohomological dimension = projective dimension of the trivial left ℤ[G]-module ℤ;
* a K(G, 1) is a path-connected CW complex with fundamental group G and contractible
  universal cover; 2-dimensional means no cells in degree above 2 (no bound on cell counts);
* groups and spaces are taken in `Type`.
-/

namespace OMA.S_wp_eilenberg_ganea_conjecture

noncomputable section

open Topology

/-- Projective dimension of the trivial integral left group-ring module. -/
def cohomologicalDimension (G : Type) [Group G] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ G) (Representation.trivial ℤ G ℤ).asModule)

/-- `G` has a CW Eilenberg–MacLane space `K(G, 1)` of dimension at most `dimension`. -/
def HasClassifyingSpace (G : Type) [Group G] (dimension : ℕ) : Prop :=
  ∃ (Space : Type) (_ : TopologicalSpace Space) (_ : T2Space Space)
    (_ : Topology.CWComplex (Set.univ : Set Space)),
    (∀ degree : ℕ, dimension < degree →
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set Space) degree)) ∧
    PathConnectedSpace Space ∧
    ∃ basepoint : Space, Nonempty (FundamentalGroup Space basepoint ≃* G) ∧
    ∃ (Cover : Type) (_ : TopologicalSpace Cover), ContractibleSpace Cover ∧
    ∃ projection : Cover → Space, IsCoveringMap projection ∧ Function.Surjective projection

theorem main : ∀ (G : Type) [Group G],
    cohomologicalDimension G = 2 → HasClassifyingSpace G 2 := by
  sorry

end

end OMA.S_wp_eilenberg_ganea_conjecture
