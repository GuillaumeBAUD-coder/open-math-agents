import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2
import Mathlib

-- Reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R2.H2.R1 of step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R2.H2
-- Credit: @TheLittleOne1234

/-!
Punctured closed homotopy sphere, split along the textbook route to contractibility.
Let `M` be a closed `n`-manifold (`n ≥ 5`) homotopy equivalent to `Sⁿ`, and `p ∈ M`.

* `H1` (Seifert–van Kampen): `M` is simply connected, as `Sⁿ` is, and for `n ≥ 3` deleting a
  point does not change `π₁`, because the overlap with a chart ball is a punctured ball.
* `H2` (excision and the exact sequence of the pair `(M, M ∖ p)`, see Hatcher, Algebraic
  Topology, §3.3): `Hₖ(M ∖ p; ℤ) = 0` for `k ≥ 1`. For `k = n` this uses that
  `Hₙ(M) → Hₙ(M, M ∖ p)` is an isomorphism, since `Hₙ(M) ≅ ℤ` forces `M` to be orientable.
* `H3` (Hurewicz and Whitehead, Hatcher §4.2, together with Milnor, On spaces having the
  homotopy type of a CW-complex, Trans. AMS 90 (1959), for the CW homotopy type of a
  manifold): a second countable, simply connected manifold with vanishing positive-degree
  integral homology is contractible.

Second countability of `M ∖ p` comes from compactness of `M`. `main` proves the step from
`H1`, `H2` and `H3` in full; the hypotheses are the classical inputs that Mathlib does not
have at the pinned commit.
-/

open Set Metric CategoryTheory Limits AlgebraicTopology
open scoped ContinuousMap

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H2_R1

/-- Removing a point from a manifold homotopy equivalent to a high-dimensional sphere leaves
it simply connected (the sphere is simply connected; Seifert–van Kampen in dimension `≥ 3`). -/
def H1 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
  (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) → ∀ p : M,
  SimplyConnectedSpace ↥(({p} : Set M)ᶜ)

/-- The punctured closed homotopy sphere is acyclic in positive degrees. -/
def H2 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
  (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) → ∀ p : M, ∀ k : ℕ, 1 ≤ k →
  IsZero (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj
    (TopCat.of ↥(({p} : Set M)ᶜ)))

/-- A second countable simply connected manifold with trivial positive-degree integral
homology is contractible. -/
def H3 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (N : Type) [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SimplyConnectedSpace N],
  (∀ k : ℕ, 1 ≤ k → IsZero (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (TopCat.of N))) → ContractibleSpace N

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2.H2 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2.H2
  intro h1 h2 h3 n hn M _ _ _ _ e
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  have hM : Nonempty M :=
    ⟨e.invFun ⟨EuclideanSpace.single (0 : Fin (n+1)) (1 : ℝ), by simp⟩⟩
  obtain ⟨p⟩ := hM
  let U : TopologicalSpace.Opens M := ⟨({p} : Set M)ᶜ, isClosed_singleton.isOpen_compl⟩
  have hsc : SimplyConnectedSpace U := h1 n hn M e p
  refine ⟨p, ?_⟩
  exact h3 n hn U (fun k hk => h2 n hn M e p k hk)

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2_H2_R1
