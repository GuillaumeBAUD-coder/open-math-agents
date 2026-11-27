import FormalConjectures.Wikipedia.LovaszPlummerConjecture

-- Reduction LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1 of Thomassen (1998): regular graphs of large degree.
-- Credit: @bradenchurch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_variants_thomassen_R1

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), 300 ≤ r → (∀ v, G.degree v = r) →
    ∀ (v : V) (c : G.Walk v v), LovaszPlummerConjecture.IsHamiltonianCycle G c →
      ∃ I : Finset V,
        (∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges) ∧
        (∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges)

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (c : G.Walk v v), LovaszPlummerConjecture.IsHamiltonianCycle G c →
    ∀ I : Finset V,
      (∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges) →
      (∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges) →
      ∃ (w : V) (c' : G.Walk w w), LovaszPlummerConjecture.IsHamiltonianCycle G c' ∧
        c'.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → type_of% @LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen := by
  intro h1 h2 V _ _ G _ r hr hreg v c hc
  obtain ⟨I, hind, hdom⟩ := h1 G r hr hreg v c hc
  exact h2 G v c hc I hind hdom

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_variants_thomassen_R1
