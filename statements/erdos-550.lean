import Mathlib

/-!
# Erdős Problem 550

Source: https://www.erdosproblems.com/550
Credit: @sntntHb

Let `m_1 ≤ ⋯ ≤ m_k` and `n` be sufficiently large. If `T` is a tree on `n` vertices and `G` is
the complete multipartite graph with vertex class sizes `m_1, …, m_k` then prove that
`R(T,G) ≤ (χ(G) - 1)(R(T, K_{m_1,m_2}) - 1) + m_1`.
(Problem #16 in Ramsey Theory in the graphs problem collection, [EFRS85].)

We state the inequality as a theorem.

Conventions:
- `R(H₁, H₂)` (`graphRamsey`) is the least `N` such that for every simple graph `G` on `N`
  vertices, `H₁` is contained in `G` (as a subgraph, not necessarily induced) or `H₂` is
  contained in the complement of `G`. Such an `N` always exists for finite `H₁, H₂`.
- `completeMultipartite m` is the complete multipartite graph whose vertex classes are
  `Fin (m i)` for `i : Fin k`: two vertices are adjacent iff they lie in different classes.
- The class sizes are positive and `k ≥ 2` (so `K_{m_1,m_2}` makes sense); then
  `χ(G) = k`, and `χ(G) - 1` is written `k - 1`.
- Sufficiently large is read as: for fixed `k` and fixed sizes `m_1 ≤ ⋯ ≤ m_k`, the inequality
  holds for every tree `T` on `n` vertices once `n` is large enough (depending on the sizes).
-/

namespace OMA.S_erdos_550

open SimpleGraph Filter

/-- The graph Ramsey number `R(H₁, H₂)`. -/
noncomputable def graphRamsey {α β : Type*} (H₁ : SimpleGraph α) (H₂ : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), H₁ ⊑ G ∨ H₂ ⊑ Gᶜ}

/-- The complete multipartite graph with vertex classes of sizes `m 0, …, m (k - 1)`. -/
def completeMultipartite {k : ℕ} (m : Fin k → ℕ) : SimpleGraph (Σ i : Fin k, Fin (m i)) where
  Adj x y := x.1 ≠ y.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

theorem main :
    ∀ (k : ℕ) (hk : 2 ≤ k) (m : Fin k → ℕ), Monotone m → (∀ i, 0 < m i) →
      ∀ᶠ n : ℕ in atTop, ∀ T : SimpleGraph (Fin n), T.IsTree →
        graphRamsey T (completeMultipartite m) ≤
          (k - 1) * (graphRamsey T
            (completeBipartiteGraph (Fin (m ⟨0, by omega⟩)) (Fin (m ⟨1, by omega⟩))) - 1) +
            m ⟨0, by omega⟩ := by
  sorry

end OMA.S_erdos_550
