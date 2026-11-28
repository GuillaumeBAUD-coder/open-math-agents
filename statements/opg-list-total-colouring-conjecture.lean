import Mathlib

/-!
# List Total Colouring Conjecture

Source: https://www.openproblemgarden.org/op/list_total_colouring_conjecture
Credit: @Moti1125

Conjecture: if `G` is the total graph of a multigraph, then `χ_ℓ(G) = χ(G)`.

From the source: given a multigraph `H`, the total graph `T(H)` has vertex set `V(H) ∪ E(H)`, where
* two elements of `V(H)` are adjacent iff they are adjacent in `H`;
* two elements of `E(H)` are adjacent iff they share an endpoint;
* an element of `V(H)` is adjacent to an element of `E(H)` iff it is incident with it.

Conventions:
- A finite multigraph is a finite vertex type `V`, a finite edge type `E` and an endpoint map
  `ends : E → Sym2 V`. Parallel edges are allowed. Loops are excluded (`¬ (ends e).IsDiag`), the
  usual convention for total colouring.
- The vertex set `V(H) ∪ E(H)` of the total graph is the disjoint union `V ⊕ E`.
- `χ(G)` is Mathlib's `chromaticNumber`. `χ_ℓ(G)` is the least `k` such that `G` is
  `k`-choosable: every assignment of lists of at least `k` colours to the vertices admits a
  proper colouring choosing each vertex's colour from its list. Colours are natural numbers; any
  finite supply of colours can be relabelled into `ℕ`.
-/

namespace OMA.S_opg_list_total_colouring_conjecture

/-- The adjacency relation of the total graph before symmetrisation. -/
def totalRel {V E : Type} (ends : E → Sym2 V) : V ⊕ E → V ⊕ E → Prop
  | .inl u, .inl v => ∃ e, ends e = s(u, v)
  | .inr e, .inr f => ∃ v, v ∈ ends e ∧ v ∈ ends f
  | .inl v, .inr e => v ∈ ends e
  | .inr e, .inl v => v ∈ ends e

/-- The total graph `T(H)` of the multigraph with endpoint map `ends`. -/
def totalGraph {V E : Type} (ends : E → Sym2 V) : SimpleGraph (V ⊕ E) :=
  SimpleGraph.fromRel (totalRel ends)

/-- `G` is `k`-choosable: every assignment of lists of at least `k` colours admits a proper
colouring from the lists. -/
def IsChoosable {W : Type} (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ L : W → Finset ℕ, (∀ w, k ≤ (L w).card) →
    ∃ c : W → ℕ, (∀ w, c w ∈ L w) ∧ ∀ u w, G.Adj u w → c u ≠ c w

/-- The list chromatic number `χ_ℓ(G)`. -/
noncomputable def listChromaticNumber {W : Type} (G : SimpleGraph W) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | IsChoosable G k}, (k : ℕ∞)

theorem main :
    ∀ (V E : Type) [Fintype V] [Fintype E] (ends : E → Sym2 V), (∀ e, ¬ (ends e).IsDiag) →
      listChromaticNumber (totalGraph ends) = (totalGraph ends).chromaticNumber := by
  sorry

end OMA.S_opg_list_total_colouring_conjecture
