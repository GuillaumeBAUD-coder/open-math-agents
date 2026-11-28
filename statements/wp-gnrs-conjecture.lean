import Mathlib

/-!
# GNRS conjecture

Source: https://en.wikipedia.org/wiki/GNRS_conjecture
Credit: @sntntHb

The source (Wikipedia) discusses embeddings of the shortest path distances of weighted
undirected graphs into ℓ₁ spaces, real vector spaces in which the distance between two vectors
is the sum of their coordinate differences. It observes that the graphs having an embedding
with at most a given distortion are closed under graph minors, and states the conjecture of
Gupta, Newman, Rabinovich and Sinclair (2004): conversely, every minor-closed family of graphs,
other than the family of all graphs, can be embedded into an ℓ₁ space with bounded distortion.

Formalized proposition. Graphs are finite simple graphs on `Fin n`; a family is a predicate
`F n G`. `H` is a minor of `G` when `G` contains a minor model of `H`: pairwise disjoint,
nonempty, connected branch sets, with a `G`-edge between the branch sets of adjacent vertices
of `H`. A family is minor-closed when it contains every minor of each of its members, and it
is not the family of all graphs when some graph lies outside it. Edge weights are arbitrary
nonnegative reals on the edges of a connected graph, and the distance is the least total weight
of a walk. The target is the sequence space ℓ₁ (Mathlib's `lp` with exponent 1 on `ℕ`).
An embedding has distortion at most `c` when, after scaling by some `r > 0`, every distance is
stretched by a factor between 1 and `c`. The theorem states that for each such family there is
one constant `c` that bounds the distortion for every weighted connected graph in the family.
-/

namespace OMA.S_wp_gnrs_conjecture

/-- `H` is a minor of `G`: there is a minor model of `H` in `G`. -/
def IsMinor {m n : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ B : Fin m → Finset (Fin n),
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce ((B i : Finset (Fin n)) : Set (Fin n))).Connected) ∧
    (∀ i j, H.Adj i j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- A family of finite graphs is minor-closed. -/
def MinorClosed (F : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)), F n G → IsMinor H G → F m H

/-- The weighted shortest path distance: the least total weight of a walk from `u` to `v`. -/
noncomputable def weightedDist {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (u v : Fin n) : ℝ :=
  ⨅ p : G.Walk u v, (p.edges.map w).sum

theorem main :
    ∀ F : ∀ n : ℕ, SimpleGraph (Fin n) → Prop, MinorClosed F →
      (∃ (n : ℕ) (G : SimpleGraph (Fin n)), ¬ F n G) →
      ∃ c : ℝ, 1 ≤ c ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), F n G → G.Connected →
          ∀ w : Sym2 (Fin n) → ℝ, (∀ e ∈ G.edgeSet, 0 ≤ w e) →
            ∃ (f : Fin n → lp (fun _ : ℕ => ℝ) 1) (r : ℝ), 0 < r ∧
              ∀ u v : Fin n,
                r * weightedDist G w u v ≤ ‖f u - f v‖ ∧
                ‖f u - f v‖ ≤ c * r * weightedDist G w u v := by
  sorry

end OMA.S_wp_gnrs_conjecture
