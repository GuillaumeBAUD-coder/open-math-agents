import Mathlib

/-!
# Clique factors in powers of 2-connected graphs

Source: *Clique factors in powers of graphs*, https://arxiv.org/abs/2210.17489
Credit: @SulkBash

## The problem (as the source states it)

The $k$th power of a graph $G$, denoted $G^k$, has the same vertex set as $G$; two vertices are
adjacent in $G^k$ if and only if there is a path between them in $G$ of length at most $k$. A
$K_r$-factor in a graph is a spanning subgraph in which every component is a complete graph of
order $r$.
- For any connected graph $G$ of order divisible by $r$, $G^{2r-2}$ contains a $K_r$-factor, and
  this is best possible for connected graphs.
- Conjecture: for any 2-connected graph $G$ of order divisible by $r$, $G^r$ contains a
  $K_r$-factor.

This was known for $r \le 3$, and the paper proves it for $r = 4$.

## Formalization notes

* **Vertices.** Graphs are on `Fin n`; any finite simple graph is isomorphic to one of these.
* **2-connected.** `IsTwoConnected G` means `n ≥ 3`, `G` is connected, and `G` stays connected
  after deleting any single vertex (`G.induce {w | w ≠ v}`). This is the standard definition.
* **Graph power.** `graphPower G k` is `SimpleGraph.fromRel` of the relation "there is a walk of
  length `≤ k` from `u` to `v` in `G`". So distinct `u, v` are adjacent iff such a walk exists in
  one of the two directions; reversing a walk shows both directions are equivalent.
  - The source says "path". A walk of length `≤ k` exists iff a path of length `≤ k` does, since
    shortening a walk to a path never increases its length.
* **Clique factor.** A $K_r$-factor of `H` is a partition of the vertex set into parts of size
  exactly `r`, each a clique of `H`. Its components are then exactly these complete graphs. We
  use a `Finpartition` of `Finset.univ`.
* **Order divisible by `r`.** This is `r ∣ n`. For `r = 0` the hypothesis fails, since `n ≥ 3`.
-/

namespace OMA.S_arxiv_2210_17489

/-- `G` is 2-connected: it has at least three vertices, is connected, and remains connected after
deleting any single vertex. -/
def IsTwoConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  3 ≤ n ∧ G.Connected ∧ ∀ v : Fin n, (G.induce {w | w ≠ v}).Connected

/-- The `k`-th power of `G`: distinct vertices are adjacent iff they are joined by a walk of length
at most `k` in `G`. -/
def graphPower {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ p : G.Walk u v, p.length ≤ k

/-- `H` has a `K_r`-factor: the vertex set splits into parts of size `r`, each a clique in `H`. -/
def HasCliqueFactor {n : ℕ} (H : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ P : Finpartition (Finset.univ : Finset (Fin n)),
    ∀ s ∈ P.parts, s.card = r ∧ H.IsClique (s : Set (Fin n))

/-- For every 2-connected graph `G` whose order is divisible by `r`, the power `G^r` has a
`K_r`-factor. -/
theorem main :
    ∀ (n r : ℕ) (G : SimpleGraph (Fin n)), IsTwoConnected G → r ∣ n →
      HasCliqueFactor (graphPower G r) r := by
  sorry

end OMA.S_arxiv_2210_17489
