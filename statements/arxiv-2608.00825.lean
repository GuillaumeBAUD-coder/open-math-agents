import Mathlib

/-!
# Small $q$-kernels in digraphs (bipartite, even $q$)

Source: https://arxiv.org/abs/2608.00825 (Irena Penev, Maya Stein, Ana Trujillo-Negrete,
"Small $q$-kernels in digraphs", 2026, Question 1.4 / Theorem 1.6, following Spiro,
Europ. J. Combin. 133, 2026, Question 7.7)
Credit: @Matthew-Eucaristo

For a finite loopless digraph $D$ and an integer $q \ge 2$, a $q$-kernel of $D$ is an
independent set $Q \subseteq V(D)$ such that every vertex $v \in V(D)$ is reachable from
some vertex of $Q$ by a directed path of length at most $q$. Penev, Stein, and
Trujillo-Negrete proved that for every odd $q \ge 3$, every source-free bipartite digraph
containing an out-branching (in particular, every strongly connected bipartite digraph)
admits a $q$-kernel of size at most $|V(D)|/(q+1) + 1$, and left open whether every
strongly connected bipartite digraph admits a $q$-kernel of size at most $|V(D)|/(q+1) + C$
(for some constant $C$ depending only on $q$) when $q \ge 2$ is even.
-/

namespace OMA.S_arxiv_2608_00825

/-- A finite loopless digraph on vertex type `V`. -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v

/-- Directed reachability from `u` to `v` in at most `k` steps. -/
inductive ReachableWithin {V : Type*} (D : Digraph V) : ℕ → V → V → Prop
  | refl (v : V) (k : ℕ) : ReachableWithin D k v v
  | step {k : ℕ} {u w v : V} : D.adj u w → ReachableWithin D k w v → ReachableWithin D (k + 1) u v

/-- A digraph is strongly connected if every vertex can reach every other vertex. -/
def StronglyConnected {V : Type*} (D : Digraph V) : Prop :=
  ∀ u v : V, ∃ k : ℕ, ReachableWithin D k u v

/-- A digraph is bipartite if its vertices can be 2-colored so every arc crosses colors. -/
def IsBipartite {V : Type*} (D : Digraph V) : Prop :=
  ∃ col : V → Bool, ∀ u v : V, D.adj u v → col u ≠ col v

/-- A subset `Q` is a `q`-kernel of `D` if it is independent and reaches every vertex
within directed distance at most `q`. -/
def IsQKernel {V : Type*} (D : Digraph V) (q : ℕ) (Q : Finset V) : Prop :=
  (∀ u ∈ Q, ∀ v ∈ Q, ¬ D.adj u v) ∧
  (∀ v : V, ∃ u ∈ Q, ReachableWithin D q u v)

/-- Open question of Penev, Stein, and Trujillo-Negrete (arXiv:2608.00825, following
Spiro, Question 7.7) for strongly connected bipartite digraphs and even `q ≥ 2`:
does there exist a constant `C` (depending only on `q`) such that every finite nonempty
strongly connected bipartite digraph `D` admits a `q`-kernel `Q` with
`|Q| ≤ |V(D)| / (q + 1) + C`? (Equivalently, `(q + 1) * |Q| ≤ |V(D)| + (q + 1) * C`.) -/
theorem main :
    ∀ q : ℕ, 2 ≤ q → Even q →
      ∃ C : ℕ, ∀ (n : ℕ) (_ : 0 < n) (D : Digraph (Fin n)),
        StronglyConnected D → IsBipartite D →
          ∃ Q : Finset (Fin n), IsQKernel D q Q ∧ (q + 1) * Q.card ≤ n + (q + 1) * C := by
  sorry

end OMA.S_arxiv_2608_00825
