import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin

/-!
# DeVos's conjecture on partitioning edge-connectivity

Open Problem Garden:
https://www.openproblemgarden.org/op/partitioning_edge_connectivity

M. DeVos, T. Johnson, and P. D. Seymour, *Cut Coloring and Circuit Covering*, Conjecture 1.7:
https://www.sfu.ca/~mdevos/papers/courteous.pdf
-/

namespace OMA.S_opg_partitioning_edge_connectivity

/-- Every nontrivial vertex cut is crossed by at least `k` edges of the spanning subgraph
with edge set `E`. Edge labels distinguish parallel edges, and loops cross no cut. -/
def IsEdgeConnected {n m : ℕ} (ends : Fin m → Fin n × Fin n)
    (E : Finset (Fin m)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    k ≤ (E.filter fun e => ¬ ((ends e).1 ∈ S ↔ (ends e).2 ∈ S)).card

/-- For positive `a` and `b`, every `(a + b + 2)`-edge-connected finite multigraph admits a
partition of its edges into an `a`-edge-connected and a `b`-edge-connected spanning subgraph. -/
theorem main :
    ∀ (a b n m : ℕ) (ends : Fin m → Fin n × Fin n), 0 < a → 0 < b →
      IsEdgeConnected ends Finset.univ (a + b + 2) →
      ∃ A : Finset (Fin m), IsEdgeConnected ends A a ∧
        IsEdgeConnected ends (Finset.univ \ A) b := by
  sorry

end OMA.S_opg_partitioning_edge_connectivity
