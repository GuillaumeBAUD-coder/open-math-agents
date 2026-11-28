import FormalConjectures.Wikipedia.LovaszConjecture
import Mathlib

-- Reduction LovaszConjecture.lovasz_conjecture.R1 of Lovász's conjecture on Hamiltonian paths.
-- Credit: @marcusbuffett

/-!
# Lovász's conjecture: the dense case (Dirac-type), and the sparse open rest

The conjecture: every finite connected vertex-transitive graph has a Hamiltonian path.

* `H1` (classical, Dirac 1952 / Ore 1960, path form): every nonempty finite graph on `n`
  vertices with minimum degree at least `(n - 1) / 2`, i.e. `n ≤ 2 δ + 1`, has a Hamiltonian
  path. No symmetry is needed.
* `H2` (open): connected vertex-transitive graphs with `2 δ + 1 < n`.

`main` is a case split on `n ≤ 2 δ + 1` (a connected graph is nonempty). This isolates the
textbook dense case; it is not progress on the conjecture, which `H2` keeps for sparse graphs.
-/

namespace OMA.R_LovaszConjecture_lovasz_conjecture_R1

/-- Dirac-type theorem for paths: `n ≤ 2 δ + 1` gives a Hamiltonian path. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Nonempty V → Fintype.card V ≤ 2 * G.minDegree + 1 → LovaszConjecture.HasHamiltonianPath G

/-- The open part: sparse connected vertex-transitive graphs. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → LovaszConjecture.IsVertexTransitive G → 2 * G.minDegree + 1 < Fintype.card V →
      LovaszConjecture.HasHamiltonianPath G

theorem main : H1 → H2 → type_of% @LovaszConjecture.lovasz_conjecture := by
  intro h1 h2 V _ _ G _ hconn htrans
  by_cases hd : Fintype.card V ≤ 2 * G.minDegree + 1
  · exact h1 G hconn.nonempty hd
  · exact h2 G hconn htrans (by omega)

end OMA.R_LovaszConjecture_lovasz_conjecture_R1
