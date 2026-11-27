import Mathlib

/-!
# Hoàng–Reed Conjecture

Source: https://www.openproblemgarden.org/op/hoand_reed_conjecture
Credit: @ishaanzee

**Conjecture** (C. T. Hoàng, B. Reed). Every digraph in which each vertex has outdegree at least
`k` contains `k` directed cycles `C₁, …, C_k` such that `C_j` meets `C₁ ∪ ⋯ ∪ C_{j-1}` in at most
one vertex, `2 ≤ j ≤ k`.

(Not even known for `k = 3`; it would imply the Caccetta–Häggkvist conjecture.)

Formalization:
* A digraph on a finite set `V` is a loopless relation `D` (`D u v` is the arc `u → v`; no
  parallel arcs, 2-cycles allowed).
* A directed cycle is a list of at least two distinct vertices `v₀, …, v_{m-1}` with an arc from
  each `vᵢ` to `v_{i+1 mod m}` (`finRotate`).
* The cycles are `C : Fin k → List V`; for each `j` (`j ≥ 1` in `0`-based indexing), at most one
  vertex of `C j` lies on an earlier cycle `C i`, `i < j`.
-/

namespace OMA.S_opg_hoand_reed_conjecture

/-- `l` is a directed cycle of `D`. -/
def IsDirCycle {V : Type*} (D : V → V → Prop) (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧ ∀ i : Fin l.length, D (l.get i) (l.get (finRotate _ i))

/-- **Hoàng–Reed conjecture.** -/
theorem main : ∀ (k : ℕ) (V : Type) [Fintype V] [DecidableEq V] (D : V → V → Prop) [DecidableRel D],
    (∀ v, ¬ D v v) → (∀ v, k ≤ (Finset.univ.filter fun w => D v w).card) →
      ∃ C : Fin k → List V, (∀ j, IsDirCycle D (C j)) ∧
        ∀ j : Fin k, ((C j).toFinset ∩
          (Finset.univ.filter fun i : Fin k => i < j).biUnion fun i => (C i).toFinset).card ≤ 1 := by
  sorry

end OMA.S_opg_hoand_reed_conjecture
