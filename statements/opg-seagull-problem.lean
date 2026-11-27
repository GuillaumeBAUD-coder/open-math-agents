import Mathlib

/-!
# Seagull problem

Source: https://www.openproblemgarden.org/op/seagull_problem
Credit: @Hyvok

Informal statement (Open Problem Garden, conjecture attributed by M. DeVos to Paul D. Seymour,
possibly suggested independently by Mader and others):
Every `n`-vertex graph with no independent set of size `3` has a complete graph on `≥ n/2`
vertices as a minor.
It is a consequence of Hadwiger's conjecture. Reference for the best known bound
`(n + ω(G))/3`: K. Kawarabayashi, M. Plummer, B. Toft, Improvements of the theorem of Duchet
and Meyniel on Hadwiger's Conjecture, J. Combin. Theory Ser. B 95 (2005), 152-167.

Formalization notes:
* Graphs are finite simple graphs `G : SimpleGraph V` on a `Fintype` vertex type `V`;
  `n = Fintype.card V`.
* No independent set of size `3` is Mathlib's `G.IndepSetFree 3` (no three pairwise
  nonadjacent distinct vertices), i.e. independence number at most `2`.
* `G` has a `K_t`-minor (`HasCompleteMinor G t`) when there are `t` pairwise disjoint vertex
  sets (branch sets), each nonempty and inducing a connected subgraph (Mathlib's `Connected`
  includes nonemptiness), with an edge of `G` between any two of them. This is the standard
  equivalent of contracting/deleting to obtain `K_t`.
* A complete graph on at least `n/2` vertices: since the number of vertices `t` is a natural
  number, `t ≥ n/2` (real division) is written `n ≤ 2 * t`, i.e. `t ≥ ⌈n/2⌉`.
* The empty graph (`n = 0`) is included; it is trivially fine with `t = 0`.
-/

namespace OMA.S_opg_seagull_problem

/-- `G` has a `K_t`-minor: `t` pairwise disjoint connected branch sets, any two joined by an
edge of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V, (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- **Seagull problem.** Every finite graph on `n` vertices with no independent set of size
`3` has a complete minor on at least `n/2` vertices. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IndepSetFree 3 →
      ∃ t : ℕ, Fintype.card V ≤ 2 * t ∧ HasCompleteMinor G t := by
  sorry

end OMA.S_opg_seagull_problem
