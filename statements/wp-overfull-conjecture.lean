import Mathlib

/-!
# Overfull conjecture (Chetwynd–Hilton, 1986)

Source: https://en.wikipedia.org/wiki/Overfull_graph#Overfull_conjecture
Credit: @joshuadc11

A finite simple graph `G` on `n` vertices with maximum degree `Δ(G) > n / 3` is class 2
if and only if it has an overfull subgraph `S` satisfying `Δ(S) = Δ(G)`.

Formalization notes:
- As stated on the linked source page (`Overfull_graph#Overfull_conjecture`), the degree
  hypothesis is strict: `Δ(G) > n / 3`, written `Fintype.card V < 3 * G.maxDegree`.
- By Vizing's theorem, a graph is class 2 iff it is not class 1 (i.e. has no proper edge
  coloring using `G.maxDegree` colors).
- A graph `S` is overfull iff `|E(S)| > Δ(S) * ⌊|V(S)| / 2⌋`.
-/

namespace OMA.S_wp_overfull_conjecture

/-- A finite simple graph `G` is class 1 if it admits a proper edge-coloring with
`G.maxDegree` colors. -/
def IsClassOne {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∃ c : G.edgeSet → Fin G.maxDegree,
    ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) → c e₁ ≠ c e₂

/-- A finite simple graph `S` is overfull if `|E(S)| > Δ(S) * ⌊|V(S)| / 2⌋`. -/
def IsOverfull {W : Type*} [Fintype W] [DecidableEq W] (S : SimpleGraph W)
    [DecidableRel S.Adj] : Prop :=
  S.maxDegree * (Fintype.card W / 2) < S.edgeFinset.card

theorem main :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V < 3 * G.maxDegree →
      (¬ IsClassOne G ↔
        ∃ (U : Finset V) (S : SimpleGraph U) (_ : DecidableRel S.Adj),
          (∀ u v : U, S.Adj u v → G.Adj u.1 v.1) ∧
          S.maxDegree = G.maxDegree ∧
          IsOverfull S) := by
  sorry

end OMA.S_wp_overfull_conjecture
