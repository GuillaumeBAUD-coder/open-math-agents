import Mathlib

namespace OMA.S_mo_70899

open SimpleGraph

/-- Replace vertex `v` of `G` by `H`, preserving its adjacencies to outside vertices. -/
def substitute {V W : Type} (G : SimpleGraph V) (v : V) (H : SimpleGraph W) :
    SimpleGraph ({x : V // x ≠ v} ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a.val b.val
    | .inl a, .inr _ => G.Adj a.val v
    | .inr _, .inl b => G.Adj v b.val
    | .inr a, .inr b => H.Adj a b
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact G.adj_symm h
    · exact G.adj_symm h
    · exact G.adj_symm h
    · exact H.adj_symm h⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl a => exact G.irrefl h
    | inr a => exact H.irrefl h⟩

abbrev GraphClass := (V : Type) → SimpleGraph V → Prop

/-- A finite graph class closed under induced subgraphs, substitution, and complement.
Induced embeddings include graph isomorphisms. -/
def IsClosedComplementClass (C : GraphClass) : Prop :=
  (∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    (G ↪g H) → C W H → C V G) ∧
  (∀ {V W : Type} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (v : V),
    C V G → C W H → C _ (substitute G v H)) ∧
  (∀ (V : Type) [Finite V] (G : SimpleGraph V), C V G → C V Gᶜ)

/-- Inclusion between classes, restricted to finite graphs. -/
def ClassIncluded (C D : GraphClass) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), C V G → D V G

/-- Even with complement closure, the inclusion order of finite graph classes
contains an order copy of the power set of the natural numbers. -/
theorem main :
    ∃ C : Set ℕ → GraphClass,
      (∀ S, IsClosedComplementClass (C S)) ∧
      ∀ S T : Set ℕ, ClassIncluded (C S) (C T) ↔ S ⊆ T := by
  sorry

end OMA.S_mo_70899
