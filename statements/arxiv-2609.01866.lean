import Mathlib

/-!
# The multiorbital bivariate chromatic polynomial

Source: https://arxiv.org/abs/2609.01866v5
Credit: @pmaster

Does equality of the multiorbital polynomials for two graph actions of the
same group imply equality of their ordinary orbital polynomials? Polynomial
equality is expressed by equality at all integer color counts 0 ≤ y ≤ x.
This domain determines a bivariate polynomial over ℚ.
-/

namespace OMA.S_arxiv_2609_01866

/-- The group operation is written additively. Commutativity is not assumed. -/
structure GraphAction (G V : Type) [AddGroup G] where
  graph : SimpleGraph V
  act : G → V → V
  zero_act : ∀ v, act 0 v = v
  add_act : ∀ g h v, act (g + h) v = act g (act h v)
  adj_act : ∀ g v w, graph.Adj (act g v) (act g w) ↔ graph.Adj v w

variable {G V : Type} [AddGroup G] [Fintype G] [DecidableEq G]
variable [Fintype V] [DecidableEq V]

/-- All subgroups of the finite group, represented by their underlying finsets. -/
def subgroups (G : Type) [AddGroup G] [Fintype G] [DecidableEq G] : Finset (Finset G) :=
  Finset.univ.powerset.filter fun H =>
    0 ∈ H ∧ (∀ a ∈ H, -a ∈ H) ∧ (∀ a ∈ H, ∀ b ∈ H, a + b ∈ H)

def subgroupWeight (g : G) : ℚ :=
  ∑ H ∈ (subgroups G).filter (g ∈ ·), (H.card : ℚ)⁻¹

noncomputable def isolated (A : GraphAction G V) : Finset V := by
  classical exact Finset.univ.filter (fun v => ∀ w, ¬ A.graph.Adj v w)

/-- Burnside's count of cycles on an invariant set. The list of |G| multiples
of g runs through the cyclic subgroup equally often. -/
def cycles (A : GraphAction G V) (S : Finset V) (g : G) : ℕ :=
  (∑ j ∈ Finset.range (Fintype.card G), (S.filter (fun v => A.act (j • g) v = v)).card)
    / Fintype.card G

/-- Fixed colorings of the graph with x colors, the first y of which must be
proper. Isolated vertex cycles each supply an independent factor x. On the
remaining vertices we count invariant colorings directly. This also handles
edges whose endpoints belong to a single cycle. -/
noncomputable def quotientCount (A : GraphAction G V) (g : G) (x y : ℕ) : ℕ :=
  x ^ cycles A (isolated A) g *
    Nat.card {f : {v // v ∉ isolated A} → Fin x //
      (∀ v w, A.act g v.val = w.val → f v = f w) ∧
      (∀ v w, A.graph.Adj v.val w.val → f v = f w → y ≤ (f v).val)}

noncomputable def orbital (A : GraphAction G V) (x y : ℕ) : ℚ :=
  (∑ g : G, (quotientCount A g x y : ℚ)) / Fintype.card G

noncomputable def multiorbital (A : GraphAction G V) (x y : ℕ) : ℚ :=
  ∑ g : G, subgroupWeight g * quotientCount A g x y

/-- Whether equality of the multiorbital evaluations forces equality of the orbital evaluations. -/
theorem main : ∀ (K U W : Type) [AddGroup K] [Fintype K] [DecidableEq K]
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (A : GraphAction K U) (B : GraphAction K W),
    (∀ x y, y ≤ x → multiorbital A x y = multiorbital B x y) →
    ∀ x y, y ≤ x → orbital A x y = orbital B x y := by
  sorry

end OMA.S_arxiv_2609_01866
