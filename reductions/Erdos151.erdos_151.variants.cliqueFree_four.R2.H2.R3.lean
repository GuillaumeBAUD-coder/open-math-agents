import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R2
import Mathlib

/-!
A reduction of the four-clique-free case using pairs of color classes.

An edge is bare if it belongs to no triangle. In the union of two independent
color classes, deleting one endpoint per bare edge leaves a set containing no
entire nontrivial maximal clique. Summing this bound over all color pairs
gives the independent counting problem H2. For eight colors, H1 and H2 force
at least 28 bare edges in any counterexample in the range of the parent step.
-/

open Finset SimpleGraph
open scoped Classical

namespace OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R3

/-- The numerical Ramsey bound follows from finite triangle-free witnesses
for orders 40 to 71 and a 32-vertex block of independence number at most 8. -/
def H1 : Prop :=
  ∀ n : ℕ, 10 ≤ Erdos151.H n → 4 * Erdos151.H n ≤ n

/-- Sum the free-set bound over pairs of classes in a proper coloring.
The use of an ordered orientation counts each bare edge exactly once. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    let b := (univ.filter (fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ ¬ ∃ z, G.Adj e.1 z ∧ G.Adj e.2 z)).card
    ∀ q : ℕ, 2 ≤ q → G.Colorable q →
      (q - 1) * n ≤ q.choose 2 * (n - G.cliqueTransversalNumber) + b

/-- The remaining graphs satisfy the necessary density inequalities for every
proper coloring. In particular, an eight-colorable candidate has at least
28 bare edges. -/
def H3 : Prop :=
  ∀ n : ℕ, 10 ≤ Erdos151.H n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
    (∀ v, (univ.filter (G.Adj v)).card < Erdos151.H n) →
    (∃ x y, G.Adj x y ∧ 3 ≤ (univ.filter fun z => G.Adj x z ∧ G.Adj y z).card) →
    let b := (univ.filter (fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ ¬ ∃ z, G.Adj e.1 z ∧ G.Adj e.2 z)).card
    (∀ q : ℕ, 2 ≤ q → G.Colorable q →
      (q - 1) * n ≤ q.choose 2 * (Erdos151.H n - 1) + b) →
    (G.Colorable 8 → 28 ≤ b) →
    G.cliqueTransversalNumber ≤ n - Erdos151.H n

theorem main : H1 → H2 → H3 → OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2.H2 := by
  intro hRamsey hcount hrest n hn G hfree hdegree hbook
  by_contra hfail
  have hsmall : n - G.cliqueTransversalNumber ≤ Erdos151.H n - 1 := by omega
  let b := (univ.filter (fun e : Fin n × Fin n =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ ¬ ∃ z, G.Adj e.1 z ∧ G.Adj e.2 z)).card
  have hdensity (q : ℕ) (hq : 2 ≤ q) (hcolor : G.Colorable q) :
      (q - 1) * n ≤ q.choose 2 * (Erdos151.H n - 1) + b :=
    (hcount n G q hq hcolor).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left (q.choose 2) hsmall) b)
  have height (hcolor : G.Colorable 8) : 28 ≤ b := by
    have h := hdensity 8 (by decide) hcolor
    change 7 * n ≤ 28 * (Erdos151.H n - 1) + b at h
    have hn' := hRamsey n hn
    omega
  exact hfail (hrest n hn G hfree hdegree hbook hdensity height)

end OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R2_H2_R3
