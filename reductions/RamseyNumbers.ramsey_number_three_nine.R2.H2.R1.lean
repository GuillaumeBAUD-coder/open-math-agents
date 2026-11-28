import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R2_H2_R1

open SimpleGraph Finset

/-- The whole graph has minimum degree at least four. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 → D.edgeFinset.card = 51 →
    ∀ w, 4 ≤ D.degree w

/-- The exterior of a degree-four root has minimum degree at least three. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 → D.edgeFinset.card = 51 →
    (∀ w, 4 ≤ D.degree w) → ∀ v, D.degree v = 4 →
    let B := Dᶜ.neighborFinset v
    let E := D.induce (B : Set V)
    ∀ x : B, 3 ≤ E.degree x

/-- Classify the graph when that exterior has minimum degree three. -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 → D.edgeFinset.card = 51 →
    (∀ w, 4 ≤ D.degree w) → ∀ v, D.degree v = 4 →
    (let B := Dᶜ.neighborFinset v
     let E := D.induce (B : Set V)
     (∀ x : B, 3 ≤ E.degree x) ∧ ∃ x : B, E.degree x = 3) →
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc := fun vs : List V => (vs.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (D.Adj v x)) :: p.2)) ([],[])).2
    ∃ vs : List V, vs.Nodup ∧ (∀ x, x ∈ vs) ∧ enc vs ∈
      [[0x380a8,0x140a8,0x3081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x91,0x4,0x11,0x4,0x1,0x3,0x0,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0x100a8,0xb081,0x2480,0x4190,0x4c4,0x10a8,0x1a8,0x444,0x51,0x44,0x1,0x4,0x1,0x1,0x2,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0xc0a8,0x3081,0x2480,0x4190,0x10c4,0x10a8,0x4a8,0x444,0x111,0x44,0x11,0x4,0x1,0x1,0x0,0x8,0x4,0x2,0x1,0x0],
       [0x380a8,0x40a8,0x7081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x11,0x84,0x1,0x4,0x5,0x1,0x4,0x8,0x4,0x2,0x1,0x0]]

/-- An exterior of a degree-four root cannot have all degrees at least four. -/
def H4 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
    Fintype.card V = 21 → D.CliqueFree 3 → Dᶜ.CliqueFree 7 → D.edgeFinset.card = 51 →
    (∀ w, 4 ≤ D.degree w) → ∀ v, D.degree v = 4 →
    (let B := Dᶜ.neighborFinset v
     let E := D.induce (B : Set V)
     ∀ x : B, 4 ≤ E.degree x) →
    False

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2 := by
  intro lower outside middle upper V _ _ D _ order tri anti edges
  classical
  have min4 := lower V D order tri anti edges
  have root : ∃ v, D.degree v = 4 := by
    by_contra! none
    have five (v : V) : 5 ≤ D.degree v := by have a := min4 v; have b := none v; omega
    have bound : (∑ _v : V, (5 : Nat)) ≤ ∑ v : V, D.degree v :=
      Finset.sum_le_sum (fun v _ => five v)
    rw [D.sum_degrees_eq_twice_card_edges, edges] at bound
    simp only [sum_const, card_univ, nsmul_eq_mul, order] at bound
    omega
  obtain ⟨v,degree⟩ := root
  let B := Dᶜ.neighborFinset v
  let E := D.induce (B : Set V)
  have atLeastThree : ∀ x : B, 3 ≤ E.degree x := outside V D order tri anti edges min4 v degree
  by_cases found : ∃ x : B, E.degree x = 3
  · exact middle V D order tri anti edges min4 v degree ⟨atLeastThree,found⟩
  · have atLeastFour (x : B) : 4 ≤ E.degree x := by
      have low := atLeastThree x
      by_contra! small
      exact found ⟨x,by omega⟩
    exact (upper V D order tri anti edges min4 v degree atLeastFour).elim

end OMA.R_RamseyNumbers_ramsey_number_three_nine_R2_H2_R1