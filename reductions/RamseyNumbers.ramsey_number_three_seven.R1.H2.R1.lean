import OMAReductions.R_RamseyNumbers_ramsey_number_three_seven_R1

/-!
The last step of Graver and Yackel's proof of the upper bound on `R(3,7)` counts
quadrilaterals through each vertex of a hypothetical counterexample. Regularity
and the local count are the two residual hypotheses. The incidence count below
makes the contradiction independent of any classification of small graphs.

Reference: Graver and Yackel, *Some Graph Theoretic Results Associated with
Ramsey's Theorem*, Journal of Combinatorial Theory 4 (1968), 125–175, pp. 145–147.
-/

namespace OMA.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1

open SimpleGraph

private def cross {V : Type*} (G : SimpleGraph V) (p q : V × V) : Prop :=
  G.Adj p.1 q.1 ∧ G.Adj p.1 q.2 ∧ G.Adj p.2 q.1 ∧ G.Adj p.2 q.2

variable {V : Type*} [LinearOrder V]

/-- A quadrilateral rooted at `v`: record its opposite vertex and order its two neighbors. -/
private def Rooted (G : SimpleGraph V) (v : V) :=
  {p : V × (V × V) // v ≠ p.1 ∧ p.2.1 < p.2.2 ∧ cross G (v, p.1) p.2}

private def Oriented (G : SimpleGraph V) :=
  {p : (V × V) × (V × V) //
    p.1.1 ≠ p.1.2 ∧ p.2.1 < p.2.2 ∧ cross G p.1 p.2}

private def firstLt (G : SimpleGraph V) (p : Oriented G) : Prop :=
  p.val.1.1 < p.val.1.2

private def Ordered (G : SimpleGraph V) := Subtype (firstLt G)

private def pairLt (G : SimpleGraph V) (p : Ordered G) : Prop :=
  p.val.val.1.1 < p.val.val.2.1

private def rootedEquiv (G : SimpleGraph V) : (Σ v, Rooted G v) ≃ Oriented G where
  toFun x := ⟨((x.1, x.2.val.1), x.2.val.2), x.2.property⟩
  invFun x := ⟨x.val.1.1, ⟨(x.val.1.2, x.val.2), x.property⟩⟩
  left_inv := by rintro ⟨v, ⟨⟨u, a, b⟩, h⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨v, u⟩, a, b⟩, h⟩; rfl

private def flipFirst (G : SimpleGraph V) (p : Oriented G) : Oriented G :=
  ⟨(p.val.1.swap, p.val.2), p.property.1.symm, p.property.2.1,
    p.property.2.2.2.2.1, p.property.2.2.2.2.2, p.property.2.2.1, p.property.2.2.2.1⟩

private theorem flipFirst_involutive (G : SimpleGraph V) :
    Function.Involutive (flipFirst G) := by
  rintro ⟨⟨⟨v, u⟩, a, b⟩, h⟩
  rfl

private theorem flipFirst_switch (G : SimpleGraph V) (p : Oriented G) :
    firstLt G (flipFirst G p) ↔ ¬ firstLt G p := by
  change p.val.1.2 < p.val.1.1 ↔ ¬ p.val.1.1 < p.val.1.2
  exact ⟨not_lt_of_gt, fun h => lt_of_le_of_ne (le_of_not_gt h) p.property.1.symm⟩

private def flipPairs (G : SimpleGraph V) (p : Ordered G) : Ordered G :=
  ⟨⟨(p.val.val.2, p.val.val.1), p.val.property.2.1.ne, p.property,
    p.val.property.2.2.1.symm, p.val.property.2.2.2.2.1.symm,
    p.val.property.2.2.2.1.symm, p.val.property.2.2.2.2.2.symm⟩,
    p.val.property.2.1⟩

private theorem flipPairs_involutive (G : SimpleGraph V) :
    Function.Involutive (flipPairs G) := by
  rintro ⟨⟨⟨⟨v, u⟩, a, b⟩, h⟩, h'⟩
  rfl

private theorem flipPairs_switch (G : SimpleGraph V) (p : Ordered G) :
    pairLt G (flipPairs G p) ↔ ¬ pairLt G p := by
  change p.val.val.2.1 < p.val.val.1.1 ↔ ¬ p.val.val.1.1 < p.val.val.2.1
  exact ⟨not_lt_of_gt, fun h =>
    lt_of_le_of_ne (le_of_not_gt h) p.val.property.2.2.1.ne.symm⟩

/-- An involution switching the two sides of a predicate gives two copies of either side. -/
private def splitBool {α : Type*} (p : α → Prop) [DecidablePred p]
    (s : α → α) (hs : Function.Involutive s) (hp : ∀ x, p (s x) ↔ ¬ p x) :
    α ≃ Bool × Subtype p where
  toFun x := if h : p x then (false, ⟨x, h⟩) else (true, ⟨s x, (hp x).mpr h⟩)
  invFun x := if x.1 = true then s x.2.val else x.2.val
  left_inv x := by
    by_cases h : p x <;> simp [h, hs x]
  right_inv := by
    rintro ⟨b, x, hx⟩
    cases b
    · simp [hx]
    · simp [show ¬ p (s x) from fun h => (hp x).mp h hx, hs x]

private theorem incidence_divisible_by_four [Fintype V] (G : SimpleGraph V) :
    4 ∣ ∑ v, Nat.card (Rooted G v) := by
  classical
  let (v : V) : Fintype (Rooted G v) := by
    unfold Rooted
    exact Fintype.ofFinite _
  let : Fintype (Oriented G) := by
    unfold Oriented
    exact Fintype.ofFinite _
  let : Fintype (Ordered G) := by
    unfold Ordered
    exact Fintype.ofFinite _
  let : Fintype (Subtype (pairLt G)) := Fintype.ofFinite _
  let e₁ := splitBool (firstLt G) (flipFirst G) (flipFirst_involutive G) (flipFirst_switch G)
  let e₂ := splitBool (pairLt G) (flipPairs G) (flipPairs_involutive G) (flipPairs_switch G)
  have h := Fintype.card_congr ((rootedEquiv G).trans
    (e₁.trans ((Equiv.refl Bool).prodCongr e₂)))
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool] at h
  simp_rw [Nat.card_eq_fintype_card]
  rw [h]
  exact ⟨Fintype.card (Subtype (pairLt G)), by omega⟩

/-- A hypothetical graph with degrees five or six is in fact six-regular. -/
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
    Gᶜ.CliqueFree 7 → (∀ v, G.degree v = 5 ∨ G.degree v = 6) →
    ∀ v, G.degree v = 6

/-- The local quadrilateral count in a hypothetical six-regular counterexample. -/
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 23)) [DecidableRel G.Adj], G.CliqueFree 3 →
    Gᶜ.CliqueFree 7 → (∀ v, G.degree v = 6) →
    ∀ v, Nat.card {p : Fin 23 × (Fin 23 × Fin 23) //
      v ≠ p.1 ∧ p.2.1 < p.2.2 ∧
      G.Adj v p.2.1 ∧ G.Adj v p.2.2 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.1 p.2.2} = 18

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_three_seven_R1.H2 := by
  intro regular count G dec ht hd _ hc
  have h := incidence_divisible_by_four G
  have rootedCount (v : Fin 23) : Nat.card (Rooted G v) = 18 :=
    count G ht hc (regular G ht hc hd) v
  simp_rw [rootedCount] at h
  norm_num at h

end OMA.R_RamseyNumbers_ramsey_number_three_seven_R1_H2_R1
