import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

/-! Exclude starting patterns whose residual pairs cannot be partitioned into triangles. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1

open Finset
open scoped BigOperators

def H1 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 2 ∧ 7 ≤ x ∧ x ≤ 9 ∧ (x ≠ 7 ∨ ¬ (∃ p q : Fin 19, (C p).card = 3 ∧ (C q).card = 3 ∧ C p ∪ C q = Finset.univ)) ∧
    let patterns : List (List Nat) := [[3,5,6,9,10,17,28,33,50], [3,5,6,9,10,20,24,44,49], [3,5,9,14,18,20,34,36,56]]
    ∃ e : Equiv.Perm (Fin 6), ∃ i : Fin 3,
      (F.image fun X => ∑ a ∈ X.map e.toEmbedding, (2 : Nat)^a.val) = (patterns[i.val]!).toFinset

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 2 ∧ 7 ≤ x ∧ x ≤ 9 ∧ (x ≠ 7 ∨ ¬ (∃ p q : Fin 19, (C p).card = 3 ∧ (C q).card = 3 ∧ C p ∪ C q = Finset.univ)) ∧
    let patterns : List (List Nat) := [[3,5,6,9,10,17,28,33,50], [3,5,6,9,10,20,24,44,49], [3,5,9,14,18,20,34,36,56]]
    ¬ (∃ e : Equiv.Perm (Fin 6), ∃ i : Fin 3,
      (F.image fun X => ∑ a ∈ X.map e.toEmbedding, (2 : Nat)^a.val) = (patterns[i.val]!).toFinset)

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1.H2 := by
  intro noBad noOther
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1.H2
  dsimp only
  rintro ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,card2,lower,upper,complementRestriction⟩
  classical
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
  let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
  let patterns : List (List Nat) := [[3,5,6,9,10,17,28,33,50], [3,5,6,9,10,20,24,44,49], [3,5,9,14,18,20,34,36,56]]
  by_cases group : ∃ e : Equiv.Perm (Fin 6), ∃ i : Fin 3,
      (F.image fun X => ∑ a ∈ X.map e.toEmbedding, (2 : Nat)^a.val) = (patterns[i.val]!).toFinset
  · exact noBad ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,card2,lower,upper,complementRestriction,group⟩
  · exact noOther ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,card2,lower,upper,complementRestriction,group⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1
