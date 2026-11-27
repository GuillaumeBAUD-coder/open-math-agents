import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-! Isolate the cases with one or two points incident with four of the eight heavy lines. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1

def H1 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    (∃ p ∉ S,
  let C := Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true
  C.card = 4 ∧ ∀ a b : Fin 8, a ≠ b →
    ((∃ q ∉ S, M (.inl a) q = true ∧ M (.inl b) q = true) ↔ (a ∈ C ↔ b ∈ C))) ∧ (∃ q ∉ S, A M q = 3)

def H2 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    ∃ p ∉ S,
      let C := Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true
      C.card = 4 ∧ (∀ a b : Fin 8, a ≠ b →
        ((∃ q ∉ S, M (.inl a) q = true ∧ M (.inl b) q = true) ↔ (a ∈ C ↔ b ∈ C))) ∧
      ∀ q ∉ S, q ≠ p → A M q ≤ 2

def H3 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    ∃ p ∉ S,
      let C := Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true
      C.card = 4 ∧ (∀ a b : Fin 8, a ≠ b →
        ((∃ q ∉ S, M (.inl a) q = true ∧ M (.inl b) q = true) ↔ (a ∈ C ↔ b ∈ C))) ∧
      ∃ q ∉ S, q ≠ p ∧ A M q = 4

theorem main : H1 → H2 → H3 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1.H2 := by
  intro unexpected single double
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1.H2
  dsimp only
  rintro ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,p,hp,four,side⟩
  classical
  let A (q : Fin 111) := (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card
  by_cases triple : ∃ q ∉ S, A q = 3
  · exact unexpected ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,⟨p,hp,four,side⟩,triple⟩
  by_cases extra : ∃ q ∉ S, q ≠ p ∧ A q = 4
  · exact double ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,p,hp,four,side,extra⟩
  apply single
  refine ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,p,hp,four,side,?_⟩
  intro q hq different
  change A q ≤ 2
  have formula := outside q hq
  change 2*A q + _ = 8 at formula
  have not_three : A q ≠ 3 := fun eq => triple ⟨q,hq,eq⟩
  have not_four : A q ≠ 4 := fun eq => extra ⟨q,hq,different,eq⟩
  omega

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1
