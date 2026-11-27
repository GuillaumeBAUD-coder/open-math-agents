import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-! Keep all visible columns and the five unmarked columns through one two-secant. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1_H2_R1

open Finset

def H1 : Prop :=
  let L := Fin 4 ⊕ Fin 4
  let V := (Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))
  let P := V ⊕ Fin 45
  let Q := V ⊕ Fin 5
  let U : Finset P := Finset.univ.filter fun x => ∃ a b : Fin 4, x = .inl (.inl (a,b))
  let A (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun a : L => M (.inl a) p = true).card
  let B (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card
  ∀ M : L ⊕ Fin 72 → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) →
    (∀ b : Fin 72, (U.filter fun p => M (.inr b) p = true).card = 2) →
    (∀ p ∈ U, A M p = 2 ∧ B M p = 9) →
    (∀ p ∉ U, 2*A M p + B M p = 8) →
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) →
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) →
      (∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b)) →
      (∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b)) →
      (∀ a : Fin 4, ∀ i : Fin 2,
        M (.inl (.inl a)) (.inl (.inr (.inl i))) = decide (i = 0) ∧
        M (.inl (.inr a)) (.inl (.inr (.inl i))) = decide (i = 1)) →
      (∀ a b i, M (.inl a) (.inl (.inr (.inr (b,i)))) = decide (a = b)) →
    (∀ a i, M (.inl a) (.inr i) = false) →
    ∃ f : Q ↪ P, (∀ v : V, f (.inl v) = .inl v) ∧
      (∀ i : Fin 5, ∃ j : Fin 45, f (.inr i) = .inr j ∧ M (.inr 0) (.inr j) = true) ∧
      (∀ a : L, (Finset.univ.filter fun x => M (.inl a) (f x) = true).card = 11) ∧
      (∀ a : L, ∀ l : L ⊕ Fin 72, .inl a ≠ l → ∃! x, M (.inl a) (f x) = true ∧ M l (f x) = true) ∧
      (∀ l : L ⊕ Fin 72, .inr 0 ≠ l → ∃! x, M (.inr 0) (f x) = true ∧ M l (f x) = true) ∧
      ∀ p : Fin 4 × Fin 4, ∀ x : Q, .inl (.inl p) ≠ x →
        ∃! l, M l (f (.inl (.inl p))) = true ∧ M l (f x) = true

def H2 : Prop :=
  let L := Fin 4 ⊕ Fin 4
  let P := ((Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))) ⊕ Fin 5
  let U : Finset P := Finset.univ.filter fun x => ∃ a b : Fin 4, x = .inl (.inl (a,b))
  let A (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun a : L => M (.inl a) p = true).card
  let B (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card
  ¬ ∃ M : L ⊕ Fin 72 → P → Bool,
    (∀ a : L, (Finset.univ.filter fun p => M (.inl a) p = true).card = 11) ∧
    (∀ b : Fin 72, (U.filter fun p => M (.inr b) p = true).card = 2) ∧
    (∀ p ∈ U, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ U, 2*A M p + B M p = 8) ∧
    (∀ a : L, ∀ l : L ⊕ Fin 72, .inl a ≠ l → ∃! p, M (.inl a) p = true ∧ M l p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
      (∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b)) ∧
      (∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b)) ∧
      (∀ a : Fin 4, ∀ i : Fin 2,
        M (.inl (.inl a)) (.inl (.inr (.inl i))) = decide (i = 0) ∧
        M (.inl (.inr a)) (.inl (.inr (.inl i))) = decide (i = 1)) ∧
      (∀ a b i, M (.inl a) (.inl (.inr (.inr (b,i)))) = decide (a = b)) ∧
    (∀ a i, M (.inl a) (.inr i) = false) ∧
    (∀ i : Fin 5, M (.inr 0) (.inr i) = true) ∧
    (∀ l : L ⊕ Fin 72, .inr 0 ≠ l → ∃! x, M (.inr 0) x = true ∧ M l x = true) ∧
    ∀ p : Fin 4 × Fin 4, ∀ x : P, .inl (.inl p) ≠ x →
      ∃! l, M l (.inl (.inl p)) = true ∧ M l x = true


theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1.H2 := by
  intro select impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1.H2
  dsimp only
  rintro ⟨M,rows,twos,interior,exterior,rowPairs,columnPairs,horiz,vert,centers,private_,hidden⟩
  obtain ⟨f,visible,tailHits,rowSize,heavyMeet,secantMeet,codeMeet⟩ :=
    select M rows twos interior exterior rowPairs columnPairs horiz vert centers private_ hidden
  let L := Fin 4 ⊕ Fin 4
  let V := (Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))
  let Q := V ⊕ Fin 5
  let N (l : L ⊕ Fin 72) (q : Q) := M l (f q)
  let U : Finset Q := Finset.univ.filter fun q => ∃ a b : Fin 4, q = .inl (.inl (a,b))
  let W : Finset (V ⊕ Fin 45) := Finset.univ.filter fun q => ∃ a b : Fin 4, q = .inl (.inl (a,b))
  have onCode (q : Q) : q ∈ U ↔ f q ∈ W := by
    cases q with
    | inl v =>
      rw [visible]
      simp only [U,W,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,b,eq⟩
        exact ⟨a,b,congrArg (Sum.inl : V → V ⊕ Fin 45) (Sum.inl.inj eq)⟩
      · rintro ⟨a,b,eq⟩
        exact ⟨a,b,congrArg (Sum.inl : V → Q) (Sum.inl.inj eq)⟩
    | inr i =>
      obtain ⟨j,moved,_⟩ := tailHits i
      rw [moved]
      simp [U,W]
  have mappedU : U.map f = W := by
    ext p
    rw [Finset.mem_map]
    constructor
    · rintro ⟨q,on,rfl⟩
      exact (onCode q).mp on
    · intro hp
      obtain ⟨a,b,hp⟩ := (Finset.mem_filter.mp hp).2
      subst p
      exact ⟨.inl (.inl (a,b)),(onCode _).mpr (by
        rw [visible]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b,rfl⟩),visible _⟩
  apply impossible
  refine ⟨N,rowSize,?_,?_,?_,heavyMeet,?_,?_,?_,?_,?_,?_,?_,secantMeet,codeMeet⟩
  · intro b
    have count := twos b
    change (W.filter fun p => M (.inr b) p = true).card = 2 at count
    rwa [← mappedU,Finset.filter_map,Finset.card_map] at count
  · exact fun p hp => interior (f p) ((onCode p).mp hp)
  · exact fun p hp => exterior (f p) (fun h => hp ((onCode p).mpr h))
  · exact fun p q ne => columnPairs (f p) (f q) (fun eq => ne (f.injective eq))
  · intro a b j
    change M (.inl (.inl a)) (f (.inl (.inl (b,j)))) = _
    rw [visible,horiz]
  · intro a b j
    change M (.inl (.inr a)) (f (.inl (.inl (j,b)))) = _
    rw [visible,vert]
  · intro a i
    change (M (.inl (.inl a)) (f (.inl (.inr (.inl i)))) = _) ∧
      (M (.inl (.inr a)) (f (.inl (.inr (.inl i)))) = _)
    rw [visible]
    exact centers a i
  · intro a b i
    change M (.inl a) (f (.inl (.inr (.inr (b,i))))) = _
    rw [visible,private_]
  · intro a i
    obtain ⟨j,moved,_⟩ := tailHits i
    change M (.inl a) (f (.inr i)) = false
    rw [moved,hidden]
  · intro i
    obtain ⟨j,moved,onRow⟩ := tailHits i
    change M (.inr 0) (f (.inr i)) = true
    rwa [moved]

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1_H2_R1
