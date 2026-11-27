import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic

/-! Index the two-secants by the pairs of code points left uncovered by the first eight rows. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1

open Finset
open scoped Classical BigOperators

def H1 : Prop :=
  ∀ (P : Type) [DecidableEq P] (S : Finset P), S.card = 16 →
  ∀ (A : Fin 8 → P → Bool) (B : Fin 72 → P → Bool),
    (∀ a, (S.filter fun p => A a p = true).card = 4) →
    (∀ b, (S.filter fun p => B b p = true).card = 2) →
    (∀ p q, p ≠ q → ∀ l m : Fin 8 ⊕ Fin 72,
      Sum.elim A B l p = true → Sum.elim A B l q = true →
      Sum.elim A B m p = true → Sum.elim A B m q = true → l = m) →
    let C := S.powersetCard 2 \
      (Finset.univ : Finset (Fin 8)).biUnion (fun a => (S.filter fun p => A a p = true).powersetCard 2)
    ∃ e : Fin 72 ≃ ↥C, ∀ b, (e b).val = S.filter fun p => B b p = true

def H2 : Prop :=
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  ¬ ∃ (S : Finset P) (A : Fin 8 → P → Bool),
    S.card = 16 ∧
    (∀ a, (S.filter fun p => A a p = true).card = 4) ∧
    (∀ a (q : Q), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) ∧
    (∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b)) ∧
    (∀ a i, A a (.inr i) = false) ∧
    let C := S.powersetCard 2 \
      (Finset.univ : Finset (Fin 8)).biUnion (fun a => (S.filter fun p => A a p = true).powersetCard 2)
    ∃ B : ↥C → P → Bool,
      let M := Sum.elim A B
      let c (p : P) := (Finset.univ.filter fun a => A a p = true).card
      let d (p : P) := (Finset.univ.filter fun b => B b p = true).card
      (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
      (∀ b p, p ∈ S → (B b p = true ↔ p ∈ b.val)) ∧
      (∀ p ∈ S, c p = 2 ∧ d p = 9) ∧
      (∀ p ∉ S, 2*c p + d p = 8) ∧
      (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
      (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
        M m p = true → M m q = true → l = m) ∧
      (∀ p ∈ S, ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
      word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187] : List Nat)

theorem saturated_column {R P : Type} [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]
    (M : R → P → Bool) (pointCount : Fintype.card P = 111)
    (rowSize : ∀ l, (Finset.univ.filter fun q => M l q = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (p : P) (onSize : (Finset.univ.filter fun l => M l p = true).card = 11) :
    ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true := by
  let on := Finset.univ.filter fun l => M l p = true
  let ray (l : R) := (Finset.univ.filter fun q => M l q = true).erase p
  let covered := on.biUnion ray
  let other : Finset P := Finset.univ.erase p
  have rays_disjoint : (on : Set R).PairwiseDisjoint ray := by
    intro a ha b hb different
    change Disjoint (ray a) (ray b)
    rw [Finset.disjoint_left]
    intro q qa qb
    obtain ⟨ne,in_a⟩ := Finset.mem_erase.mp qa
    obtain ⟨_,in_b⟩ := Finset.mem_erase.mp qb
    exact different (columnPairs p q ne.symm a b
      (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2 (Finset.mem_filter.mp in_a).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 (Finset.mem_filter.mp in_b).2)
  have ray_size (l : R) (hl : l ∈ on) : (ray l).card = 10 := by
    change ((Finset.univ.filter fun q => M l q = true).erase p).card = 10
    have on_l : p ∈ Finset.univ.filter (fun q => M l q = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem on_l,rowSize]
  have matched : covered.card = 110 := by
    change (on.biUnion ray).card = 110
    rw [Finset.card_biUnion rays_disjoint,Finset.sum_congr rfl ray_size,Finset.sum_const,Nat.nsmul_eq_mul]
    change (Finset.univ.filter fun l => M l p = true).card * 10 = 110
    rw [onSize]
  have other_size : other.card = 110 := by
    change ((Finset.univ : Finset P).erase p).card = 110
    rw [Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,pointCount]
  have subset : covered ⊆ other := by
    intro q hq
    obtain ⟨l,_,loc⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp loc).1,Finset.mem_univ _⟩
  have full : covered = other := by
    apply Finset.eq_of_subset_of_card_le subset
    rw [other_size,matched]
  intro q ne
  have elsewhere : q ∈ other := Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ _⟩
  have some_ray : q ∈ covered := full.symm ▸ elsewhere
  obtain ⟨l,hl,present⟩ := Finset.mem_biUnion.mp some_ray
  have lp := (Finset.mem_filter.mp hl).2
  have lq := (Finset.mem_filter.mp (Finset.mem_erase.mp present).2).2
  exact ⟨l,⟨lp,lq⟩,fun m hm => columnPairs p q ne m l hm.1 hm.2 lp lq⟩

lemma count_reindexed {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl

lemma count_incidence_sum {X Y : Type} [Fintype X] [Fintype Y]
    (P : X ⊕ Y → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (.inl x)).card +
      (Finset.univ.filter fun y => P (.inr y)).card := by
  have same : Finset.univ.filter P = (Finset.univ.filter fun x => P (.inl x)).disjSum
      (Finset.univ.filter fun y => P (.inr y)) := by
    ext l
    cases l <;> simp [Finset.mem_filter]
  rw [same,Finset.card_disjSum]

set_option maxRecDepth 4096 in
theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro indexing impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1.H2
  dsimp only
  rintro ⟨M,S,cardS,rows,asizes,bsizes,inside,outside,oldR,oldP,pairs,private_,hidden,graph⟩
  classical
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let A (a : Fin 8) (p : P) := M (.inl a) p
  let B (b : Fin 72) (p : P) := M (.inr b) p
  let candidates := S.powersetCard 2 \
    (Finset.univ : Finset (Fin 8)).biUnion (fun a => (S.filter fun p => A a p = true).powersetCard 2)
  have sum_form (l : Fin 8 ⊕ Fin 72) (p : P) : Sum.elim A B l p = M l p := by
    cases l <;> rfl
  have unique : ∀ p q, p ≠ q → ∀ l m, Sum.elim A B l p = true → Sum.elim A B l q = true →
      Sum.elim A B m p = true → Sum.elim A B m q = true → l = m := by
    simpa only [sum_form] using oldP
  obtain ⟨e,desc⟩ : ∃ e : Fin 72 ≃ ↥candidates, ∀ b, (e b).val = S.filter fun p => B b p = true :=
    indexing P S cardS A B asizes bsizes unique
  let D (b : ↥candidates) (p : P) := B (e.symm b) p
  let N := Sum.elim A D
  let r := Equiv.sumCongr (Equiv.refl (Fin 8)) e.symm
  have entry (l : Fin 8 ⊕ ↥candidates) (p : P) : N l p = M (r l) p := by
    cases l <;> rfl
  have rowSize (l : Fin 8 ⊕ ↥candidates) : (Finset.univ.filter fun p => N l p = true).card = 11 := by
    simpa only [entry] using rows (r l)
  have bSize (p : P) :
      (Finset.univ.filter fun b : ↥candidates => D b p = true).card =
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card :=
    count_reindexed e.symm (fun b => M (.inr b) p = true)
  have newR (l m : Fin 8 ⊕ ↥candidates) (different : l ≠ m) : ∃! p, N l p = true ∧ N m p = true := by
    simpa only [entry] using oldR (r l) (r m) (fun same => different (r.injective same))
  have newP (p q : P) (different : p ≠ q) (l m : Fin 8 ⊕ ↥candidates)
      (lp : N l p = true) (lq : N l q = true) (mp : N m p = true) (mq : N m q = true) : l = m :=
    r.injective (oldP p q different (r l) (r m) ((entry l p) ▸ lp) ((entry l q) ▸ lq)
      ((entry m p) ▸ mp) ((entry m q) ▸ mq))
  have full (p : P) (hp : p ∈ S) : ∀ q, p ≠ q → ∃! l, N l p = true ∧ N l q = true := by
    have both := inside p hp
    have all : (Finset.univ.filter fun l => N l p = true).card = 11 := by
      rw [count_incidence_sum]
      change (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card +
        (Finset.univ.filter fun b : ↥candidates => D b p = true).card = 11
      rw [bSize]
      exact congrArg₂ Nat.add both.1 both.2
    have pointCount : Fintype.card P = 111 := by decide +kernel
    exact saturated_column N pointCount rowSize newP p all
  have indexed (b : ↥candidates) (p : P) (hp : p ∈ S) : D b p = true ↔ p ∈ b.val := by
    have same := desc (e.symm b)
    rw [Equiv.apply_symm_apply] at same
    rw [same,Finset.mem_filter]
    exact ⟨fun hd => ⟨hp,hd⟩, fun both => both.2⟩
  apply impossible
  refine ⟨S,A,cardS,asizes,pairs,private_,hidden,D,rowSize,indexed,?_,?_,newR,newP,full,?_⟩
  · intro p hp
    change (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : ↥candidates => D b p = true).card = 9
    rw [bSize]
    exact inside p hp
  · intro p hp
    change 2 * (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card +
      (Finset.univ.filter fun b : ↥candidates => D b p = true).card = 8
    rw [bSize]
    exact outside p hp
  · exact graph


end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1
