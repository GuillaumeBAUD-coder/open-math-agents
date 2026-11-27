import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-! Two exterior triple points cannot lie on the same four-secant. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1

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
    (∀ p ∉ S, A M p ≤ 3) ∧
    (Finset.univ.filter fun p => p ∉ S ∧ A M p = 3).card = 1

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
    (∀ p ∉ S, A M p ≤ 3) ∧
    (Finset.univ.filter fun p => p ∉ S ∧ A M p = 3).card = 2 ∧
    ∀ p q, p ≠ q → p ∉ S → q ∉ S → A M p = 3 → A M q = 3 →
      Disjoint (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true)
        (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true)

lemma second_row (A : Fin 8 → Fin 111 → Bool) (p : Fin 111)
    (rows : (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (on_a : A a p = true) : ∃! b, b ≠ a ∧ A b p = true := by
  let here : Finset (Fin 8) := Finset.univ.filter fun r => A r p = true
  have contains_a : a ∈ here := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on_a⟩
  have residual : (here.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem contains_a]
    exact Nat.sub_eq_of_eq_add rows
  obtain ⟨b, represented⟩ := Finset.card_eq_one.mp residual
  have iff_mem (r : Fin 8) : r ∈ here.erase a ↔ r ≠ a ∧ A r p = true := by
    simp [here, Finset.mem_erase, Finset.mem_filter]
  have hb : b ∈ here.erase a := by rw [represented]; exact Finset.mem_singleton_self b
  refine ⟨b,(iff_mem b).mp hb,fun r hr => ?_⟩
  have h := (iff_mem r).mpr hr
  rw [represented] at h
  exact Finset.mem_singleton.mp h

lemma cardinal_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (insideNeighbors : Fin 8 → Finset (Fin 8))
    (inside_mem : ∀ a b, b ∈ insideNeighbors a ↔ b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true)
    (share : ∀ a b, a ≠ b → ∃! p, (A a p = true ∧ A b p = true))
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (line_four : (S.filter fun p => A a p = true).card = 4) :
    (insideNeighbors a).card = 4 := by
  classical
  let on_line := S.filter fun p => A a p = true
  have second (p : Fin 111) (hp : p ∈ on_line) : ∃! b, b ≠ a ∧ A b p = true := by
    obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
    exact second_row A p (degree_two p inS) a onA
  let other (p : Fin 111) (hp : p ∈ on_line) := Classical.choose (second p hp)
  have other_good (p : Fin 111) (hp : p ∈ on_line) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp := Classical.choose_spec (second p hp)
  have bij : on_line.card = (insideNeighbors a).card := by
    apply Finset.card_bij other
    · intro p hp
      obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
      obtain ⟨different, onB⟩ := (other_good p hp).1
      exact (inside_mem a _).mpr ⟨different,p,inS,onA,onB⟩
    · intro p hp q hq eq
      obtain ⟨_, _, unique⟩ := share a (other p hp) ((other_good p hp).1.1.symm)
      have one : A a p = true ∧ A (other p hp) p = true :=
        ⟨(Finset.mem_filter.mp hp).2,(other_good p hp).1.2⟩
      have two : A a q = true ∧ A (other p hp) q = true :=
        ⟨(Finset.mem_filter.mp hq).2,eq.symm ▸ (other_good q hq).1.2⟩
      exact (unique p one).trans (unique q two).symm
    · intro b hb
      obtain ⟨different,p,inS,onA,onB⟩ := (inside_mem a b).mp hb
      have hp : p ∈ on_line := Finset.mem_filter.mpr ⟨inS,onA⟩
      exact ⟨p,hp,((other_good p hp).2 b ⟨different,onB⟩).symm⟩
  exact bij.symm.trans line_four

theorem exterior_cubic (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (insideNeighbors : Fin 8 → Finset (Fin 8))
    (inside_mem : ∀ a b, b ∈ insideNeighbors a ↔ b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true)
    (outsideNeighbors : Fin 8 → Finset (Fin 8))
    (outside_mem : ∀ a b, b ∈ outsideNeighbors a ↔ b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
    (share : ∀ a b, a ≠ b → ∃! p, (A a p = true ∧ A b p = true))
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4)
    (a : Fin 8) : (outsideNeighbors a).card = 3 := by
  classical
  have inner_four := cardinal_inner A S insideNeighbors inside_mem share degree_two a (line_four a)
  have separated : Disjoint (insideNeighbors a) (outsideNeighbors a) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    obtain ⟨different,p,inside,hp⟩ := (inside_mem a b).mp hb
    obtain ⟨_,q,outside,hq⟩ := (outside_mem a b).mp hc
    obtain ⟨_, _, unique⟩ := share a b different.symm
    have same := (unique p hp).trans (unique q hq).symm
    exact outside (same ▸ inside)
  have total : insideNeighbors a ∪ outsideNeighbors a = Finset.univ.erase a := by
    ext b
    simp only [Finset.mem_union, inside_mem, outside_mem, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨different,_⟩ | ⟨different,_⟩) <;> exact different
    · intro different
      obtain ⟨p,on_rows,_⟩ := share a b different.symm
      by_cases inside : p ∈ S
      · exact Or.inl ⟨different,p,inside,on_rows⟩
      · exact Or.inr ⟨different,p,inside,on_rows⟩
  have count := Finset.card_union_of_disjoint separated
  rw [total, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, inner_four] at count
  omega

lemma triple_disjoint (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (neighbors : Fin 8 → Finset (Fin 8))
    (on : Fin 111 → Finset (Fin 8))
    (on_iff : ∀ p a, a ∈ on p ↔ A a p = true)
    (outer : ∀ a b, b ≠ a → (∃ p ∉ S, A a p = true ∧ A b p = true) → b ∈ neighbors a)
    (three_neighbors : ∀ a, (neighbors a).card = 3)
    (shares : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true)
    (p q : Fin 111) (different : p ≠ q)
    (hp : p ∉ S) (hq : q ∉ S) (cp : (on p).card = 3) (cq : (on q).card = 3) :
    Disjoint (on p) (on q) := by
  rw [Finset.disjoint_left]
  intro a ap aq
  have erase_on (r : Fin 111) (hr : r ∉ S) (ar : a ∈ on r) :
      (on r).erase a ⊆ neighbors a := by
    intro b rb
    obtain ⟨ne,br⟩ := Finset.mem_erase.mp rb
    exact outer a b ne ⟨r,hr,(on_iff r a).mp ar,(on_iff r b).mp br⟩
  let left := (on p).erase a
  let right := (on q).erase a
  have cl : left.card = 2 := by
    change ((on p).erase a).card = 2
    rw [Finset.card_erase_of_mem ap,cp]
  have cr : right.card = 2 := by
    change ((on q).erase a).card = 2
    rw [Finset.card_erase_of_mem aq,cq]
  have union_bound : (left ∪ right).card ≤ 3 := by
    rw [← three_neighbors a]
    exact Finset.card_le_card (Finset.union_subset (erase_on p hp ap) (erase_on q hq aq))
  have count := Finset.card_union_add_card_inter left right
  have nonempty : (left ∩ right).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b,hb⟩ := nonempty
  obtain ⟨bl,br⟩ := Finset.mem_inter.mp hb
  obtain ⟨ne,bp⟩ := Finset.mem_erase.mp bl
  obtain ⟨_,bq⟩ := Finset.mem_erase.mp br
  obtain ⟨_,_,unique⟩ := shares a b ne.symm
  exact different ((unique p ⟨(on_iff p a).mp ap,(on_iff p b).mp bp⟩).trans
    (unique q ⟨(on_iff q a).mp aq,(on_iff q b).mp bq⟩).symm)

theorem count_triples (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (neighbors : Fin 8 → Finset (Fin 8))
    (on : Fin 111 → Finset (Fin 8))
    (on_iff : ∀ p a, a ∈ on p ↔ A a p = true)
    (outer : ∀ a b, b ≠ a → (∃ p ∉ S, A a p = true ∧ A b p = true) → b ∈ neighbors a)
    (three_neighbors : ∀ a, (neighbors a).card = 3)
    (shares : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true) :
    ((Finset.univ.filter fun p => p ∉ S ∧ (on p).card = 3).card ≤ 2) ∧
    ∀ p q, p ≠ q → p ∉ S → q ∉ S → (on p).card = 3 → (on q).card = 3 →
      Disjoint (on p) (on q) := by
  let points : Finset (Fin 111) := Finset.univ.filter fun p => p ∉ S ∧ (on p).card = 3
  have disjoint := triple_disjoint A S neighbors on on_iff outer three_neighbors shares
  refine ⟨?_,disjoint⟩
  have pairwise : (points : Set (Fin 111)).PairwiseDisjoint on := by
    intro p hp q hq ne
    obtain ⟨hp,cp⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    obtain ⟨hq,cq⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    exact disjoint p q ne hp hq cp cq
  have each (p : Fin 111) (hp : p ∈ points) : (on p).card = 3 :=
    (Finset.mem_filter.mp hp).2.2
  have bound := Finset.card_le_card (Finset.subset_univ (points.biUnion on))
  rw [Finset.card_biUnion pairwise, Finset.card_univ, Fintype.card_fin] at bound
  rw [Finset.sum_congr rfl each, Finset.sum_const, Nat.nsmul_eq_mul] at bound
  change points.card ≤ 2
  omega

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1.H1 := by
  intro single double
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1.H1
  dsimp only
  rintro ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,hasTriple,maxTriple⟩
  classical
  let A (a : Fin 8) (p : Fin 111) := M (.inl a) p
  let inner (a : Fin 8) : Finset (Fin 8) :=
    Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true
  let outer (a : Fin 8) : Finset (Fin 8) :=
    Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true
  have inner_mem (a b : Fin 8) : b ∈ inner a ↔ b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true := by
    simp [inner]
  have outer_mem (a b : Fin 8) : b ∈ outer a ↔ b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true := by
    simp [outer]
  have share (a b : Fin 8) (ne : a ≠ b) : ∃! p, A a p = true ∧ A b p = true :=
    rowPairs (.inl a) (.inl b) (fun eq => ne (Sum.inl.inj eq))
  have degree := exterior_cubic A S inner inner_mem outer outer_mem share
    (fun p hp => (insideDegrees p hp).1) Asizes
  let on (p : Fin 111) : Finset (Fin 8) := Finset.univ.filter fun a => A a p = true
  have on_iff (p : Fin 111) (a : Fin 8) : a ∈ on p ↔ A a p = true := by simp [on]
  obtain ⟨maxTwo,disjoint⟩ := count_triples A S outer on on_iff
    (fun a b ne meet => (outer_mem a b).mpr ⟨ne,meet⟩) degree share
  let points : Finset (Fin 111) := Finset.univ.filter fun p => p ∉ S ∧ (on p).card = 3
  have existsPoint : 0 < points.card := by
    obtain ⟨p,hp,three⟩ := hasTriple
    exact Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ p,
      hp,Nat.le_antisymm (maxTriple p hp) three⟩⟩
  have upper : points.card ≤ 2 := maxTwo
  by_cases one : points.card = 1
  · exact single ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,
      columnPairs,maxTriple,one⟩
  · have two : points.card = 2 := by omega
    exact double ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,
      columnPairs,maxTriple,two,disjoint⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1
