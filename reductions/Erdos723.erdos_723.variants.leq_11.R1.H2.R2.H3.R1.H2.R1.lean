import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1

/-! The eight four-secants give a cubic graph. Two of its vertices are adjacent
when their intersection lies outside the sixteen-point set. Its adjacency matrix
is encoded row by row, the bit at 8*i+j recording the ordered pair (i,j).
The six isomorphism types supply starting patterns for the extension problem,
as in Carter's classification and the MathCheck weight-sixteen analysis. -/

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1

open Finset

private lemma three_outside (S : Finset (Fin 111)) (inc : Fin 8 → Fin 111 → Bool)
    (four : ∀ i, (S.filter fun p => inc i p = true).card = 4)
    (two : ∀ p ∈ S, (univ.filter fun j => inc j p = true).card = 2)
    (unique : ∀ i j, i ≠ j → ∃! p, inc i p = true ∧ inc j p = true)
    (i : Fin 8) :
    (univ.filter fun j => i ≠ j ∧ ¬ ∃ p ∈ S, inc i p = true ∧ inc j p = true).card = 3 := by
  classical
  let P := S.filter (fun p => inc i p = true)
  let O (p : Fin 111) := (univ.erase i).filter (fun j => inc j p = true)
  have op (p : Fin 111) (hp : p ∈ P) : (O p).card = 1 := by
    have q := mem_filter.mp hp
    have eq : O p = (univ.filter (fun j => inc j p = true)).erase i := by ext j; simp [O]
    have mem : i ∈ univ.filter (fun j => inc j p = true) := mem_filter.mpr ⟨mem_univ _,q.2⟩
    rw [eq,card_erase_of_mem mem,two p q.1]
  have dis : (P : Set (Fin 111)).PairwiseDisjoint O := by
    intro p hp q hq pq
    apply Finset.disjoint_left.mpr
    intro j hjp hjq
    have jip := mem_filter.mp hjp
    have ji := (mem_erase.mp jip.1).1
    have un := unique i j ji.symm
    exact pq (un.unique ⟨(mem_filter.mp hp).2,jip.2⟩ ⟨(mem_filter.mp hq).2,(mem_filter.mp hjq).2⟩)
  have cardInside : (P.biUnion O).card = 4 := by
    rw [card_biUnion dis]
    calc
      _ = ∑ _ ∈ P, 1 := sum_congr rfl op
      _ = 4 := by simpa using four i
  have sub : P.biUnion O ⊆ univ.erase i := by
    intro j hj
    obtain ⟨p,hp,hjp⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hjp).1
  have diff : (univ.filter fun j => i ≠ j ∧ ¬ ∃ p ∈ S, inc i p = true ∧ inc j p = true) =
      (univ.erase i) \ P.biUnion O := by
    ext j
    simp only [mem_filter,mem_univ,true_and,mem_sdiff,mem_erase,mem_biUnion, O,P]
    aesop
  rw [diff,card_sdiff_of_subset sub,cardInside]
  simp


-- Classification of cubic simple graphs on eight labeled vertices.
def H1 : Prop := ∀ A : Fin 8 → Fin 8 → Bool,
    (∀ i, A i i = false) → (∀ i j, A i j = A j i) →
    (∀ i, (Finset.univ.filter fun j => A i j = true).card = 3) →
    ∃ (e : Fin 8 ≃ Fin 8) (mask : ℕ), mask ∈ ({8120219788758420750, 8120210872876600590, 8117954426681103630, 4051204205562762510, 8110009338750382350, 6387312113610731790} : Finset ℕ) ∧
      ∀ i j, A (e i) (e j) = mask.testBit (8*i.val + j.val)

-- The six starting patterns cannot extend to the specified incidence geometry.
def H2 : Prop := ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    ∀ (S : Finset (Fin 111)), S.card = 16 →
    (∀ l, let k := (S.filter fun p => incidence l p = true).card
          2 ∣ k ∧ k ≤ 4) →
    ∀ (rows : Fin 8 ↪ Fin 111), (∀ i, (S.filter fun p => incidence (rows i) p = true).card = 4) →
    ∀ mask ∈ ({8120219788758420750, 8120210872876600590, 8117954426681103630, 4051204205562762510, 8110009338750382350, 6387312113610731790} : Finset ℕ),
      ¬ ∀ i j : Fin 8, (mask.testBit (8*i.val + j.val) = true ↔
        i ≠ j ∧ ¬ ∃ p ∈ S, incidence (rows i) p = true ∧ incidence (rows j) p = true)

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1.H2 := by
  intro classify exclude incidence sizeRow sizeCol onePoint oneLine
  dsimp only
  rintro ⟨S,profile,zero⟩
  classical
  let k (l : Fin 111) := (S.filter fun p => incidence l p = true).card
  let Q := univ.filter fun l => k l = 4
  have noSix (l : Fin 111) : k l ≠ 6 := by
    intro h
    have z : (univ.filter fun l => k l = 6).card = 0 := zero
    have mem : l ∈ univ.filter (fun l => k l = 6) := mem_filter.mpr ⟨mem_univ _,h⟩
    rw [card_eq_zero.mp z] at mem
    exact notMem_empty _ mem
  have cap (l : Fin 111) : 2 ∣ k l ∧ k l ≤ 4 := by
    obtain ⟨ev,le⟩ := profile.2.1 l
    change 2 ∣ k l at ev
    change k l ≤ 6 at le
    exact ⟨ev, by have := noSix l; omega⟩
  have qcard : Q.card = 8 := by
    have bal := profile.2.2.1.1
    rw [zero] at bal
    simpa [Q,k] using bal
  let e : Fin 8 ≃ Q := (Fintype.equivFinOfCardEq (by simpa using qcard)).symm
  let rows : Fin 8 ↪ Fin 111 := e.toEmbedding.trans (Function.Embedding.subtype _)
  have four (i : Fin 8) : k (rows i) = 4 := (mem_filter.mp (e i).property).2
  have two (p : Fin 111) (hp : p ∈ S) : (univ.filter fun i => incidence (rows i) p = true).card = 2 := by
    have z : (univ.filter fun l => k l = 6 ∧ incidence l p = true) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact noSix l (mem_filter.mp hl).2.1
    have tot := profile.2.2.2 p hp
    change (univ.filter fun l => k l = 4 ∧ incidence l p = true).card +
      2*(univ.filter fun l => k l = 6 ∧ incidence l p = true).card = 2 at tot
    simp only [z, card_empty,mul_zero,add_zero] at tot
    rw [←tot]
    apply card_bij (fun i _ => rows i)
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _,four i,(mem_filter.mp hi).2⟩
    · intro i hi j hj eq; exact rows.injective eq
    · intro l hl
      have a := (mem_filter.mp hl).2
      let u : Q := ⟨l,mem_filter.mpr ⟨mem_univ _,a.1⟩⟩
      have val : rows (e.symm u) = l := congrArg Subtype.val (e.apply_symm_apply u)
      exact ⟨e.symm u,mem_filter.mpr ⟨mem_univ _,val ▸ a.2⟩, val⟩
  let A (i j : Fin 8) : Bool := decide (i ≠ j ∧ ¬ ∃ p ∈ S, incidence (rows i) p = true ∧ incidence (rows j) p = true)
  have diag (i : Fin 8) : A i i = false := by simp [A]
  have symm (i j : Fin 8) : A i j = A j i := by
    simp only [A,decide_eq_decide]
    constructor <;> rintro ⟨hn,h⟩ <;> refine ⟨hn.symm,?_⟩ <;> rintro ⟨p,hp,hx,hy⟩ <;> exact h ⟨p,hp,hy,hx⟩
  have degree (i : Fin 8) : (univ.filter fun j => A i j = true).card = 3 := by
    simpa [A] using three_outside S (fun i p => incidence (rows i) p) four two
      (fun i j h => onePoint _ _ (fun eq => h (rows.injective eq))) i
  obtain ⟨f,mask,hm,adj⟩ := classify A diag symm degree
  apply exclude incidence sizeRow sizeCol onePoint oneLine S profile.1 cap
    (f.toEmbedding.trans rows) (fun i => four (f i)) mask hm
  intro i j
  rw [←adj i j]
  simpa [A,Function.Embedding.trans_apply] using
    (show A (f i) (f j) = true ↔ f i ≠ f j ∧ ¬ ∃ p ∈ S,
      incidence (rows (f i)) p = true ∧ incidence (rows (f j)) p = true from decide_eq_true_iff)
end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1
