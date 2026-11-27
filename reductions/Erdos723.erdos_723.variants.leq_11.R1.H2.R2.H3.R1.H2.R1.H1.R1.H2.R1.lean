import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

/-! Put the eight four-secants into canonical columns, after their graph relabeling. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1

open scoped Classical

def H1 : Prop :=
  ∀ A : Fin 8 → Fin 111 → Bool,
    (∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true) →
    (∀ p, (Finset.univ.filter fun a => A a p = true).card ≤ 2) →
    (∀ a, (Finset.univ.filter fun p => A a p = true).card = 11) →
    ∃ e : (({q : Fin 8 × Fin 8 // q.1 < q.2} ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51) ≃ Fin 111,
      (∀ r q, A r (e (.inl (.inl q))) = decide (r = q.val.1 ∨ r = q.val.2)) ∧
      (∀ r s i, A r (e (.inl (.inr (s,i)))) = decide (r = s)) ∧
      (∀ r t, A r (e (.inr t)) = false)

def H2 : Prop :=
  let R := Fin 8 ⊕ Fin 72
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let A (M : R → P → Bool) (p : P) := (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) := (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card
  ¬ ∃ (M : R → P → Bool) (S : Finset P),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    (∀ a (q : Q), M (.inl a) (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) ∧
    (∀ a b i, M (.inl a) (.inl (.inr (b,i))) = decide (a = b)) ∧
    (∀ a i, M (.inl a) (.inr i) = false) ∧
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl a) p = true ∧ M (.inl b) p = true)
    let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
    let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
    word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187] : List Nat)

lemma card_filter_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl

set_option maxRecDepth 4096 in
theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1.H2 := by
  intro normalize impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1.H2
  dsimp only
  rintro ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,sparse,e,representative⟩
  classical
  let A (a : Fin 8) (p : Fin 111) := M (.inl (e a)) p
  have shares (a b : Fin 8) (ne : a ≠ b) : ∃! p, A a p = true ∧ A b p = true :=
    rowPairs (.inl (e a)) (.inl (e b)) (fun same => ne (e.injective (Sum.inl.inj same)))
  have counts (p : Fin 111) :
      (Finset.univ.filter fun a => A a p = true).card =
      (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card :=
    card_filter_relabel e (fun a => M (.inl a) p = true)
  have bounds (p : Fin 111) : (Finset.univ.filter fun a => A a p = true).card ≤ 2 := by
    rw [counts]
    by_cases hp : p ∈ S
    · exact Nat.le_of_eq (inside p hp).1
    · exact sparse p hp
  obtain ⟨d,shared,private_,hidden⟩ := normalize A shares bounds (fun a => rows (.inl (e a)))
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let r := Equiv.sumCongr e (Equiv.refl (Fin 72))
  let N (l : Fin 8 ⊕ Fin 72) (p : P) := M (r l) (d p)
  let U := S.map d.symm.toEmbedding
  have loc (p : P) : p ∈ U ↔ d p ∈ S := by
    simpa only [U, Equiv.symm_symm] using (Finset.mem_map_equiv (f := d.symm) (s := S) (b := p))
  have row_count (l : Fin 8 ⊕ Fin 72) : (Finset.univ.filter fun p => N l p = true).card = 11 :=
    (card_filter_relabel d (fun p => M (r l) p = true)).trans (rows (r l))
  have in_count (l : Fin 8 ⊕ Fin 72) :
      (U.filter fun p => N l p = true).card = (S.filter fun p => M (r l) p = true).card := by
    change ((S.map d.symm.toEmbedding).filter fun p => M (r l) (d p) = true).card = _
    rw [Finset.filter_map, Finset.card_map]
    simp only [Function.comp_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
  have degree (p : P) : (Finset.univ.filter fun a : Fin 8 => N (.inl a) p = true).card =
      (Finset.univ.filter fun a : Fin 8 => M (.inl a) (d p) = true).card := counts (d p)
  have pair (l m : Fin 8 ⊕ Fin 72) (ne : l ≠ m) : ∃! p, N l p = true ∧ N m p = true := by
    obtain ⟨p,hp,unique⟩ := rowPairs (r l) (r m) (fun same => ne (r.injective same))
    have hit : d (d.symm p) = p := d.apply_symm_apply p
    refine ⟨d.symm p,?_,fun q hq => d.injective ((unique (d q) hq).trans hit.symm)⟩
    simpa only [N,hit] using hp
  have column (p q : P) (ne : p ≠ q) (l m : Fin 8 ⊕ Fin 72)
      (lp : N l p = true) (lq : N l q = true) (mp : N m p = true) (mq : N m q = true) : l = m :=
    r.injective (colPairs (d p) (d q) (fun same => ne (d.injective same)) (r l) (r m) lp lq mp mq)
  let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ U, N (.inl a) p = true ∧ N (.inl b) p = true)
  let H (a b : Fin 8) := decide (e b ≠ e a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)
  have compatible (a b : Fin 8) : G a b = H a b := by
    apply Bool.eq_iff_iff.mpr
    simp only [G,H,decide_eq_true_eq]
    constructor
    · rintro ⟨ne,p,hp,ha,hb⟩
      exact ⟨fun same => ne (e.injective same),d p,fun inside => hp ((loc p).mpr inside),ha,hb⟩
    · rintro ⟨ne,p,hp,ha,hb⟩
      refine ⟨fun same => ne (congrArg e same),d.symm p,?_,?_,?_⟩
      · intro inside
        exact hp (by simpa only [Equiv.apply_symm_apply] using (loc _).mp inside)
      · change M (.inl (e a)) (d (d.symm p)) = true
        rwa [Equiv.apply_symm_apply]
      · change M (.inl (e b)) (d (d.symm p)) = true
        rwa [Equiv.apply_symm_apply]
  apply impossible
  refine ⟨N,U,(Finset.card_map _).trans cardS,row_count,?_,?_,?_,?_,pair,column,
    shared,private_,hidden,?_⟩
  · intro a
    exact (in_count (.inl a)).trans (As (e a))
  · intro b
    exact (in_count (.inr b)).trans (Bs b)
  · intro p hp
    change (Finset.univ.filter fun a : Fin 8 => N (.inl a) p = true).card = 2 ∧ _
    rw [degree]
    exact inside (d p) ((loc p).mp hp)
  · intro p hp
    change 2 * (Finset.univ.filter fun a : Fin 8 => N (.inl a) p = true).card + _ = 8
    rw [degree]
    exact outside (d p) (fun inside => hp ((loc p).mpr inside))
  · let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
    change ((pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0) ∈ _
    change ((pairs.zipIdx.map fun ((a,b),i) => if H a b then 2^i else 0).foldr Nat.lor 0) ∈ _ at representative
    simpa only [compatible] using representative


end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1
