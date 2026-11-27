import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-! Index the 16 code points, two concurrency points and eight private blocks explicitly. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1

open Finset
open scoped Classical

def H1 : Prop :=
  let L := Fin 4 ⊕ Fin 4
  let P := ((Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))) ⊕ Fin 45
  let on (A : Fin 8 → Fin 111 → Bool) (p : Fin 111) :=
    Finset.univ.filter fun a => A a p = true
  ∀ (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 →
    (∀ a, (Finset.univ.filter fun x => A a x = true).card = 11) →
    (∀ a, (S.filter fun x => A a x = true).card = 4) →
    (∀ p ∈ S, (on A p).card = 2) →
    (∀ a b, a ≠ b → ∃! q, A a q = true ∧ A b q = true) →
    ∀ p q : Fin 111, p ∉ S → q ∉ S → p ≠ q →
    (on A p).card = 4 → (on A q).card = 4 →
    (∀ a b, a ≠ b → ((∃ x ∉ S, A a x = true ∧ A b x = true) ↔ (a ∈ on A p ↔ b ∈ on A p))) →
    ∃ (r : L ≃ Fin 8) (c : P ≃ Fin 111),
      (∀ x, c x ∈ S ↔ ∃ a b : Fin 4, x = .inl (.inl (a,b))) ∧
      (∀ a b j, A (r (.inl a)) (c (.inl (.inl (b,j)))) = decide (a = b)) ∧
      (∀ a b j, A (r (.inr a)) (c (.inl (.inl (j,b)))) = decide (a = b)) ∧
      (∀ a : Fin 4, ∀ i : Fin 2,
        A (r (.inl a)) (c (.inl (.inr (.inl i)))) = decide (i = 0) ∧
        A (r (.inr a)) (c (.inl (.inr (.inl i)))) = decide (i = 1)) ∧
      (∀ a b i, A (r a) (c (.inl (.inr (.inr (b,i))))) = decide (a = b)) ∧
      ∀ a i, A (r a) (c (.inr i)) = false

def H2 : Prop :=
  let L := Fin 4 ⊕ Fin 4
  let P := ((Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))) ⊕ Fin 45
  let U : Finset P := Finset.univ.filter fun x => ∃ a b : Fin 4, x = .inl (.inl (a,b))
  let A (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun a : L => M (.inl a) p = true).card
  let B (M : L ⊕ Fin 72 → P → Bool) (p : P) := (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card
  ¬ ∃ M : L ⊕ Fin 72 → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ b : Fin 72, (U.filter fun p => M (.inr b) p = true).card = 2) ∧
    (∀ p ∈ U, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ U, 2*A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
      (∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b)) ∧
      (∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b)) ∧
      (∀ a : Fin 4, ∀ i : Fin 2,
        M (.inl (.inl a)) (.inl (.inr (.inl i))) = decide (i = 0) ∧
        M (.inl (.inr a)) (.inl (.inr (.inl i))) = decide (i = 1)) ∧
      (∀ a b i, M (.inl a) (.inl (.inr (.inr (b,i)))) = decide (a = b)) ∧
      ∀ a i, M (.inl a) (.inr i) = false

lemma card_filter_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl

set_option maxRecDepth 4096 in
theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro model impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1.H3
  dsimp only
  rintro ⟨M,S,cardS,rows,asizes,bsizes,inside,outside,rowPairs,colPairs,
    p,hp,fourP,components,q,hq,qp,fourQ⟩
  classical
  let A (a : Fin 8) (x : Fin 111) := M (.inl a) x
  have shares (a b : Fin 8) (different : a ≠ b) : ∃! x, A a x = true ∧ A b x = true :=
    rowPairs (.inl a) (.inl b) (fun same => different (Sum.inl.inj same))
  obtain ⟨r,c,code,innerL,innerR,centers,private_,hidden⟩ := model A S cardS
    (fun a => rows (.inl a)) asizes (fun q given => (inside q given).1) shares
    p q hp hq (Ne.symm qp) fourP fourQ components
  let L := Fin 4 ⊕ Fin 4
  let P := ((Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (L × Fin 6))) ⊕ Fin 45
  let E := Equiv.sumCongr r (Equiv.refl (Fin 72))
  let N (l : L ⊕ Fin 72) (x : P) := M (E l) (c x)
  let U : Finset P := Finset.univ.filter fun x => ∃ a b : Fin 4, x = .inl (.inl (a,b))
  have loc (x : P) : x ∈ U ↔ c x ∈ S := by simpa [U] using (code x).symm
  have mapS : U = S.map c.symm.toEmbedding := by
    ext x
    rw [loc,Finset.mem_map_equiv,Equiv.symm_symm]
  have row_sizes (l : L ⊕ Fin 72) : (Finset.univ.filter fun p => N l p = true).card = 11 :=
    (card_filter_relabel c (fun p => M (E l) p = true)).trans (rows (E l))
  have secants (b : Fin 72) : (U.filter fun p => N (.inr b) p = true).card = 2 := by
    rw [mapS,Finset.filter_map,Finset.card_map]
    change (S.filter fun p => M (.inr b) (c (c.symm p)) = true).card = 2
    simpa only [Equiv.apply_symm_apply] using bsizes b
  have upperDegree (x : P) :
      (Finset.univ.filter fun a : L => N (.inl a) x = true).card =
      (Finset.univ.filter fun a : Fin 8 => M (.inl a) (c x) = true).card :=
    card_filter_relabel r (fun a => M (.inl a) (c x) = true)
  have meet (l m : L ⊕ Fin 72) (diff : l ≠ m) : ∃! x, N l x = true ∧ N m x = true := by
    obtain ⟨x,seen,unique⟩ := rowPairs (E l) (E m) (fun eq => diff (E.injective eq))
    have cEq : c (c.symm x) = x := c.apply_symm_apply x
    refine ⟨c.symm x,?_,fun y hy => c.injective ((unique (c y) hy).trans cEq.symm)⟩
    simpa only [N,cEq] using seen
  have column (x y : P) (diff : x ≠ y) (l m : L ⊕ Fin 72)
      (lx : N l x = true) (ly : N l y = true) (mx : N m x = true) (my : N m y = true) : l = m :=
    E.injective (colPairs (c x) (c y) (fun eq => diff (c.injective eq)) (E l) (E m) lx ly mx my)
  apply impossible
  refine ⟨N,row_sizes,secants,?_,?_,meet,column,innerL,innerR,centers,private_,hidden⟩
  · intro x hx
    change (Finset.univ.filter fun a : L => N (.inl a) x = true).card = 2 ∧ _
    rw [upperDegree]
    exact inside (c x) ((loc x).mp hx)
  · intro x hx
    change 2 * (Finset.univ.filter fun a : L => N (.inl a) x = true).card + _ = 8
    rw [upperDegree]
    exact outside (c x) (fun inside => hx ((loc x).mpr inside))


end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1
