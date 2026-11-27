import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic

/-! Index the six five-secants and their nineteen code-point supports. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H2_R1

open Finset

def H1 : Prop :=
  ∀ (C : Fin 19 → Finset (Fin 6)),
    (∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) →
    (∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5) →
    (∀ p, (C p).card ≤ 4) →
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let P := F.filter fun T => T.card = 2
    ∀ U ∈ F, U.card = 4 →
    let E := (Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2
    (∀ T ∈ F, T.card ≠ 3) → (E \ P).card ≤ 1 →
    (P.card ≠ 8 ∨ (Finset.univ \ U) ∉ P) →
    let D (i : Fin 2) (p : Fin 19) := ((([[[0, 1, 2, 3], [0, 4], [0, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], []], [[0, 1, 2, 3], [0, 4], [0, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [0], [0], [1], [1], [2], [2], [3], [3], [4], [5]]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset
    ∃ (i : Fin 2) (e : Equiv.Perm (Fin 6)) (π : Equiv.Perm (Fin 19)),
      ∀ p, (C (π p)).map e.toEmbedding = D i p

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ i : Fin 2, ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    let D (i : Fin 2) (p : Fin 19) := ((([[[0, 1, 2, 3], [0, 4], [0, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5], [0], [0], [1], [1], [2], [2], [3], [3], []], [[0, 1, 2, 3], [0, 4], [0, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [0], [0], [1], [1], [2], [2], [3], [3], [4], [5]]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset
    ∀ p : Fin 19, (Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true) = D i p


lemma card_filter_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl


lemma unique_relabel {X Y : Type} (e : X ≃ Y) (P : Y → Prop)
    (h : ∃! y, P y) : ∃! x, P (e x) := by
  obtain ⟨y,yes,only⟩ := h
  refine ⟨e.symm y,?_ ,?_⟩
  · simpa only [Equiv.apply_symm_apply] using yes
  · intro x hx
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using only (e x) hx

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1.H2 := by
  intro normalize impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1.H2
  dsimp only
  rintro ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,U,hU,four,none,missing,complement⟩
  classical
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
  have rows (a : Fin 6) : (Finset.univ.filter fun p => a ∈ C p).card = 5 := by
    simpa only [C,Finset.mem_filter,Finset.mem_univ,true_and] using aSizes a
  have bound (p : Fin 19) : (C p).card ≤ 4 := by
    have count := inside p
    change _ + 2 * (C p).card = 9 at count
    omega
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have both (x : Fin 6) (hx : x ∈ C p ∩ C q) :
        M (.inl x) (.inl p) = true ∧ M (.inl x) (.inl q) = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hx
      exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hq).2⟩
    obtain ⟨_,_,unique⟩ := colPairs (.inl p) (.inl q) (fun eq => different (Sum.inl.inj eq))
    exact Sum.inl.inj ((unique (.inl a) (both a ha)).trans (unique (.inl b) (both b hb)).symm)
  obtain ⟨i,e,π,matched⟩ := normalize C overlap rows bound U hU four none missing complement
  let r := Equiv.sumCongr e.symm (Equiv.refl (Fin 37 ⊕ Fin 68))
  let c := Equiv.sumCongr π (Equiv.refl (Fin 92))
  let N (l : Fin 6 ⊕ (Fin 37 ⊕ Fin 68)) (p : Fin 19 ⊕ Fin 92) := M (r l) (c p)
  apply impossible
  refine ⟨i,N,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro l
    exact (card_filter_relabel c (fun p => M (r l) p = true)).trans (rowSizes (r l))
  · intro p
    exact (card_filter_relabel r (fun l => M l (c p) = true)).trans (colSizes (c p))
  · intro l m ne
    exact unique_relabel c _ (rowPairs (r l) (r m) (fun eq => ne (r.injective eq)))
  · intro p q ne
    exact unique_relabel r _ (colPairs (c p) (c q) (fun eq => ne (c.injective eq)))
  · intro a
    exact (card_filter_relabel π (fun p => M (.inl (e.symm a)) (.inl p) = true)).trans (aSizes (e.symm a))
  · intro b
    exact (card_filter_relabel π (fun p => M (.inr (.inl b)) (.inl p) = true)).trans (bSizes b)
  · intro d
    exact (card_filter_relabel π (fun p => M (.inr (.inr d)) (.inl p) = true)).trans (cSizes d)
  · intro p
    change _ + 2 * (Finset.univ.filter fun a : Fin 6 => M (.inl (e.symm a)) (.inl (π p)) = true).card = 9
    rw [card_filter_relabel e.symm (fun a => M (.inl a) (.inl (π p)) = true)]
    exact inside (π p)
  · intro p
    change _ + 2 * (Finset.univ.filter fun a : Fin 6 => M (.inl (e.symm a)) (.inr p) = true).card = 4
    rw [card_filter_relabel e.symm (fun a => M (.inl a) (.inr p) = true)]
    exact outside p
  · dsimp only
    intro p
    refine Eq.trans ?_ (matched p)
    ext a
    rw [Finset.mem_map_equiv]
    simp only [C,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H2_R1
