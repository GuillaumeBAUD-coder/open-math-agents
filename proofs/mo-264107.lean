import OMAStatements.S_mo_264107
import Mathlib

open Finset

open OMA.S_mo_264107

private theorem upper_strict_card {L : Type} [Fintype L] [PartialOrder L] [DecidableRel (α := L) (· ≤ ·)]
    {a b : L} (h : a < b) : (upperElements b).card < (upperElements a).card := by
  apply Finset.card_lt_card
  apply lt_of_le_of_ne
  · intro x hx
    simp only [upperElements,mem_filter,mem_univ,true_and] at hx ⊢
    exact h.le.trans hx
  · intro he
    have ha : a ∈ upperElements a := by simp [upperElements]
    rw [←he] at ha
    have hn : b ≤ a := by simpa [upperElements] using ha
    exact (not_le_of_gt h) hn

private theorem above_coatom_exists {L : Type} [Fintype L] [PartialOrder L] [OrderTop L]
    (a : L) (ha : a ≠ ⊤) : ∃ c, IsCoatom c ∧ a ≤ c := by
  classical
  let candidates := univ.filter fun b : L => a ≤ b ∧ b ≠ ⊤
  have hNonempty : candidates.Nonempty := ⟨a,by simp [candidates,ha]⟩
  obtain ⟨c,hc,hmin⟩ := candidates.exists_min_image (fun b => (upperElements b).card) hNonempty
  have hc' : a ≤ c ∧ c ≠ ⊤ := by simpa [candidates] using hc
  refine ⟨c,⟨hc'.2,?_⟩,hc'.1⟩
  intro b hb
  by_contra hNot
  have hIn : b ∈ candidates := by simp [candidates,hc'.1.trans hb.le,hNot]
  exact (not_lt_of_ge (hmin b hIn)) (upper_strict_card hb)

private theorem weight_sum {L : Type} [DecidableEq L] (T : Finset L) :
    (∑ S ∈ T.powerset, (-1 : ℤ)^S.card) = (0 : ℤ)^T.card := by
  simpa [Finset.prod_const] using
    (Finset.prod_add (fun _ : L => (-1 : ℤ)) (fun _ : L => (1 : ℤ)) T).symm

private theorem sum_coatoms_above {L : Type} [Fintype L] [Lattice L] [OrderTop L]
    [DecidableRel (α := L) (· ≤ ·)] [DecidableEq L] (a : L) :
    ∑ b ∈ upperElements a, coatomSum b = if a = ⊤ then 1 else 0 := by
  classical
  let T : Finset L := (coatoms : Finset L).filter fun b => a ≤ b
  have hFiltered : ((coatoms : Finset L).powerset.filter fun S => a ≤ S.inf id) = T.powerset := by
    ext S
    simp only [mem_filter,mem_powerset,Finset.le_inf_iff, id_eq]
    constructor
    · rintro ⟨hS,hAbove⟩ b hb
      exact mem_filter.mpr ⟨hS hb,hAbove b hb⟩
    · intro hS
      exact ⟨fun b hb => (mem_filter.mp (hS hb)).1,fun b hb => (mem_filter.mp (hS hb)).2⟩
  have hEq : ∑ b ∈ upperElements a, coatomSum b = ∑ S ∈ T.powerset, (-1 : ℤ)^S.card := by
    unfold coatomSum
    rw [Finset.sum_comm, ← hFiltered, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    simp only [@eq_comm _ (S.inf id),Finset.sum_ite_eq']
    simp [upperElements]
  rw [hEq,weight_sum]
  by_cases ht : a = ⊤
  · have he : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      have h : IsCoatom b ∧ a ≤ b := by simpa [T,coatoms] using hb
      exact h.1.1 (top_unique (ht ▸ h.2))
    simp [ht,he]
  · obtain ⟨b,hb,hab⟩ := above_coatom_exists a ht
    have hn : T.Nonempty := ⟨b,by simp [T,coatoms,hb,hab]⟩
    simp [ht,(card_pos.mpr hn).ne']

private theorem upper_split {L : Type} [Fintype L] [PartialOrder L] [DecidableRel (α := L) (· ≤ ·)]
    [DecidableEq L] (a : L) :
    upperElements a = insert a (strictUpper a) := by
  ext b
  simp [upperElements,strictUpper,le_iff_eq_or_lt,eq_comm]

theorem OMA.solution : type_of% @OMA.S_mo_264107.main := by
  classical
  intro L _ _ _ μ hTop hRec a
  refine (measure (fun a : L => (upperElements a).card)).wf.induction (C := fun b => μ b = coatomSum b) a ?_
  intro a ih
  have hNot : a ∉ strictUpper a := by simp [strictUpper]
  have hCandidate := sum_coatoms_above a
  have hSame : ∑ b ∈ upperElements a, μ b = ∑ b ∈ upperElements a, coatomSum b := by
    rw [hCandidate,upper_split,Finset.sum_insert hNot]
    by_cases ht : a = ⊤
    · simp [ht,hTop,strictUpper]
    · rw [if_neg ht,hRec a ht,neg_add_cancel]
  rw [upper_split,Finset.sum_insert hNot,Finset.sum_insert hNot] at hSame
  have hTail : ∑ b ∈ strictUpper a, μ b =
      ∑ b ∈ strictUpper a, coatomSum b := by
    apply Finset.sum_congr rfl
    intro b hb
    exact ih b (upper_strict_card (by simpa [strictUpper] using hb))
  rw [hTail] at hSame
  exact add_right_cancel hSame
