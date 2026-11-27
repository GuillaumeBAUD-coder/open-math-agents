import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1
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

-- Credit: @avivorly
namespace WeightNineteenTriangleCertificate

open Finset

abbrev Points := Fin 19
abbrev Graph := Points → Points → Bool
abbrev Triangles := Finset (Finset Points)

def IsCover (G : Graph) (F : Triangles) : Prop :=
  (∀ X ∈ F, X.card = 3 ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → G x y = true) ∧
  (∀ x y, G x y = true → ∃! T, T ∈ F ∧ x ∈ T ∧ y ∈ T)

def GraphLoopless (G : Graph) : Prop := ∀ x, G x x = false

def triangle (a b c : Points) : Finset Points := {a,b,c}

def deleteTriangle (G : Graph) (T : Finset Points) : Graph :=
  fun a b => G a b && !(decide (a ∈ T ∧ b ∈ T))

def goodThird (G : Graph) (a b c : Points) : Bool := G a c && G b c

def refute (G : Graph) : List (Points × Points × Option Points) → Bool
  | [] => false
  | (a,b,none) :: _ =>
      G a b && (List.finRange 19).all (fun c => !(goodThird G a b c))
  | (a,b,some c) :: tail =>
      G a b && goodThird G a b c &&
        (List.finRange 19).all (fun d => !(goodThird G a b d) || decide (d = c)) &&
        refute (deleteTriangle G (triangle a b c)) tail

lemma find_third (G : Graph) (F : Triangles) (valid : IsCover G F)
    (loopless : GraphLoopless G) (a b : Points) (edge : G a b = true) :
    ∃ T ∈ F, ∃ c, T = triangle a b c ∧ goodThird G a b c = true := by
  obtain ⟨T,⟨inF,inA,inB⟩,_⟩ := valid.2 a b edge
  obtain ⟨card,adj⟩ := valid.1 T inF
  have separate : a ≠ b := by
    intro same
    rw [same,loopless] at edge
    contradiction
  have third : (T \ {a,b}).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro sub
    have le := Finset.card_le_card sub
    rw [Finset.card_pair_eq_two_iff.mpr separate,card] at le
    omega
  obtain ⟨c,hc⟩ := third
  obtain ⟨inC,novel⟩ := Finset.mem_sdiff.mp hc
  have ca : c ≠ a := fun eq => novel (eq ▸ Finset.mem_insert_self _ _)
  have cb : c ≠ b := fun eq => novel (eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have subset : triangle a b c ⊆ T := by
    intro p hp
    simp only [triangle,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with eq | eq | eq
    · exact eq.symm ▸ inA
    · exact eq.symm ▸ inB
    · exact eq.symm ▸ inC
  have size : (triangle a b c).card = 3 := by
    unfold triangle
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_pair_eq_two_iff.mpr cb.symm]
    · simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
        (show a ≠ b ∧ a ≠ c from ⟨separate,ca.symm⟩)
  refine ⟨T,inF,c,(Finset.eq_of_subset_of_card_le subset (by rw [size,card])).symm,?_⟩
  simp [goodThird, adj a inA c inC ca.symm, adj b inB c inC cb.symm]

lemma delete_cover_triangle (G : Graph) (F : Triangles) (valid : IsCover G F)
    (T : Finset Points) (inF : T ∈ F) : IsCover (deleteTriangle G T) (F.erase T) := by
  constructor
  · intro U hu
    obtain ⟨different,old⟩ := Finset.mem_erase.mp hu
    obtain ⟨card,adj⟩ := valid.1 U old
    refine ⟨card,fun x hx y hy ne => ?_⟩
    have edge := adj x hx y hy ne
    change (G x y && !(decide (x ∈ T ∧ y ∈ T))) = true
    simp only [edge,Bool.true_and,Bool.not_eq_true',decide_eq_false_iff_not]
    rintro ⟨tx,ty⟩
    obtain ⟨W,_,unique⟩ := valid.2 x y edge
    have same := (unique U ⟨old,hx,hy⟩).trans (unique T ⟨inF,tx,ty⟩).symm
    exact different same
  · intro x y kept
    have contents : G x y = true ∧ ¬ (x ∈ T ∧ y ∈ T) := by
      simpa only [deleteTriangle,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not] using kept
    obtain ⟨W,⟨inF,hx,hy⟩,unique⟩ := valid.2 x y contents.1
    have different : W ≠ T := fun eq => contents.2 ⟨eq ▸ hx,eq ▸ hy⟩
    exact ⟨W,⟨Finset.mem_erase.mpr ⟨different,inF⟩,hx,hy⟩,
      fun U h => unique U ⟨(Finset.mem_erase.mp h.1).2,h.2⟩⟩

theorem refutation_sound (G : Graph) (F : Triangles) (cert : List (Points × Points × Option Points))
    (valid : IsCover G F) (loopless : GraphLoopless G) : refute G cert = false := by
  induction cert generalizing G F with
  | nil => rfl
  | cons step tail recur =>
    obtain ⟨a,b,c⟩ := step
    cases c with
    | none =>
      cases result : refute G ((a,b,none) :: tail) with
      | false => rfl
      | true =>
        simp only [refute,Bool.and_eq_true] at result
        obtain ⟨T,_,c,_,witness⟩ := find_third G F valid loopless a b result.1
        have spec := List.all_eq_true.mp result.2 c (List.mem_finRange c)
        rw [witness] at spec
        contradiction
    | some c =>
      cases result : refute G ((a,b,some c) :: tail) with
      | false => rfl
      | true =>
        simp only [refute,Bool.and_eq_true] at result
        obtain ⟨⟨⟨edge,_⟩,force⟩,remaining⟩ := result
        obtain ⟨T,inF,d,shape,third⟩ := find_third G F valid loopless a b edge
        have same : d = c := by
          have fit := List.all_eq_true.mp force d (List.mem_finRange d)
          simpa only [third,Bool.not_true,Bool.false_or,decide_eq_true_eq] using fit
        subst d
        rw [← shape] at remaining
        have smaller := delete_cover_triangle G F valid T inF
        have loops (x : Points) : deleteTriangle G T x x = false := by
          simp only [deleteTriangle,loopless x,Bool.false_and]
        rw [recur (deleteTriangle G T) (F.erase T) smaller loops] at remaining
        contradiction

def available (C : Fin 19 → Finset (Fin 6)) (p q : Points) : Bool :=
  decide (p ≠ q ∧ Disjoint (C p) (C q))

lemma available_iff (C : Fin 19 → Finset (Fin 6)) (p q : Points) :
    available C p q = true ↔ p ≠ q ∧ Disjoint (C p) (C q) := by
  simp [available]

lemma available_loopless (C : Fin 19 → Finset (Fin 6)) : GraphLoopless (available C) := by
  intro p
  simp [available]

theorem incidence_gives_cover
    (M : Fin 6 ⊕ (Fin 37 ⊕ Fin 68) → Fin 19 ⊕ Fin 92 → Bool)
    (colPairs : ∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true)
    (bSizes : ∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3)
    (cSizes : ∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1)
    (C : Fin 19 → Finset (Fin 6))
    (loc : ∀ p a, a ∈ C p ↔ M (.inl a) (.inl p) = true) :
    ∃ F : Triangles, IsCover (available C) F := by
  let T (b : Fin 37) : Finset (Fin 19) :=
    Finset.univ.filter fun p => M (.inr (.inl b)) (.inl p) = true
  let F := Finset.univ.image T
  have T_mem (b : Fin 37) (p : Fin 19) : p ∈ T b ↔ M (.inr (.inl b)) (.inl p) = true := by
    simp [T]
  refine ⟨F,?_,?_⟩
  · intro U hU
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hU
    refine ⟨bSizes b,fun p hp q hq ne => (available_iff C p q).mpr ⟨ne,?_⟩⟩
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨_,_,unique⟩ := colPairs (.inl p) (.inl q) (fun eq => ne (Sum.inl.inj eq))
    have on_a := unique (.inl a) ⟨(loc p a).mp ha,(loc q a).mp ha'⟩
    have on_b := unique (.inr (.inl b)) ⟨(T_mem b p).mp hp,(T_mem b q).mp hq⟩
    have impossible := on_a.trans on_b.symm
    cases impossible
  · intro p q edge
    obtain ⟨ne,apart⟩ := (available_iff C p q).mp edge
    obtain ⟨l,hl,unique⟩ := colPairs (.inl p) (.inl q) (fun eq => ne (Sum.inl.inj eq))
    cases l with
    | inl a =>
      exact False.elim (Finset.disjoint_left.mp apart ((loc p a).mpr hl.1) ((loc q a).mpr hl.2))
    | inr l =>
      cases l with
      | inr c =>
        let onLine := Finset.univ.filter fun x : Fin 19 => M (.inr (.inr c)) (.inl x) = true
        have one : onLine.card ≤ 1 := (cSizes c).le
        exact False.elim (ne (Finset.card_le_one.mp one p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.1⟩)
          q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.2⟩)))
      | inl b =>
        refine ⟨T b,⟨Finset.mem_image_of_mem T (Finset.mem_univ _),(T_mem b p).mpr hl.1,(T_mem b q).mpr hl.2⟩,?_⟩
        rintro U ⟨hU,hp,hq⟩
        obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hU
        have eq := unique (.inr (.inl b')) ⟨(T_mem b' p).mp hp,(T_mem b' q).mp hq⟩
        exact congrArg T (Sum.inl.inj (Sum.inr.inj eq))

theorem relabel_cover (G H : Graph) (F : Triangles) (e : Equiv.Perm Points)
    (to_graph : ∀ a b, H (e a) (e b) = G a b) (valid : IsCover G F) :
    IsCover H (F.image (Finset.map e.toEmbedding)) := by
  have maps (S : Finset Points) (p : Points) :
      p ∈ S.map e.toEmbedding ↔ e.symm p ∈ S := Finset.mem_map_equiv
  constructor
  · intro S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    have ⟨size,adj⟩ := valid.1 T hT
    refine ⟨(Finset.card_map _).trans size,fun a ha b hb ne => ?_⟩
    have ne' : e.symm a ≠ e.symm b := fun same => ne (e.symm.injective same)
    have edge := adj (e.symm a) ((maps T a).mp ha) (e.symm b) ((maps T b).mp hb) ne'
    simpa only [Equiv.apply_symm_apply] using (to_graph (e.symm a) (e.symm b)).trans edge
  · intro a b edge
    have in_graph : G (e.symm a) (e.symm b) = true := by
      rw [← to_graph,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
      exact edge
    obtain ⟨T,⟨hT,ha,hb⟩,unique⟩ := valid.2 _ _ in_graph
    refine ⟨T.map e.toEmbedding,⟨Finset.mem_image_of_mem _ hT,(maps T a).mpr ha,(maps T b).mpr hb⟩,?_⟩
    rintro S ⟨hS,at_a,at_b⟩
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hS
    exact congrArg (Finset.map e.toEmbedding) (unique U ⟨hU,(maps U a).mp at_a,(maps U b).mp at_b⟩)

end WeightNineteenTriangleCertificate

namespace WeightNineteenSupportRelabel

open Finset
open scoped BigOperators

abbrev Columns := Fin 19 → Finset (Fin 6)

def shared (C : Columns) : Finset (Fin 19) :=
  Finset.univ.filter fun p => 2 ≤ (C p).card

def layout (C : Columns) : Finset (Finset (Fin 6)) :=
  (shared C).image C

def fiber (C : Columns) (s : Finset (Fin 6)) : Finset (Fin 19) :=
  Finset.univ.filter fun p => C p = s

lemma mem_fiber (C : Columns) (s : Finset (Fin 6)) (p : Fin 19) :
    p ∈ fiber C s ↔ C p = s := by simp [fiber]

lemma injective_shared (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    (shared C : Set (Fin 19)).InjOn C := by
  intro p hp q hq same
  by_contra different
  have small := overlap p q different
  rw [same,Finset.inter_self] at small
  have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  omega

lemma high_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (s : Finset (Fin 6)) (many : 2 ≤ s.card) :
    (fiber C s).card = if s ∈ layout C then 1 else 0 := by
  by_cases yes : s ∈ layout C
  · rw [if_pos yes]
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp yes
    apply Finset.card_eq_one.mpr
    refine ⟨p,?_⟩
    ext q
    rw [mem_fiber,Finset.mem_singleton]
    constructor
    · intro hs
      have hq : q ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
      exact injective_shared C overlap hq hp (hs.trans eq.symm)
    · rintro rfl
      exact eq
  · rw [if_neg yes]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hs := (mem_fiber C s p).mp hp
    have here : p ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
    exact yes (hs ▸ Finset.mem_image_of_mem C here)

lemma single_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (a : Fin 6) :
    (fiber C {a}).card + ((layout C).filter fun s => a ∈ s).card =
      (Finset.univ.filter fun p => a ∈ C p).card := by
  let high := (shared C).filter fun p => a ∈ C p
  have image_high : high.image C = (layout C).filter fun s => a ∈ s := by
    ext s
    constructor
    · rintro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨sharedp,one⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ sharedp,one⟩
    · rintro hs
      obtain ⟨in_layout,one⟩ := Finset.mem_filter.mp hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp in_layout
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,one⟩,rfl⟩
  have inj : (high : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    exact injective_shared C overlap (Finset.filter_subset _ _ hp) (Finset.filter_subset _ _ hq) same
  have high_count := Finset.card_image_of_injOn inj
  rw [image_high] at high_count
  have apart : Disjoint (fiber C {a}) high := by
    rw [Finset.disjoint_left]
    intro p hf hp
    have hs := (mem_fiber C {a} p).mp hf
    have many := (Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).2
    rw [hs,Finset.card_singleton] at many
    omega
  have cover : fiber C {a} ∪ high = Finset.univ.filter fun p => a ∈ C p := by
    ext p
    rw [Finset.mem_union, mem_fiber]
    have hit : p ∈ (Finset.univ.filter fun p => a ∈ C p) ↔ a ∈ C p := by simp
    rw [hit]
    constructor
    · rintro (one | above)
      · rw [one]
        simp
      · exact (Finset.mem_filter.mp above).2
    · intro on_a
      by_cases many : 2 ≤ (C p).card
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p,many⟩,on_a⟩)
      · apply Or.inl
        symm
        apply Finset.eq_of_subset_of_card_le ((Finset.singleton_subset_iff).mpr on_a)
        rw [Finset.card_singleton]
        omega
  rw [high_count,← Finset.card_union_of_disjoint apart,cover]

lemma sum_fibers (C : Columns) : (∑ s : Finset (Fin 6), (fiber C s).card) = 19 := by
  calc
    _ = ∑ s : Finset (Fin 6), ∑ p : Fin 19, if C p = s then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [fiber]
    _ = ∑ p : Fin 19, ∑ s : Finset (Fin 6), if C p = s then (1 : Nat) else 0 := Finset.sum_comm
    _ = 19 := by simp [eq_comm]

theorem relabel_columns (C D : Columns)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (same : layout C = layout D) :
    ∃ e : Equiv.Perm (Fin 19), ∀ p, D (e p) = C p := by
  classical
  have counts_ne (s : Finset (Fin 6)) (nonzero : s ≠ ∅) : (fiber C s).card = (fiber D s).card := by
    by_cases large : 2 ≤ s.card
    · rw [high_fiber C c_overlap s large,high_fiber D d_overlap s large,same]
    · have pos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonzero)
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      have left := single_fiber C c_overlap a
      have right := single_fiber D d_overlap a
      rw [same,c_row] at left
      rw [d_row] at right
      omega
  have all_counts (s : Finset (Fin 6)) : (fiber C s).card = (fiber D s).card := by
    by_cases zero : s = ∅
    · subst s
      let nonempty := (Finset.univ : Finset (Finset (Fin 6))).erase ∅
      have agree : (∑ s ∈ nonempty, (fiber C s).card) = ∑ s ∈ nonempty, (fiber D s).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact counts_ne s (Finset.ne_of_mem_erase hs)
      have hc := Finset.sum_erase_add Finset.univ (fun s => (fiber C s).card) (Finset.mem_univ ∅)
      have hd := Finset.sum_erase_add Finset.univ (fun s => (fiber D s).card) (Finset.mem_univ ∅)
      rw [sum_fibers] at hc hd
      change (∑ s ∈ nonempty, (fiber C s).card) + (fiber C ∅).card = 19 at hc
      change (∑ s ∈ nonempty, (fiber D s).card) + (fiber D ∅).card = 19 at hd
      omega
    · exact counts_ne s zero
  let match_card (s : Finset (Fin 6)) : Fintype.card ↥(fiber C s) = Fintype.card ↥(fiber D s) := by
    rw [Fintype.card_coe,Fintype.card_coe,all_counts]
  let fibers (s : Finset (Fin 6)) : ↥(fiber C s) ≃ ↥(fiber D s) :=
    (Fintype.equivOfCardEq (match_card s))
  let as_fiber (W : Columns) (s : Finset (Fin 6)) : {p // W p = s} ≃ ↥(fiber W s) :=
    Equiv.subtypeEquivProp (funext fun p => propext (mem_fiber W s p).symm)
  let mapped (s : Finset (Fin 6)) : {p // C p = s} ≃ {p // D p = s} :=
    ((as_fiber C s).trans (fibers s)).trans (as_fiber D s).symm
  let e : Equiv.Perm (Fin 19) :=
    (Equiv.sigmaFiberEquiv C).symm.trans
      ((Equiv.sigmaCongrRight mapped).trans (Equiv.sigmaFiberEquiv D))
  exact ⟨e,fun p => (mapped (C p) ⟨p,rfl⟩).property⟩

end WeightNineteenSupportRelabel


namespace WeightNineteenForbiddenLayouts

open Finset
open WeightNineteenTriangleCertificate WeightNineteenSupportRelabel

def masks : List (List Nat) := [[3,5,6,9,10,12,17,18,33,34,52,4,8,8,16,16,32,32,0], [3,5,6,9,10,12,17,18,33,52,2,4,8,8,16,16,32,32,32], [3,5,6,9,10,17,18,28,33,34,4,4,8,8,16,16,32,32,32], [3,5,6,9,10,17,18,28,33,36,2,4,8,8,16,16,32,32,32], [3,5,6,9,10,17,18,33,36,56,2,4,4,8,8,16,16,32,32], [3,5,6,9,10,20,24,36,40,49,1,2,2,4,8,16,16,32,32], [3,5,6,9,10,17,28,33,50,2,4,4,8,8,16,16,32,32,32], [3,5,6,9,10,20,24,44,49,1,2,2,4,8,16,16,32,32,32], [3,5,9,14,18,20,34,36,56,1,1,2,4,8,8,16,16,32,32]]

def certs : List (List (Points × Points × Option Points)) := [[(3,10,some 18), (4,10,none)], [(4,9,none)], [(7,8,none)], [(7,8,some 10), (7,16,some 0), (7,17,none)], [(2,9,none)], [(2,9,some 14), (4,9,some 13), (9,11,none)], [(6,7,some 9), (6,16,some 0), (6,17,none)], [(2,8,some 13), (4,8,some 12), (8,10,none)], [(0,8,some 12), (1,8,some 11), (8,9,none)]]

def badColumns (i : Fin 9) (p : Points) : Finset (Fin 6) :=
  Finset.univ.filter fun a => ((masks[i.val]!)[p.val]!).testBit a.val

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 4096 in
theorem check_all : ∀ i : Fin 9, refute (available (badColumns i)) (certs[i.val]!) = true := by
  decide +kernel

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 4096 in
theorem check_no_repeated_pairs : ∀ (i : Fin 9) (p q : Points), p ≠ q →
      (badColumns i p ∩ badColumns i q).card ≤ 1 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 4096 in
theorem check_row_size : ∀ (i : Fin 9) (a : Fin 6),
    (Finset.univ.filter fun p => a ∈ badColumns i p).card = 5 := by
  decide +kernel

theorem invalid_layout (C : Columns)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (possible : ∃ F : Triangles, IsCover (available C) F)
    (i : Fin 9) (same : layout C = layout (badColumns i)) : False := by
  obtain ⟨e,property⟩ := relabel_columns C (badColumns i) c_overlap
    (check_no_repeated_pairs i) c_row (check_row_size i) same
  obtain ⟨F,valid⟩ := possible
  have faithful (a b : Points) : available (badColumns i) (e a) (e b) = available C a b := by
    apply Bool.eq_iff_iff.mpr
    simp only [available_iff,property]
    constructor
    · rintro ⟨ne,apart⟩
      exact ⟨fun eq => ne (congrArg e eq),apart⟩
    · rintro ⟨ne,apart⟩
      exact ⟨fun eq => ne (e.injective eq),apart⟩
  have cover := relabel_cover _ _ F e faithful valid
  have reject := refutation_sound _ _ (certs[i.val]!) cover (available_loopless (badColumns i))
  rw [check_all i] at reject
  contradiction

end WeightNineteenForbiddenLayouts

namespace WeightNineteenSupportRelabel

open Finset
open scoped BigOperators
open WeightNineteenTriangleCertificate

def supportMask (X : Finset (Fin 6)) : Nat := ∑ a ∈ X, 2^a.val

set_option maxHeartbeats 10000000 in
lemma support_mask_inj : Function.Injective supportMask := by
  have finite : ∀ X Y : Finset (Fin 6), supportMask X = supportMask Y → X = Y := by
    decide +kernel
  exact finite

def moveRows (C : Columns) (e : Equiv.Perm (Fin 6)) : Columns :=
  fun p => (C p).map e.toEmbedding

lemma row_bounds_after_permutation (C : Columns)
    (rows : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (e : Equiv.Perm (Fin 6)) (a : Fin 6) :
    (Finset.univ.filter fun p => a ∈ moveRows C e p).card = 5 := by
  have same : (Finset.univ.filter fun p => a ∈ moveRows C e p) =
      Finset.univ.filter fun p => e.symm a ∈ C p := by
    ext p
    simp only [moveRows,Finset.mem_filter,Finset.mem_map_equiv]
  rw [same,rows]

lemma overlap_after_permutation (C : Columns)
    (pairwise : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (e : Equiv.Perm (Fin 6)) (p q : Points) (ne : p ≠ q) :
    (moveRows C e p ∩ moveRows C e q).card ≤ 1 := by
  have same : moveRows C e p ∩ moveRows C e q = (C p ∩ C q).map e.toEmbedding := by
    ext a
    simp only [moveRows,Finset.mem_inter,Finset.mem_map_equiv]
  rw [same,Finset.card_map]
  exact pairwise p q ne

lemma available_after_permutation (C : Columns) (e : Equiv.Perm (Fin 6)) :
    available (moveRows C e) = available C := by
  funext p q
  apply Bool.eq_iff_iff.mpr
  simp only [available_iff]
  have same : Disjoint (moveRows C e p) (moveRows C e q) ↔ Disjoint (C p) (C q) := by
    simp only [Finset.disjoint_left,moveRows,Finset.mem_map_equiv]
    constructor
    · intro disj a ha hq
      exact disj (a := e a) (by simpa only [Equiv.symm_apply_apply] using ha)
        (by simpa only [Equiv.symm_apply_apply] using hq)
    · exact fun disj _ ha hq => disj ha hq
  rw [same]

lemma layout_after_permutation (C : Columns) (e : Equiv.Perm (Fin 6)) :
    layout (moveRows C e) = (layout C).image (Finset.map e.toEmbedding) := by
  have same : shared (moveRows C e) = shared C := by
    ext p
    simp only [shared,Finset.mem_filter,moveRows,Finset.card_map]
  unfold layout
  rw [same,Finset.image_image]
  rfl

theorem forbid_permuted_layout (C D : Columns) (e : Equiv.Perm (Fin 6))
    (rows : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (possible : ∃ F : Triangles, IsCover (available C) F)
    (codes_match : (layout C).image (fun X => supportMask (X.map e.toEmbedding)) =
      (layout D).image supportMask)
    (blocked : ∀ W : Columns, (∀ p q, p ≠ q → (W p ∩ W q).card ≤ 1) →
      (∀ a, (Finset.univ.filter fun p => a ∈ W p).card = 5) →
      (∃ F : Triangles, IsCover (available W) F) → layout W = layout D → False) : False := by
  let W := moveRows C e
  have pattern : layout W = layout D := by
    apply Finset.image_injective support_mask_inj
    change (layout (moveRows C e)).image supportMask = (layout D).image supportMask
    rw [layout_after_permutation,Finset.image_image]
    exact codes_match
  apply blocked W (overlap_after_permutation C overlap e) (row_bounds_after_permutation C rows e)
  · change ∃ F : Triangles, IsCover (available (moveRows C e)) F
    rwa [available_after_permutation]
  · exact pattern

end WeightNineteenSupportRelabel

namespace WeightNineteenTwoTriplesPruning

open Finset
open scoped BigOperators
open WeightNineteenSupportRelabel WeightNineteenForbiddenLayouts WeightNineteenTriangleCertificate

def patterns : List (List Nat) := [[3,5,6,9,10,17,28,33,50], [3,5,6,9,10,20,24,44,49], [3,5,9,14,18,20,34,36,56]]

def chooseBad (i : Fin 3) : Fin 9 := ⟨i.val+6,by omega⟩

set_option maxHeartbeats 30000000 in
set_option maxRecDepth 4096 in
lemma masks_exact : ∀ i : Fin 3, (layout (badColumns (chooseBad i))).image supportMask =
    (patterns[i.val]!).toFinset := by decide +kernel

theorem reject : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1.H1 := by
  classical
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1.H1
  dsimp only
  rintro ⟨M,_,_,_,colPairs,aSizes,bSizes,cSizes,_,_,_,card2,lower,upper,complementRestriction,e,i,encode⟩
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
  have loc (p : Fin 19) (a : Fin 6) : a ∈ C p ↔ M (.inl a) (.inl p) = true := by simp [C]
  have sizes (a : Fin 6) : (Finset.univ.filter fun p => a ∈ C p).card = 5 := by
    simpa only [loc] using aSizes a
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have on_both (z : Fin 6) (hz : z ∈ C p ∩ C q) :
        M (.inl z) (.inl p) = true ∧ M (.inl z) (.inl q) = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hz
      exact ⟨(loc p z).mp hp,(loc q z).mp hq⟩
    obtain ⟨_,_,same⟩ := colPairs (.inl p) (.inl q) (fun e => different (Sum.inl.inj e))
    exact Sum.inl.inj ((same (.inl a) (on_both a ha)).trans (same (.inl b) (on_both b hb)).symm)
  have possible := incidence_gives_cover M colPairs bSizes cSizes C loc
  have packed : (layout C).image (fun X => supportMask (X.map e.toEmbedding)) = (patterns[i.val]!).toFinset :=
    encode
  rw [← masks_exact i] at packed
  exact forbid_permuted_layout C _ e sizes overlap possible packed
    (fun W wo ws wpossible same => invalid_layout W wo ws wpossible (chooseBad i) same)

end WeightNineteenTwoTriplesPruning

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H2_R1.H1 := by
  exact WeightNineteenTwoTriplesPruning.reject
