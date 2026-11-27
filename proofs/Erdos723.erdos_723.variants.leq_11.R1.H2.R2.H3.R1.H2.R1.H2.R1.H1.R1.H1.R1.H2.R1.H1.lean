import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1
import Mathlib
open Finset
/-!
The three inner intersections of rows 1,2,3 form a triangle of special
points. Each would need a distinct light line through the exterior triple
point, which has just two light lines. Edge-mask decoding follows the
finite-list lemma in the weight-sixteen graph classification by avivorly.
-/
namespace PlaneTriple

private theorem join_point {L : Type*} [Fintype L] [DecidableEq L]
    (M : L → Fin 111 → Bool) (p q : Fin 111) (pq : p ≠ q)
    (rows : ∀ l, (univ.filter fun r => M l r = true).card = 11)
    (degree : (univ.filter fun l => M l p = true).card = 11)
    (cols : ∀ x y, x ≠ y → ∀ l m, M l x = true → M l y = true →
      M m x = true → M m y = true → l = m) :
    ∃ l, M l p = true ∧ M l q = true := by
  classical
  let I := univ.filter fun l => M l p = true
  let D := fun l => (univ.filter fun r => M l r = true).erase p
  have memI (l : L) : l ∈ I ↔ M l p = true := by simp [I]
  have memD (l : L) (r : Fin 111) : r ∈ D l ↔ r ≠ p ∧ M l r = true := by simp [D]
  have disj : (I : Set L).PairwiseDisjoint D := by
    intro l hl m hm ne
    apply Finset.disjoint_left.mpr
    intro r lr mr
    obtain ⟨rp,lr⟩ := (memD _ _).mp lr
    exact ne (cols p r rp.symm l m ((memI _).mp hl) lr ((memI _).mp hm) ((memD _ _).mp mr).2)
  have sz (l) (hl : l ∈ I) : (D l).card = 10 := by
    have yes : p ∈ univ.filter (fun r => M l r = true) := by simpa using (memI _).mp hl
    simp [D,card_erase_of_mem yes,rows]
  have size : (I.biUnion D).card = 110 := by
    rw [card_biUnion disj, Finset.sum_congr rfl sz]
    simp [I, degree]
  have sub : I.biUnion D ⊆ univ.erase p := by
    intro r hr
    obtain ⟨l,_,lr⟩ := mem_biUnion.mp hr
    simp [(memD _ _).mp lr |>.1]
  have eq : I.biUnion D = univ.erase p := eq_of_subset_of_card_le sub (by simp [size])
  have hit : q ∈ I.biUnion D := by simp [eq,pq.symm]
  obtain ⟨l,il,ql⟩ := mem_biUnion.mp hit
  exact ⟨l,(memI _).mp il,((memD _ _).mp ql).2⟩

private theorem sum_degree {a b : ℕ} (f : Fin a ⊕ Fin b → Bool) :
    (univ.filter fun x => f x = true).card =
    (univ.filter fun i => f (.inl i) = true).card + (univ.filter fun j => f (.inr j) = true).card := by
  have e : (univ.filter fun x => f x = true) =
      (univ.filter fun i => f (.inl i) = true).disjSum (univ.filter fun j => f (.inr j) = true) := by
    ext x
    cases x <;> simp
  rw [e,card_disjSum]

namespace FiniteSearchMasks

variable {α : Type}

def bitMask (xs : List α) (chosen : α → Bool) : Nat :=
  (xs.zipIdx.map fun (x, i) => if chosen x then 2^i else 0).foldr Nat.lor 0

lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

theorem bitMask_testBit (xs : List α) (chosen : α → Bool) (i : Nat) :
    (bitMask xs chosen).testBit i = true ↔ ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [bitMask, foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

lemma bitMask_getElem_testBit (xs : List α) (chosen : α → Bool) (i : ℕ) (in_list : i < xs.length) :
    (bitMask xs chosen).testBit i = chosen xs[i] := by
  apply Bool.eq_iff_iff.mpr
  rw [bitMask_testBit]
  simp [List.getElem?_eq_getElem in_list]

end FiniteSearchMasks



open FiniteSearchMasks
def pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
private def adjacent (a b : Fin 8) := (0x2e69807 : Nat).testBit (pairs.idxOf (a,b))

private theorem first_triangle : ∀ T : Finset (Fin 8), T.card = 3 →
    (∀ a ∈ T, ∀ b ∈ T, a < b → adjacent a b = true) → T = {4,5,6} := by
  decide +kernel

private theorem mem_pairs : ∀ a b : Fin 8, a < b → (a,b) ∈ pairs := by decide

private theorem recover (g : Fin 8 → Fin 8 → Bool)
    (code : bitMask pairs (fun (a,b) => g a b) = 0x2e69807) (a b : Fin 8) (hab : a < b) :
    adjacent a b = g a b := by
  have h := mem_pairs a b hab
  apply Bool.eq_iff_iff.mpr
  change (0x2e69807 : Nat).testBit _ = true ↔ _
  rw [← code, bitMask_testBit,List.getElem?_idxOf h]
  simp

private theorem two_exact {α : Type*} [DecidableEq α] (T : Finset α) (a b : α)
    (ab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) (two : T.card = 2) : T = {a,b} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [ab,two]

private theorem no_three {α : Type*} [DecidableEq α] (T : Finset α) (two : T.card = 2)
    {a b c : α} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) : False := by
  rw [two_exact T a b ab ha hb two] at hc
  simp [ac.symm, bc.symm] at hc

theorem impossible : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := by
  classical
  dsimp [OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1]
  rintro ⟨M,S,_,rows,_,_,inside,outside,rowPairs,cols,_,triple,e,word⟩
  let H (p : Fin 111) := (univ.filter fun i : Fin 8 => M (.inl i) p = true).map e.symm.toEmbedding
  let B (p : Fin 111) := univ.filter fun j : Fin 72 => M (.inr j) p = true
  have hmem (p : Fin 111) (i : Fin 8) : i ∈ H p ↔ M (.inl (e i)) p = true := by simp [H]
  have bmem (p : Fin 111) (j : Fin 72) : j ∈ B p ↔ M (.inr j) p = true := by simp [B]
  let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ x ∉ S, M (.inl (e a)) x = true ∧ M (.inl (e b)) x = true)
  change bitMask pairs (fun (a,b) => G a b) = 0x2e69807 at word
  obtain ⟨t,ht⟩ := card_pos.mp (show 0 < (univ.filter fun p => p ∉ S ∧
    (univ.filter fun i : Fin 8 => M (.inl i) p = true).card = 3).card by omega)
  obtain ⟨htS,t3⟩ := (mem_filter.mp ht).2
  have Bt : (B t).card = 2 := by
    have := outside t htS
    dsimp [B]; omega
  have T : H t = {4,5,6} := by
    apply first_triangle
    · simpa [H] using t3
    · intro a ha b hb ab
      rw [recover G word a b ab]
      exact decide_eq_true ⟨ab.ne',t,htS,(hmem t a).mp ha,(hmem t b).mp hb⟩
  have point (a b : Fin 8) (ab : a < b) (off : adjacent a b = false) :
      ∃ p ∈ S, H p = {a,b} := by
    obtain ⟨p,⟨ap,bp⟩,_⟩ := rowPairs (.inl (e a)) (.inl (e b)) (by simpa using ab.ne)
    have ps : p ∈ S := by
      by_contra out
      have on : G a b = true := decide_eq_true ⟨ab.ne',p,out,ap,bp⟩
      rw [← recover G word a b ab,off] at on
      contradiction
    exact ⟨p,ps,two_exact _ _ _ ab.ne ((hmem p a).mpr ap) ((hmem p b).mpr bp)
      (by simpa [H] using (inside p ps).1)⟩
  obtain ⟨p,ps,hp⟩ := point 1 2 (by decide) (by decide)
  obtain ⟨q,qs,hq⟩ := point 1 3 (by decide) (by decide)
  obtain ⟨r,rs,hr⟩ := point 2 3 (by decide) (by decide)
  have light (x : Fin 111) (xs : x ∈ S) (dis : Disjoint (H x) (H t)) :
      ∃ j ∈ B t, M (.inr j) x = true := by
    have degree := sum_degree (fun l => M l x)
    obtain ⟨a,b⟩ := inside x xs
    rw [a,b] at degree
    obtain ⟨l,xl,tl⟩ := join_point M x t (fun w => htS (w ▸ xs)) rows degree cols
    cases l with
    | inr j => exact ⟨j,(bmem _ _).mpr tl,xl⟩
    | inl i =>
      exfalso
      apply (Finset.disjoint_left.mp dis) (a := e.symm i)
      · apply (hmem _ _).mpr; simpa using xl
      · apply (hmem _ _).mpr; simpa using tl
  obtain ⟨j,jt,jp⟩ := light p ps (by rw [hp,T]; decide)
  obtain ⟨k,kt,kq⟩ := light q qs (by rw [hq,T]; decide)
  obtain ⟨l,lt',lr⟩ := light r rs (by rw [hr,T]; decide)
  have diff (x y : Fin 111) (i : Fin 8) (u v : Fin 72) (ne : H x ≠ H y)
      (ix : i ∈ H x) (iy : i ∈ H y) (ux : M (.inr u) x = true) (vy : M (.inr v) y = true) : u ≠ v := by
    rintro rfl
    have eq := cols x y (fun w => ne (congrArg H w)) (.inl (e i)) (.inr u)
      ((hmem _ _).mp ix) ((hmem _ _).mp iy) ux vy
    cases eq
  exact no_three _ Bt jt kt lt'
    (diff p q 1 j k (by rw [hp,hq]; decide) (by rw [hp]; decide) (by rw [hq]; decide) jp kq)
    (diff p r 2 j l (by rw [hp,hr]; decide) (by rw [hp]; decide) (by rw [hr]; decide) jp lr)
    (diff q r 3 k l (by rw [hq,hr]; decide) (by rw [hq]; decide) (by rw [hr]; decide) kq lr)

end PlaneTriple

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := PlaneTriple.impossible
