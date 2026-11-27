import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H1_R1_H2_R1
import Mathlib

/-! Count the pairs separated by the union of two five-point lines. -/
open Finset
open scoped BigOperators

private def masks : List (List Nat) := [[3,5,6,9,10,12,17,18,20,33,40], [3,5,6,9,10,12,17,18,33,34,48], [3,5,6,9,10,12,17,18,33,36,48]]
private def u (i : Fin 3) : Fin 6 := ![3,2,4] i
private def v (i : Fin 3) : Fin 6 := ![5,3,5] i
private def meet (i : Fin 3) (a b : Fin 6) : ℕ :=
  if 2^a.val + 2^b.val ∈ masks[i.val]! then 1 else 0
private def allowance (i : Fin 3) (a : Fin 6) : ℕ :=
  if a = u i ∨ a = v i then 0 else
  let d := meet i a (u i) + meet i a (v i)
  d*(5-d)
private theorem diff_uv : ∀ i, u i ≠ v i := by decide
private theorem small_total : ∀ i : Fin 3, ∑ a : Fin 6, allowance i a ≤ 14 := by decide

private abbrev Rows := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
private abbrev Point := Fin 19
private def cross (L S : Finset Point) := (L ∩ S).card * (L \ S).card
private lemma cross_le {x t : ℕ} (h : x ≤ t) (ht : t ≤ 2) : x*(5-x) ≤ t*(5-t) := by
  interval_cases t <;> interval_cases x <;> decide

private lemma cut_bound (L : Rows → Finset Point) (i : Fin 3)
    (sizes : ∀ a, (L (.inl a)).card = 5)
    (tb : ∀ b, (L (.inr (.inl b))).card = 3) (sc : ∀ c, (L (.inr (.inr c))).card = 1)
    (joint : ∀ a b, a ≠ b → (L (.inl a) ∩ L (.inl b)).card ≤ meet i a b)
    (cover : ∀ p q : Point, p ≠ q → ∃ l, p ∈ L l ∧ q ∈ L l) : False := by
  classical
  let S := L (.inl (u i)) ∪ L (.inl (v i))
  have hm (a b : Fin 6) : meet i a b ≤ 1 := by unfold meet; split <;> decide
  have hS := card_union_add_card_inter (L (.inl (u i))) (L (.inl (v i)))
  have hj := (joint _ _ (diff_uv i)).trans (hm _ _)
  change S.card + _ = _ at hS
  rw [sizes,sizes] at hS
  have whole : (univ \ S).card + S.card = 19 := by
    simpa using card_sdiff_add_card_eq_card (subset_univ S)
  have lower : 90 ≤ S.card * (univ \ S).card := by
    have hval : S.card = 9 ∨ S.card = 10 := by omega
    rcases hval with h|h <;> rw [h] at whole ⊢ <;>
      have : (univ \ S).card = _ := Nat.eq_sub_of_add_eq whole <;> omega
  have upper : S.card * (univ \ S).card ≤ ∑ l, cross (L l) S := by
    let R (l : Rows) := ((L l ∩ S) ×ˢ (L l \ S))
    have hc : S ×ˢ (univ \ S) ⊆ univ.biUnion R := by
      rintro ⟨p,q⟩ hpq
      obtain ⟨hp,hq⟩ := mem_product.mp hpq
      have hqn := (mem_sdiff.mp hq).2
      obtain ⟨l,hl,hl'⟩ := cover p q (by rintro rfl; exact hqn hp)
      exact mem_biUnion.mpr ⟨l,mem_univ _,mem_product.mpr ⟨mem_inter.mpr ⟨hl,hp⟩,mem_sdiff.mpr ⟨hl',hqn⟩⟩⟩
    simpa [R,cross,card_product] using (card_le_card hc).trans card_biUnion_le
  have aa : ∑ a : Fin 6, cross (L (.inl a)) S ≤ 14 := by
    refine (sum_le_sum (g := allowance i) ?_).trans (small_total i)
    intro a _
    by_cases ha : a = u i ∨ a = v i
    · have hs : L (.inl a) ⊆ S := by rcases ha with h|h <;> subst a; exact subset_union_left; exact subset_union_right
      simp [cross,sdiff_eq_empty_iff_subset.mpr hs,allowance,ha]
    · have hh := card_sdiff_add_card_inter (L (.inl a)) S
      rw [sizes] at hh
      have hv : (L (.inl a) ∩ S).card ≤ meet i a (u i) + meet i a (v i) := by
        rw [show L (.inl a) ∩ S = _ from inter_union_distrib_left _ _ _]
        exact (card_union_le _ _).trans (Nat.add_le_add (joint _ _ (fun h => ha (Or.inl h))) (joint _ _ (fun h => ha (Or.inr h))))
      simp only [allowance,if_neg ha,cross]
      rw [show (L (.inl a) \ S).card = 5 - (L (.inl a) ∩ S).card by omega]
      exact cross_le hv (by have := hm a (u i); have := hm a (v i); omega)
  have short (W : Finset Point) {n : ℕ} (h : W.card = n) (bound : n=3 ∨ n=1) :
      cross W S ≤ (if n=3 then 2 else 0) := by
    have H := card_sdiff_add_card_inter W S
    rw [h] at H
    unfold cross
    generalize (W ∩ S).card = x at H ⊢
    generalize (W \ S).card = y at H ⊢
    have hx : x ≤ 3 := by omega
    rcases bound with rfl|rfl <;> norm_num <;> interval_cases x <;> omega
  have bb : ∑ b : Fin 37, cross (L (.inr (.inl b))) S ≤ 74 := by
    simpa using sum_le_sum (s := (univ : Finset (Fin 37))) fun b _ => short _ (tb b) (Or.inl rfl)
  have cc : ∑ c : Fin 68, cross (L (.inr (.inr c))) S ≤ 0 := by
    simpa using sum_le_sum (s := (univ : Finset (Fin 68))) fun c _ => short _ (sc c) (Or.inr rfl)
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type] at upper
  omega

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H1_R1_H2_R1.H1 := by
  classical
  rintro ⟨M,_,_,linePair,pointPair,sa,sb,sc,_,_,two,e,i,pat⟩
  let L₀ (l : Rows) := univ.filter fun p : Point => M l (.inl p) = true
  let r : Rows ≃ Rows := Equiv.sumCongr e.symm (Equiv.refl _)
  let L (l : Rows) := L₀ (r l)
  let C (p : Point) := univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
  apply cut_bound L i (fun a => sa (e.symm a)) sb sc
  · intro a b hab
    let x := e.symm a
    let y := e.symm b
    have hxy : x ≠ y := fun h => hab (e.symm.injective h)
    have hsize : (L (.inl a) ∩ L (.inl b)).card ≤ 1 := by
      apply card_le_one.mpr
      intro p hp q hq
      have mem (w : Point) (hw : w ∈ L (.inl a) ∩ L (.inl b)) :
          M (.inl x) (.inl w) = true ∧ M (.inl y) (.inl w) = true :=
        ⟨(mem_filter.mp (mem_inter.mp hw).1).2,(mem_filter.mp (mem_inter.mp hw).2).2⟩
      have hh := linePair (.inl x) (.inl y) (by simpa using hxy)
      exact Sum.inl.inj (hh.unique (mem p hp) (mem q hq))
    by_cases hn : (L (.inl a) ∩ L (.inl b)).Nonempty
    · obtain ⟨p,hp⟩ := hn
      have hx : x ∈ C p := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_inter.mp hp).1).2⟩
      have hy : y ∈ C p := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_inter.mp hp).2).2⟩
      have sub : ({x,y} : Finset (Fin 6)) ⊆ C p := insert_subset hx (singleton_subset_iff.mpr hy)
      have hpC : C p = {x,y} := (eq_of_subset_of_card_le sub (by simpa [hxy] using two p)).symm
      have memF : C p ∈ (univ.filter fun p : Point => 2 ≤ (C p).card).image C :=
        mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,by simp [hpC,hxy]⟩)
      have code := mem_image_of_mem (fun X : Finset (Fin 6) => ∑ j ∈ X.map e.toEmbedding, 2^j.val) memF
      change _ = (masks[i.val]!).toFinset at pat
      rw [pat] at code
      have hm : 2^a.val + 2^b.val ∈ masks[i.val]! := by simpa [hpC,x,y,hab] using code
      unfold meet
      rw [if_pos hm]
      exact hsize
    · simp [not_nonempty_iff_eq_empty.mp hn]
  · intro p q hpq
    obtain ⟨l,hl,_⟩ := pointPair (.inl p) (.inl q) (by simpa using hpq)
    refine ⟨r.symm l, ?_, ?_⟩ <;> simp only [L,L₀,Equiv.apply_symm_apply,mem_filter,mem_univ,true_and]
    · exact hl.1
    · exact hl.2
