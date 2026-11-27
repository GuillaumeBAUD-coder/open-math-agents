import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

-- Credit: @avivorly
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1.H1 := by
  classical
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1.H1
  dsimp only
  rintro ⟨M,S,_,_,_,twoSecant,inside,outside,rowPairs,_,anchor,triple⟩
  obtain ⟨p,hp,four,side⟩ := anchor
  obtain ⟨q,hq,three⟩ := triple
  let A (a : Fin 8) (x : Fin 111) := M (.inl a) x
  let C : Finset (Fin 8) := Finset.univ.filter fun a => A a p = true
  let D : Finset (Fin 8) := Finset.univ \ C
  let T : Finset (Fin 8) := Finset.univ.filter fun a => A a q = true
  have sizeC : C.card = 4 := four
  have sizeT : T.card = 3 := three
  have different : p ≠ q := by
    intro h
    have same : C = T := by simp [C,T,h]
    rw [same,sizeT] at sizeC
    omega
  have sizeD : D.card = 4 := by
    change (Finset.univ \ C).card = 4
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C),Finset.card_univ,Fintype.card_fin,sizeC]
  have C_iff (a : Fin 8) : a ∈ C ↔ A a p = true := by simp [C]
  have T_iff (a : Fin 8) : a ∈ T ↔ A a q = true := by simp [T]
  have row_unique (a b : Fin 8) (different : a ≠ b) (x y : Fin 111)
      (on_x : A a x = true ∧ A b x = true) (on_y : A a y = true ∧ A b y = true) : x = y := by
    obtain ⟨_,_,unique⟩ := rowPairs (.inl a) (.inl b) (fun same => different (Sum.inl.inj same))
    exact (unique x on_x).trans (unique y on_y).symm
  have outside_side (a b : Fin 8) (different : a ≠ b) :
      (∃ x ∉ S, A a x = true ∧ A b x = true) ↔ (a ∈ C ↔ b ∈ C) := side a b different
  have q_in_D : T ⊆ D := by
    intro a ha
    have count : (T.erase a).card = 2 := by rw [Finset.card_erase_of_mem ha,sizeT]
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase a).card)
    obtain ⟨not_a,hbT⟩ := Finset.mem_erase.mp hb
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro aC
    have hit : A a q = true ∧ A b q = true := ⟨(T_iff a).mp ha,(T_iff b).mp hbT⟩
    have bC := ((outside_side a b not_a.symm).mp ⟨q,hq,hit⟩).mp aC
    exact different (row_unique a b not_a.symm p q ⟨(C_iff a).mp aC,(C_iff b).mp bC⟩ hit)
  have one_unused : (D \ T).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset q_in_D,sizeD,sizeT]
  have in_D (x : Fin 111) (hx : x ∈ S) : ∃ a ∈ D, A a x = true := by
    let here : Finset (Fin 8) := Finset.univ.filter fun a => A a x = true
    have card2 : here.card = 2 := (inside x hx).1
    obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp card2
    have on_a : A a x = true := (Finset.mem_filter.mp (eq ▸ Finset.mem_insert_self _ _ : a ∈ here)).2
    have on_b : A b x = true :=
      (Finset.mem_filter.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _) : b ∈ here)).2
    by_cases aC : a ∈ C
    · refine ⟨b,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩,on_b⟩
      intro bC
      obtain ⟨z,hz,pair⟩ := (outside_side a b ne).mpr ⟨fun _ => bC,fun _ => aC⟩
      exact hz ((row_unique a b ne x z ⟨on_a,on_b⟩ pair) ▸ hx)
    · exact ⟨a,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,aC⟩,on_a⟩
  let B : Finset (Fin 72) := Finset.univ.filter fun b => M (.inr b) q = true
  have bCard : B.card = 2 := by
    have relation := outside q hq
    change 2*T.card + B.card = 8 at relation
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have onQ := (Finset.mem_filter.mp hb).2
  let onB := S.filter fun x => M (.inr b) x = true
  have bSize : onB.card = 2 := twoSecant b
  obtain ⟨x,y,ne,eq⟩ := Finset.card_eq_two.mp bSize
  have hit_x := Finset.mem_filter.mp (eq ▸ Finset.mem_insert_self _ _ : x ∈ onB)
  have hit_y := Finset.mem_filter.mp
    (eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _) : y ∈ onB)
  have distinct_line (a : Fin 8) : (.inl a : Fin 8 ⊕ Fin 72) ≠ .inr b := by simp
  have one_inter (a : Fin 8) (u v : Fin 111)
      (here : A a u = true ∧ M (.inr b) u = true)
      (there : A a v = true ∧ M (.inr b) v = true) : u = v := by
    obtain ⟨_,_,unique⟩ := rowPairs (.inl a) (.inr b) (distinct_line a)
    exact (unique u here).trans (unique v there).symm
  have choose_unused (u : Fin 111) (hu : u ∈ S) (on_u : M (.inr b) u = true) :
      ∃ a ∈ D \ T, A a u = true := by
    obtain ⟨a,ha,yes⟩ := in_D u hu
    refine ⟨a,Finset.mem_sdiff.mpr ⟨ha,?_⟩,yes⟩
    intro on_t
    exact hq ((one_inter a u q ⟨yes,on_u⟩ ⟨(T_iff a).mp on_t,onQ⟩) ▸ hu)
  obtain ⟨a,ha,on_a⟩ := choose_unused x hit_x.1 hit_x.2
  obtain ⟨a',ha',on_a'⟩ := choose_unused y hit_y.1 hit_y.2
  have same := Finset.card_le_one.mp one_unused a ha a' ha'
  exact ne (one_inter a x y ⟨on_a,hit_x.2⟩ ⟨same.symm ▸ on_a',hit_y.2⟩)
