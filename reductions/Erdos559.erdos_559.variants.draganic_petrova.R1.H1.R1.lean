import OMAReductions.R_Erdos559_erdos_559_variants_draganic_petrova_R1

/-! Peel long induced cycles from a subcubic graph. The remaining two inputs are the
bounded-chordality treewidth theorem and the conversion of a tree decomposition into
a bounded-degree tree partition, as in Draganic and Petrova, Lemmas 4.1 and 4.2. -/

namespace OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1
open SimpleGraph Finset

def H1 : Prop := open scoped Classical in
  ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (J : Finset (Fin n)),
    5 ≤ ℓ → G.maxDegree ≤ 3 →
    (∀ C ⊆ J, ¬ (ℓ ≤ C.card ∧ ∃ e : C ≃ Fin C.card,
      ∀ u v : C, G.Adj u.val v.val ↔
        (((e u).val+1)%C.card = (e v).val ∨ ((e v).val+1)%C.card = (e u).val))) →
    ∃ (t : ℕ) (S : SimpleGraph (Fin t)) (B : Fin t → Finset (Fin n)),
      S.IsTree ∧ (∀ a, (B a).card ≤ 2*ℓ+1 ∧ B a ⊆ J) ∧
      (∀ x ∈ J, ∃ a, x ∈ B a) ∧ (∀ x ∈ J, ∀ y ∈ J, G.Adj x y → ∃ a, x ∈ B a ∧ y ∈ B a) ∧
      ∀ x ∈ J, (S.induce {a | x ∈ B a}).Connected

def H2 : Prop := open scoped Classical in
  ∀ (n ℓ : ℕ) (G : SimpleGraph (Fin n)) (J : Finset (Fin n)),
    1 ≤ n → 5 ≤ ℓ → G.maxDegree ≤ 3 →
    (∃ (t : ℕ) (S : SimpleGraph (Fin t)) (B : Fin t → Finset (Fin n)),
      S.IsTree ∧ (∀ a, (B a).card ≤ 2*ℓ+1 ∧ B a ⊆ J) ∧
      (∀ x ∈ J, ∃ a, x ∈ B a) ∧ (∀ x ∈ J, ∀ y ∈ J, G.Adj x y → ∃ a, x ∈ B a ∧ y ∈ B a) ∧
      ∀ x ∈ J, (S.induce {a | x ∈ B a}).Connected) →
    ∃ (m : ℕ) (T : SimpleGraph (Fin m)), 1 ≤ m ∧ m ≤ n ∧ T.IsTree ∧ T.maxDegree ≤ 400*ℓ ∧
      ∃ f : J ↪ Fin m × Fin (400*ℓ), ∀ x y : J, G.Adj x.val y.val →
        (f x).1 = (f y).1 ∨ T.Adj (f x).1 (f y).1

private theorem peel {n : ℕ} (good : Finset (Fin n) → Prop)
    (pos : ∀ C, good C → 0 < C.card) (U : Finset (Fin n)) :
    ∃ (J : Finset (Fin n)) (cs : List (Finset (Fin n))), J ⊆ U ∧
      (∀ C ∈ cs, C ⊆ U ∧ Disjoint J C ∧ good C) ∧ cs.Pairwise Disjoint ∧
      (∀ x ∈ U, x ∈ J ∨ ∃ C ∈ cs, x ∈ C) ∧ ∀ C ⊆ J, ¬ good C := by
  classical
  by_cases ex : ∃ C ⊆ U, good C
  · obtain ⟨C,sub,hC⟩ := ex
    have small : (U \ C).card < U.card := by
      rw [card_sdiff_of_subset sub]
      have := pos C hC
      have := card_le_card sub
      omega
    obtain ⟨J,cs,jsub,valid,pair,cov,done_⟩ := peel good pos (U \ C)
    refine ⟨J,C::cs,jsub.trans sdiff_subset,?_,?_,?_,done_⟩
    · intro A ha
      rcases List.mem_cons.mp ha with rfl | h
      · exact ⟨sub,disjoint_left.mpr fun x hx => (mem_sdiff.mp (jsub hx)).2,hC⟩
      · exact ⟨(valid A h).1.trans sdiff_subset,(valid A h).2⟩
    · exact List.pairwise_cons.mpr ⟨fun A h => disjoint_right.mpr fun x hx =>
          (mem_sdiff.mp ((valid A h).1 hx)).2,pair⟩
    · intro x hx
      by_cases inC : x ∈ C
      · exact Or.inr ⟨C,by simp,inC⟩
      rcases cov x (mem_sdiff.mpr ⟨hx,inC⟩) with h | ⟨A,hA,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨A,List.mem_cons_of_mem _ hA,h⟩
  · exact ⟨U,[],Subset.rfl,by simp,by simp,fun x hx => Or.inl hx,fun C sub h => ex ⟨C,sub,h⟩⟩
termination_by U.card

theorem main : H1 → H2 → OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1.H1 := by
  classical
  intro chordal partition ℓ hℓ n hn G hdeg
  let good (C : Finset (Fin n)) := ℓ ≤ C.card ∧ ∃ e : C ≃ Fin C.card,
      ∀ u v : C, G.Adj u.val v.val ↔
        (((e u).val+1)%C.card = (e v).val ∨ ((e v).val+1)%C.card = (e u).val)
  obtain ⟨J,cs,_,valid,pair,cov,res⟩ := peel good (fun C h => lt_of_lt_of_le (by omega : 0 < ℓ) h.1) univ
  obtain ⟨m,T,hm,hmn,tree,degree,emb⟩ := partition n ℓ G J hn hℓ hdeg (chordal n ℓ G J hℓ hdeg res)
  refine ⟨m,T,J,cs,hm,hmn,tree,degree,fun x => cov x (mem_univ x),
    fun C h => (valid C h).2.1,pair,emb,fun C h => (valid C h).2.2,?_⟩
  intro i hi v hv
  let C := cs[i]
  have memC : C ∈ cs := List.getElem_mem hi
  obtain ⟨long,e,edges⟩ := (valid C memC).2.2
  have : NeZero C.card := ⟨by omega⟩
  let r := e ⟨v,hv⟩
  let a := (e.symm (r+1)).val
  let b := (e.symm (r-1)).val
  have ov : (1 : Fin C.card).val = 1 := by change 1 % C.card = 1; exact Nat.mod_eq_of_lt (by omega)
  have succ (s t : Fin C.card) (h : s+1 = t) : (s.val+1)%C.card = t.val := by
    simpa only [Fin.val_add,ov] using congrArg Fin.val h
  have ha : G.Adj v a := (edges ⟨v,hv⟩ (e.symm (r+1))).mpr (Or.inl (by
    simp only [Equiv.apply_symm_apply]; exact succ _ _ rfl))
  have hb : G.Adj v b := (edges ⟨v,hv⟩ (e.symm (r-1))).mpr (Or.inr (by
    simp only [Equiv.apply_symm_apply]; exact succ _ _ (sub_add_cancel r 1)))
  have distinct : a ≠ b := by
    intro eq
    have h : r+1 = r-1 := e.symm.injective (Subtype.ext eq)
    have h' : (1:Fin C.card)+1 = 0 := by
      have h'' := congrArg (fun z : Fin C.card => z+1) h
      rw [sub_add_cancel,add_assoc] at h''
      exact add_left_cancel (b := (1:Fin C.card)+1) (c := 0) (by simpa only [add_zero] using h'')
    have hv' := congrArg Fin.val h'
    simp only [Fin.val_add,ov,Fin.val_zero] at hv'
    rw [Nat.mod_eq_of_lt (by omega)] at hv'
    omega
  let U := univ.filter (fun x => G.Adj v x ∧
      (x ∈ J ∨ ∃ (j : ℕ) (hj : j < i), x ∈ cs[j]'(lt_trans hj hi)))
  have outside x (hx : x ∈ U) : x ∉ C := by
    rcases (mem_filter.mp hx).2.2 with h | ⟨j,hj,h⟩
    · exact disjoint_left.mp (valid C memC).2.1 h
    · exact disjoint_left.mp ((List.pairwise_iff_getElem.mp pair) j i _ hi hj) h
  have ha' : a ∉ U := fun h => outside a h (e.symm (r+1)).property
  have hb' : b ∉ U := fun h => outside b h (e.symm (r-1)).property
  have sub : insert a (insert b U) ⊆ G.neighborFinset v := by
    intro x hx
    apply (G.mem_neighborFinset _ _).mpr
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact (mem_filter.mp hx).2.1
  have bound := (card_le_card sub).trans ((G.degree_le_maxDegree v).trans hdeg)
  rw [card_insert_of_notMem (by simpa [distinct] using ha' : a ∉ insert b U),card_insert_of_notMem hb'] at bound
  change U.card ≤ 1
  omega

end OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1
