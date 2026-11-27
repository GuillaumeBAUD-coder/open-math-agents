import OMAReductions.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1

/-! Replace each vertex with t independent copies, then add r isolated vertices.
Count the two orientations of each edge to avoid choosing representatives of Sym2. -/

namespace OMA.Blowup
open SimpleGraph
open scoped Classical

lemma indepEmbedding {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ↪g H) : G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨s,hs⟩ := G.exists_isNIndepSet_indepNum
  have hi : H.IsIndepSet (s.map e.toEmbedding : Finset W) := by
    intro a ha b hb hab hadj
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hb
    exact hs.1 hu hv (fun eq => hab (congrArg e eq)) (e.map_rel_iff.mp hadj)
  simpa only [Finset.card_map,hs.2] using hi.card_le_indepNum

abbrev Vert (m t r : Nat) := (Fin m × Fin t) ⊕ Fin r

def expanded {m : Nat} (t r : Nat) (G : SimpleGraph (Fin m)) : SimpleGraph (Vert m t r) :=
  (G.comap Prod.fst).sum ⊥

lemma indepExpanded {m t r : Nat} (G : SimpleGraph (Fin m)) :
    (expanded t r G).indepNum ≤ t * G.indepNum + r := by
  classical
  obtain ⟨s,hs⟩ := (expanded t r G).exists_isNIndepSet_indepNum
  let A := s.toLeft.image Prod.fst
  have hi : G.IsIndepSet (A : Set (Fin m)) := by
    intro a ha b hb hab adj
    obtain ⟨⟨a',i⟩,hai,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨b',j⟩,hbj,rfl⟩ := Finset.mem_image.mp hb
    exact hs.1 (Finset.mem_toLeft.mp hai) (Finset.mem_toLeft.mp hbj)
      (by intro e; injection e with eq; exact hab (congrArg Prod.fst eq)) adj
  have cover : s.toLeft ⊆ A ×ˢ (Finset.univ : Finset (Fin t)) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_univ _⟩
  have bound := Finset.card_le_card cover
  simp only [Finset.card_product,Finset.card_univ,Fintype.card_fin] at bound
  have bound' := Nat.mul_le_mul_right t hi.card_le_indepNum
  have hr : s.toRight.card ≤ r := by simpa using Finset.card_le_univ s.toRight
  have hsum := Finset.card_toLeft_add_card_toRight (u:=s)
  rw [←hs.2,Nat.mul_comm t]
  omega

lemma edgeExpanded {m t r : Nat} (G : SimpleGraph (Fin m)) :
    t^2 * G.edgeFinset.card ≤ (expanded t r G).edgeFinset.card := by
  classical
  let inj (v : G.Dart × (Fin t × Fin t)) : (expanded t r G).Dart :=
    ⟨(.inl (v.1.fst,v.2.1), .inl (v.1.snd,v.2.2)),v.1.adj⟩
  have hinj : Function.Injective inj := by
    rintro ⟨a,i,j⟩ ⟨b,k,l⟩ h
    have hf := congrArg (fun d : (expanded t r G).Dart => d.fst) h
    have hs := congrArg (fun d : (expanded t r G).Dart => d.snd) h
    change Sum.inl (a.fst,i) = (Sum.inl (b.fst,k) : Vert m t r) at hf
    change Sum.inl (a.snd,j) = (Sum.inl (b.snd,l) : Vert m t r) at hs
    obtain ⟨ef,ei⟩ := Prod.mk.inj (Sum.inl.inj hf)
    obtain ⟨es,ej⟩ := Prod.mk.inj (Sum.inl.inj hs)
    exact Prod.ext (Dart.ext _ _ (Prod.ext ef es)) (Prod.ext ei ej)
  have h := Fintype.card_le_of_injective inj hinj
  simp only [Fintype.card_prod,Fintype.card_fin,dart_card_eq_twice_card_edges] at h
  nlinarith only [h]

lemma cliqueExpanded {m t r : Nat} (G : SimpleGraph (Fin (m+1))) (hc : G.CliqueFree 4) :
    (expanded t r G).CliqueFree 4 := by
  classical
  let f : expanded t r G →g G :=
    ⟨Sum.elim Prod.fst (fun _ => 0),by rintro (a | a) (b | b) h <;> first | exact h | contradiction⟩
  by_contra bad
  let g := f.comp (topEmbeddingOfNotCliqueFree bad).toHom
  exact (IsContained.not_cliqueFree (n:=4) ⟨g.toCopy g.injective_of_top_hom⟩) hc

end OMA.Blowup

open SimpleGraph OMA.Blowup

theorem OMA.solution : OMA.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1.H2 := by
  classical
  intro m t r G hc
  let B := expanded t r G
  have hcard : Fintype.card (Vert m t r) = m*t+r := by simp [Vert]
  let e := B.overFinIso hcard
  refine ⟨B.overFin hcard,?_,(indepEmbedding e.symm.toRelEmbedding).trans (indepExpanded G),?_⟩
  · apply CliqueFree.comap e.symm.isContained
    cases m with
    | zero =>
      have eq : G = ⊥ := Subsingleton.elim _ _
      subst G
      have bot : B = ⊥ := by
        ext x y; rcases x with ⟨a,i⟩ | a <;> rcases y with ⟨b,j⟩ | b <;> simp [B,expanded]
      rw [bot]; exact cliqueFree_bot (by decide)
    | succ m => exact cliqueExpanded G hc
  · rw [←e.card_edgeFinset_eq]
    exact edgeExpanded G

