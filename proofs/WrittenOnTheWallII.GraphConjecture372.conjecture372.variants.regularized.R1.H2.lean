import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

namespace OMA.TreeCover
open SimpleGraph

lemma parents {V : Type} {T : SimpleGraph V} (hT : T.IsTree) (root x u v : V)
    (hxu : T.Adj x u) (hxv : T.Adj x v)
    (hu : T.dist root x = T.dist root u+1) (hv : T.dist root x = T.dist root v+1) : u=v := by
  obtain ⟨p,hp,hlenp⟩ := hT.connected.exists_path_of_dist root u
  obtain ⟨q,hq,hlenq⟩ := hT.connected.exists_path_of_dist root v
  have hpc : (p.concat hxu.symm).IsPath :=
    (p.concat hxu.symm).isPath_of_length_eq_dist (by rw [p.length_concat,hlenp]; omega)
  have hqc : (q.concat hxv.symm).IsPath :=
    (q.concat hxv.symm).isPath_of_length_eq_dist (by rw [q.length_concat,hlenq]; omega)
  have he : (⟨p.concat hxu.symm,hpc⟩ : T.Path root x) = ⟨q.concat hxv.symm,hqc⟩ :=
    (hT.isAcyclic.subsingleton_path root x).elim _ _
  have hh := congrArg (fun z : T.Path root x => z.val.penultimate) he
  simpa using hh

lemma cover_bound {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (hT : T.IsTree) (D : Finset V) (hD : T.IsTotalDominating (D : Set V)) :
    T.vertexCoverNum.toNat ≤ 2*D.card := by
  classical
  let root := hT.connected.nonempty.some
  let P := Finset.univ.filter (fun u => u ∉ D ∧ ∃ v, v ∉ D ∧ T.Adj u v ∧
    T.dist root v=T.dist root u+1)
  have hm : ∀ u ∈ P, ∃ v w, T.Adj u v ∧ T.dist root v=T.dist root u+1 ∧
      w ∈ D ∧ T.Adj v w ∧ T.dist root w=T.dist root v+1 := by
    intro u hu
    obtain ⟨_,huD,v,hvD,huv,hdep⟩ := Finset.mem_filter.mp hu
    obtain ⟨w,hwD,hvw⟩ := hD v
    refine ⟨v,w,huv,hdep,hwD,hvw,?_⟩
    rcases hT.dist_eq_dist_add_one_of_adj root hvw with hw | hw
    · have he := parents hT root v u w huv.symm hvw hdep hw
      subst w
      exact (huD hwD).elim
    · exact hw
  choose! child f h using hm
  have hmaps : ∀ u ∈ P, f u ∈ D := fun u hu => (h u hu).2.2.1
  have hinj : Set.InjOn f (P : Set V) := by
    intro u hu v hv he
    obtain ⟨hu1,hu2,hu3,hu4,hu5⟩ := h u hu
    obtain ⟨hv1,hv2,hv3,hv4,hv5⟩ := h v hv
    have hc : child u=child v := parents hT root (f u) (child u) (child v)
      hu4.symm (by rw [he]; exact hv4.symm) hu5 (by rw [he]; exact hv5)
    exact parents hT root (child u) u v hu1.symm
      (by rw [hc]; exact hv1.symm) hu2 (by rw [hc]; exact hv2)
  have hcardP := Finset.card_le_card_of_injOn f hmaps hinj
  let C := D ∪ P
  have hcover : T.IsVertexCover (C : Set V) := by
    intro u v huv
    by_cases hu : u ∈ D
    · exact Or.inl (Finset.mem_union_left P hu)
    by_cases hv : v ∈ D
    · exact Or.inr (Finset.mem_union_left P hv)
    rcases hT.dist_eq_dist_add_one_of_adj root huv with hdep | hdep
    · exact Or.inr (Finset.mem_union_right D (Finset.mem_filter.mpr
        ⟨Finset.mem_univ v,hv,u,hu,huv.symm,hdep⟩))
    · exact Or.inl (Finset.mem_union_right D (Finset.mem_filter.mpr
        ⟨Finset.mem_univ u,hu,v,hv,huv,hdep⟩))
  have hvcle : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard] using hcover.vertexCoverNum_le
  have hvcnat : T.vertexCoverNum.toNat ≤ C.card := by
    simpa using ENat.toNat_le_toNat hvcle (by simp)
  have hcardC : C.card ≤ D.card+P.card := Finset.card_union_le D P
  omega

end OMA.TreeCover

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2: hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @DeepDuke
-- H2 := ∀ (α : Type) [Fintype α] [DecidableEq α] (T : SimpleGraph α), T.IsTree →     2 ≤ Fintype.card α →     T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  intro V _ _ T hT hcard
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hex : {n : ℕ | ∃ D : Finset V, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V,Finset.univ,?_,by simp⟩
    intro v
    obtain ⟨w,hw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨w,Finset.mem_univ w,hw⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem hex
  have hceq : D.card=T.totalDominationNumber := hD.card_eq
  rw [← hceq]
  exact OMA.TreeCover.cover_bound hT D hD.isTotalDominating

