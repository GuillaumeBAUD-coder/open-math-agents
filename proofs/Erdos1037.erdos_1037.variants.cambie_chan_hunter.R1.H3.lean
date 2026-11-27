import OMAReductions.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1

/-! Adjoin an isolated vertex and complement the graph. Old degrees become
n − d, while the new vertex has degree n. Positivity of the old degrees
ensures that the new degree is fresh at every iteration. -/

namespace OMA.Padding
open SimpleGraph

private noncomputable abbrev deg {n} (F : SimpleGraph (Fin n)) (v : Fin n) := (F.neighborSet v).ncard

private structure Good {n} (F : SimpleGraph (Fin n)) (t : ℝ) : Prop where
  mult : ∀ d : ℕ, {v | deg F v = d}.ncard ≤ 2
  count : 3/4 * (n : ℝ) ≤ ((Set.range (deg F)).ncard : ℝ)
  hom : ∀ s : Set (Fin n), F.IsHomogeneous s → (s.ncard : ℝ) ≤ t
  pos : ∀ v, 0 < deg F v

private lemma extend {n} (hn : 0 < n) {F : SimpleGraph (Fin n)} {t : ℝ} (h : Good F t) :
    ∃ G : SimpleGraph (Fin (n+1)), Good G (t+1) := by
  classical
  let e : Fin n ↪ Fin (n+1) := Fin.succEmb n
  let E := F.map e
  let G := Eᶜ
  have dsmall (v : Fin n) : deg F v < n := by
    simpa only [deg, ← Set.fintypeCard_eq_ncard, F.card_neighborSet_eq_degree, Fintype.card_fin]
      using F.degree_lt_card_verts v
  have transform (v : Fin (n+1)) : deg G v = n - deg E v := by
    simp only [deg, ← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree,
      G, SimpleGraph.degree_compl, Fintype.card_fin, Nat.add_sub_cancel]
  have dz : deg G 0 = n := by
    have hne : E.neighborSet 0 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨u,w,_,hu,_⟩ := (SimpleGraph.map_adj e F 0 v).mp hv
      exact Fin.succ_ne_zero u hu
    rw [transform, deg, hne]
    simp
  have ds (v : Fin n) : deg G v.succ = n - deg F v := by
    rw [transform]
    change n - ((F.map e).neighborSet (e v)).ncard = _
    rw [F.neighborSet_map, Set.ncard_image_of_injective _ e.injective]
  have lt (v : Fin n) : deg G v.succ < n := by
    rw [ds]
    have := h.pos v
    omega
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro d
    by_cases hd : d = n
    · subst d
      have sub : {v | deg G v = n} ⊆ ({0} : Set (Fin (n+1))) := by
        intro v hv
        induction v using Fin.cases with
        | zero => rfl
        | succ i => exact False.elim ((lt i).ne hv)
      exact (Set.ncard_le_ncard sub).trans (by simp)
    · have sub : {v | deg G v = d} ⊆ Fin.succ '' {u | deg F u = n-d} := by
        intro v hv
        change deg G v = d at hv
        induction v using Fin.cases with
        | zero => exact False.elim (hd (hv.symm.trans dz))
        | succ i =>
          refine ⟨i, ?_, rfl⟩
          change deg F i = n-d
          rw [ds] at hv
          have := dsmall i
          omega
      apply (Set.ncard_le_ncard sub).trans
      rw [Set.ncard_image_of_injective _ (Fin.succ_injective n)]
      exact h.mult _
  · let flip := fun d : ℕ => n-d
    have hi : Set.InjOn flip (Set.range (deg F)) := by
      rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩ hv
      dsimp [flip] at hv
      have := dsmall u
      have := dsmall v
      omega
    have hnew : n ∉ flip '' Set.range (deg F) := by
      rintro ⟨_,⟨v,rfl⟩,hv⟩
      exact (lt v).ne ((ds v).trans hv)
    have cover : insert n (flip '' Set.range (deg F)) ⊆ Set.range (deg G) := by
      rintro d (rfl | ⟨_,⟨v,rfl⟩,rfl⟩)
      · exact ⟨0,dz⟩
      · exact ⟨v.succ,ds v⟩
    have hc := Set.ncard_le_ncard cover (Set.finite_range _)
    rw [Set.ncard_insert_of_notMem hnew, hi.ncard_image] at hc
    have hc' : ((Set.range (deg F)).ncard : ℝ) + 1 ≤ ((Set.range (deg G)).ncard : ℝ) := by exact_mod_cast hc
    push_cast
    linarith [h.count]
  · intro s hs
    have homE : E.IsHomogeneous s := SimpleGraph.isHomogeneous_compl.mp hs
    let old := Fin.succ ⁻¹' s
    have hold : F.IsHomogeneous old := by
      rcases homE with hcl | hind
      · left
        intro x hx y hy hxy
        exact SimpleGraph.map_adj_apply.mp (hcl hx hy (e.injective.ne hxy))
      · right
        intro x hx y hy hxy hG
        exact hind hx hy (e.injective.ne hxy) (SimpleGraph.map_adj_apply.mpr hG)
    have sub : s ⊆ insert 0 (Fin.succ '' old) := by
      intro v hv
      induction v using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ i => exact Set.mem_insert_of_mem _ ⟨i,hv,rfl⟩
    have hc := (Set.ncard_le_ncard sub).trans (Set.ncard_insert_le _ _)
    rw [Set.ncard_image_of_injective _ (Fin.succ_injective n)] at hc
    have hc' : (s.ncard : ℝ) ≤ old.ncard + 1 := by exact_mod_cast hc
    linarith [h.hom old hold]
  · intro v
    induction v using Fin.cases with
    | zero => rwa [dz]
    | succ i => rw [ds]; exact Nat.sub_pos_of_lt (dsmall i)

end OMA.Padding

open OMA.Padding in
theorem OMA.solution : OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1.H3 := by
  intro n r hn _ F t hmult hcount hhom hpos
  have aux (k : ℕ) : ∃ G : SimpleGraph (Fin (n+k)), Good G (t+k) := by
    induction k with
    | zero => exact ⟨F, by simpa using (show Good F t from ⟨hmult,hcount,hhom,hpos⟩)⟩
    | succ k ih =>
      obtain ⟨G,hG⟩ := ih
      obtain ⟨G',hG'⟩ := extend (by omega) hG
      exact ⟨G', by simpa [add_assoc] using hG'⟩
  obtain ⟨G,hG⟩ := aux r
  exact ⟨G,hG.mult,hG.count,hG.hom⟩
