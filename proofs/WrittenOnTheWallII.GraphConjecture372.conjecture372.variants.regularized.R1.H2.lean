import OMAReductions.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1

-- Step WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1.H2:
-- hypothesis H2 of reduction WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.regularized.R1
-- Credit: @kirinzhang

open SimpleGraph

private lemma parent_unique_of_isTree {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    (r u₁ u₂ v : α) (h₁ : T.Adj u₁ v) (h₂ : T.Adj u₂ v)
    (hd₁ : T.dist r v = T.dist r u₁ + 1) (hd₂ : T.dist r v = T.dist r u₂ + 1) :
    u₁ = u₂ := by
  classical
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist r v
  have hpen : ∀ u : α, T.Adj u v → T.dist r v = T.dist r u + 1 → u = p.penultimate := by
    intro u huv hdu
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist r u
    have hv_not_mem : v ∉ q.support := by
      intro hv
      have hspec := congrArg Walk.length (q.take_spec hv)
      rw [Walk.length_append] at hspec
      have hle : T.dist r v ≤ (q.takeUntil v hv).length := dist_le (q.takeUntil v hv)
      omega
    have hqc : (q.concat huv).IsPath := hq.concat hv_not_mem huv
    have heq : p = q.concat huv :=
      Subtype.mk.inj ((hT.isAcyclic.subsingleton_path r v).elim ⟨p, hp⟩ ⟨q.concat huv, hqc⟩)
    have hu_mem : u ∈ p.support := by
      rw [heq]
      exact q.support_subset_support_concat huv q.end_mem_support
    exact hT.isAcyclic.eq_penultimate_of_adj_end hp huv.symm hu_mem
  exact (hpen u₁ h₁ hd₁).trans (hpen u₂ h₂ hd₂).symm

private lemma exists_min_totalDominating {α : Type*} [Fintype α] [DecidableEq α]
    (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating ((Finset.univ : Finset α) : Set α) := by
    intro v
    obtain ⟨x, hxv⟩ := exists_ne v
    obtain ⟨p, _⟩ := hT.connected.exists_isPath v x
    have hnil : ¬ p.Nil := Walk.not_nil_of_ne hxv.symm
    exact ⟨p.snd, Finset.mem_coe.mpr (Finset.mem_univ p.snd), p.adj_snd hnil⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Finset.univ.card, Finset.univ, ⟨huniv, rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture372_conjecture372_variants_regularized_R1.H2 := by
  intro α _ _ T hT hn
  classical
  obtain ⟨D, hD_td, hD_card⟩ := exists_min_totalDominating T hT hn
  obtain ⟨r⟩ := hT.connected.nonempty
  let P : Finset α := Finset.univ.filter fun u =>
    u ∉ D ∧ ∃ v : α, T.Adj u v ∧ T.dist r v = T.dist r u + 1 ∧ v ∉ D
  have hcov : T.IsVertexCover ((D ∪ P : Finset α) : Set α) := by
    intro x y hxy
    by_cases hx : x ∈ D
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left P hx))
    · by_cases hy : y ∈ D
      · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left P hy))
      · rcases hT.dist_eq_dist_add_one_of_adj r hxy with hdist | hdist
        · refine Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right D ?_))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy, x, hxy.symm, hdist, hx⟩
        · refine Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right D ?_))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, y, hxy, hdist, hy⟩
  have hex : ∀ u ∈ P, ∃ w ∈ D, ∃ v : α,
      T.Adj u v ∧ T.dist r v = T.dist r u + 1 ∧ T.Adj v w ∧ T.dist r w = T.dist r v + 1 := by
    intro u hu
    obtain ⟨_, huD, v, huv, hduv, _⟩ := Finset.mem_filter.mp hu
    obtain ⟨w, hwD, hvw⟩ := hD_td v
    have hwD' : w ∈ D := Finset.mem_coe.mp hwD
    rcases hT.dist_eq_dist_add_one_of_adj r hvw with hdw | hdw
    · have huw : u = w := parent_unique_of_isTree hT r u w v huv hvw.symm hduv hdw
      exact False.elim (huD (huw ▸ hwD'))
    · exact ⟨w, hwD', v, huv, hduv, hvw, hdw⟩
  let f : α → α := fun u => if hu : u ∈ P then (hex u hu).choose else r
  have hf_maps : Set.MapsTo f (P : Set α) (D : Set α) := by
    intro u hu
    have huP : u ∈ P := Finset.mem_coe.mp hu
    dsimp only [f]
    rw [dif_pos huP]
    exact Finset.mem_coe.mpr (hex u huP).choose_spec.1
  have hf_inj : Set.InjOn f (P : Set α) := by
    intro u₁ hu₁ u₂ hu₂ hfeq
    have hu₁P : u₁ ∈ P := Finset.mem_coe.mp hu₁
    have hu₂P : u₂ ∈ P := Finset.mem_coe.mp hu₂
    dsimp only [f] at hfeq
    rw [dif_pos hu₁P, dif_pos hu₂P] at hfeq
    obtain ⟨v₁, huv₁, hduv₁, hvw₁, hdw₁⟩ := (hex u₁ hu₁P).choose_spec.2
    obtain ⟨v₂, huv₂, hduv₂, hvw₂, hdw₂⟩ := (hex u₂ hu₂P).choose_spec.2
    rw [← hfeq] at hvw₂ hdw₂
    have hv_eq : v₁ = v₂ :=
      parent_unique_of_isTree hT r v₁ v₂ (hex u₁ hu₁P).choose hvw₁ hvw₂ hdw₁ hdw₂
    rw [← hv_eq] at huv₂ hduv₂
    exact parent_unique_of_isTree hT r u₁ u₂ v₁ huv₁ huv₂ hduv₁ hduv₂
  have hP_card : P.card ≤ D.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hvc_enat : (T.vertexCoverNum.toNat : ℕ∞) ≤ ((D ∪ P).card : ℕ∞) := by
    rw [ENat.natCast_toNat (SimpleGraph.vertexCoverNum_ne_top_of_finite (G := T))]
    have h := hcov.vertexCoverNum_le
    simpa only [Set.encard_coe_eq_coe_finsetCard] using h
  have hvc_nat : T.vertexCoverNum.toNat ≤ (D ∪ P).card := Nat.cast_le.mp hvc_enat
  calc T.vertexCoverNum.toNat
      ≤ (D ∪ P).card := hvc_nat
    _ ≤ D.card + P.card := Finset.card_union_le D P
    _ ≤ D.card + D.card := Nat.add_le_add_left hP_card D.card
    _ = 2 * T.totalDominationNumber := by rw [hD_card, two_mul]
