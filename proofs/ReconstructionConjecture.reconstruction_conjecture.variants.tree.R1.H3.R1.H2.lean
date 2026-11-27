import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1

/-!
# Proof of `tree.R1.H3.R1.H2`

Center degree equality and singleton-limb elimination for even-diameter (`2 * r`, `r >= 2`) non-path hypomorphic trees (`tree.R1.H3.R1.H2`).
-/

-- Credit: @green-notes

open SimpleGraph

section TreeR1H3R1H2

open Classical

private def pathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]

private lemma isTree_path_eq {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} {p q : T.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]

private lemma split_walk_first_mem {U : Type} (T : SimpleGraph U) (P : Set U)
    [DecidablePred (· ∈ P)] {y c : U} (q : T.Walk y c) (hc : c ∈ P) :
    ∃ (z : U) (q₁ : T.Walk y z) (q₂ : T.Walk z c),
      z ∈ P ∧ q = q₁.append q₂ ∧ (∀ u ∈ q₁.support, u ∈ P → u = z) := by
  induction q with
  | nil =>
    exact ⟨_, Walk.nil, Walk.nil, hc, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
  | @cons a b c h q' ih =>
    by_cases ha : a ∈ P
    · exact ⟨a, Walk.nil, Walk.cons h q', ha, rfl, fun u hu _ => by simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
    · obtain ⟨z, q₁, q₂, hz, hq', huniq⟩ := ih hc
      refine ⟨z, Walk.cons h q₁, q₂, hz, by rw [hq']; rfl, fun u hu huP => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact False.elim (ha huP)
      · exact huniq u hu huP

private lemma start_notMem_tail_support_of_isPath {U : Type} {T : SimpleGraph U} {a b : U}
    {w : T.Walk a b} (hw : w.IsPath) : a ∉ w.support.tail := by
  cases w <;> simp_all [Walk.isPath_def]

private lemma isPath_append_of_first_meet {U : Type} {T : SimpleGraph U}
    {y z x : U} {q₁ : T.Walk y z} {s : T.Walk z x}
    (hq₁ : q₁.IsPath) (hs : s.IsPath)
    (hmeet : ∀ u ∈ q₁.support, u ∈ s.support.tail → u = z) :
    (q₁.append s).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hq₁.support_nodup, hs.support_nodup.tail, fun u huq hus => ?_⟩
  have huz : u = z := hmeet u huq hus
  subst huz
  exact start_notMem_tail_support_of_isPath hs hus

private lemma exists_unique_center_of_diam_eq_two_mul {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ c : U, T.eccent c = r ∧ ∀ v : U, v ≠ c → (r : ℕ∞) < T.eccent v := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  let c : U := p.getVert r
  let p₁ : T.Walk x0 c := p.take r
  let p₂ : T.Walk c xd := p.drop r
  have hp1 : p₁.IsPath := hp.take r
  have hp2 : p₂.IsPath := hp.drop r
  have hp1_len : p₁.length = r := by rw [Walk.take_length]; omega
  have hp2_len : p₂.length = r := by rw [Walk.drop_length]; omega
  have hp_app : p₁.append p₂ = p := p.append_take_drop_eq r
  have hkey : ∀ y : U, (T.dist y xd = T.dist y c + r ∨ T.dist y x0 = T.dist y c + r) := by
    intro y
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist y c
    obtain ⟨z, q₁, q₂, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem T {u | u ∈ p.support} q (p.getVert_mem_support r)
    have hq_app : (q₁.append q₂).IsPath := hq_eq ▸ hq
    have hq1 : q₁.IsPath := hq_app.of_append_left
    have hq2 : q₂.IsPath := hq_app.of_append_right
    have hq_len : q.length = q₁.length + q₂.length := by rw [hq_eq, Walk.length_append]
    have hz12 : z ∈ p₁.support ∨ z ∈ p₂.support :=
      (Walk.mem_support_append_iff p₁ p₂).mp (hp_app.symm ▸ hz_mem)
    rcases hz12 with hz1 | hz2
    · obtain ⟨a, b, ha, hb, hp1_eq⟩ := hp1.mem_support_iff_exists_append.mp hz1
      let pR : T.Walk z xd := b.append p₂
      have hp_decomp : p = a.append pR := by rw [← hp_app, hp1_eq, Walk.append_assoc]
      have hpR : pR.IsPath := (hp_decomp ▸ hp).of_append_right
      have hb_eq : q₂ = b := isTree_path_eq T hT hq2 hb
      have hpR_len : pR.length = q₂.length + r := by rw [Walk.length_append, hp2_len, hb_eq]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pR.support.tail → u = z := by
        intro u huq hus
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_right a pR (List.mem_of_mem_tail hus))
      have hqpR : (q₁.append pR).IsPath := isPath_append_of_first_meet hq1 hpR hmeet
      have hdist : (q₁.append pR).length = T.dist y xd :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pR) hqpR
      left
      rw [Walk.length_append, hpR_len] at hdist
      omega
    · obtain ⟨a, b, ha, hb, hp2_eq⟩ := hp2.mem_support_iff_exists_append.mp hz2
      let pL : T.Walk x0 z := p₁.append a
      have hp_decomp : p = pL.append b := by rw [← hp_app, hp2_eq, ← Walk.append_assoc]
      have hpL : pL.IsPath := (hp_decomp ▸ hp).of_append_left
      have ha_eq : q₂ = a.reverse := isTree_path_eq T hT hq2 ha.reverse
      have hpL_len : pL.reverse.length = r + q₂.length := by
        rw [Walk.length_reverse, Walk.length_append, hp1_len, ha_eq, Walk.length_reverse]
      have hmeet : ∀ u ∈ q₁.support, u ∈ pL.reverse.support.tail → u = z := by
        intro u huq hus
        have hus1 : u ∈ pL.reverse.support := List.mem_of_mem_tail hus
        rw [Walk.support_reverse, List.mem_reverse] at hus1
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_left pL b hus1)
      have hqpL : (q₁.append pL.reverse).IsPath := isPath_append_of_first_meet hq1 hpL.reverse hmeet
      have hdist : (q₁.append pL.reverse).length = T.dist y x0 :=
        isTree_dist_eq_length_of_isPath T hT (q₁.append pL.reverse) hqpL
      right
      rw [Walk.length_append, hpL_len] at hdist
      omega
  have hediam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.connected
  have hle_r : ∀ y : U, T.dist y c ≤ r := by
    intro y
    rcases hkey y with hy | hy
    · have := dist_le_diam hediam (u := y) (v := xd); omega
    · have := dist_le_diam hediam (u := y) (v := x0); omega
  have hecc_le : T.eccent c ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected c y).coe_dist_eq_edist, SimpleGraph.dist_comm]
    exact Nat.cast_le.mpr (hle_r y)
  have hecc_ge : (r : ℕ∞) ≤ T.eccent c := by
    have hcx0 : T.dist c x0 = r := by
      have h := isTree_dist_eq_length_of_isPath T hT p₁ hp1
      rw [SimpleGraph.dist_comm, ← h, hp1_len]
    rw [← hcx0, (hT.connected c x0).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  refine ⟨c, le_antisymm hecc_le hecc_ge, fun v hvc => ?_⟩
  have hpos : 0 < T.dist v c := hT.connected.pos_dist_of_ne hvc
  rcases hkey v with hv | hv
  · have hlt : (r : ℕ∞) < (T.dist v xd : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v xd).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
  · have hlt : (r : ℕ∞) < (T.dist v x0 : ℕ∞) := Nat.cast_lt.mpr (by omega)
    rw [(hT.connected v x0).coe_dist_eq_edist] at hlt
    exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent

private lemma induce_support_iso_pathG {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {a b : U} (p : T.Walk a b) (hp : p.IsPath) :
    Nonempty (T.induce (p.support.toFinset : Set U) ≃g pathG (p.length + 1)) := by
  let S : Finset U := p.support.toFinset
  let f : Fin (p.length + 1) → S := fun i =>
    ⟨p.getVert i.val, List.mem_toFinset.mpr (p.getVert_mem_support i.val)⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval : p.getVert i.val = p.getVert j.val := congrArg Subtype.val hij
    exact Fin.ext (hp.getVert_injOn (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) hval)
  have hfsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rw [List.mem_toFinset, Walk.mem_support_iff_exists_getVert] at hv
    obtain ⟨i, hi_eq, hi_le⟩ := hv
    exact ⟨⟨i, Nat.lt_succ_of_le hi_le⟩, Subtype.ext hi_eq⟩
  let e : Fin (p.length + 1) ≃ S := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hrel : ∀ i j : Fin (p.length + 1),
      (T.induce (S : Set U)).Adj (e i) (e j) ↔ (pathG (p.length + 1)).Adj i j := by
    intro i j
    change T.Adj (p.getVert i.val) (p.getVert j.val) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    constructor
    · intro hadj
      rcases Nat.lt_trichotomy i.val j.val with hij | hij | hji
      · left
        let q : T.Walk (p.getVert i.val) (p.getVert j.val) :=
          ((p.take j.val).drop i.val).copy
            (by simp [Walk.take_getVert, Nat.min_eq_right hij.le]) rfl
        have hq : q.IsPath := by rw [Walk.isPath_copy]; exact (hp.take j.val).drop i.val
        have hqlen : q.length = j.val - i.val := by
          rw [Walk.length_copy, Walk.drop_length, Walk.take_length]
          have hj : j.val ≤ p.length := Nat.lt_succ_iff.mp j.isLt
          omega
        have hq_eq : q = (Path.singleton hadj).val :=
          isTree_path_eq T hT hq (Path.singleton hadj).isPath
        have hlen1 : q.length = 1 := by rw [hq_eq]; rfl
        omega
      · exact False.elim (T.ne_of_adj hadj (by rw [hij]))
      · right
        let q : T.Walk (p.getVert j.val) (p.getVert i.val) :=
          ((p.take i.val).drop j.val).copy
            (by simp [Walk.take_getVert, Nat.min_eq_right hji.le]) rfl
        have hq : q.IsPath := by rw [Walk.isPath_copy]; exact (hp.take i.val).drop j.val
        have hqlen : q.length = i.val - j.val := by
          rw [Walk.length_copy, Walk.drop_length, Walk.take_length]
          have hi : i.val ≤ p.length := Nat.lt_succ_iff.mp i.isLt
          omega
        have hq_eq : q = (Path.singleton hadj.symm).val :=
          isTree_path_eq T hT hq (Path.singleton hadj.symm).isPath
        have hlen1 : q.length = 1 := by rw [hq_eq]; rfl
        omega
    · rintro (hij | hji)
      · have := p.adj_getVert_succ (by omega : i.val < p.length)
        simpa [hij] using this
      · have := p.adj_getVert_succ (by omega : j.val < p.length)
        simpa [hji] using this.symm
  exact ⟨(⟨e, @hrel⟩ : pathG (p.length + 1) ≃g T.induce (S : Set U)).symm⟩

private lemma length_walk_induce {U : Type*} (T : SimpleGraph U) (S : Set U) {a b : U}
    (p : T.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (Walk.map_induce p hp)
  rwa [Walk.length_map] at h

private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁) (φ.symm_apply_apply a₂))).trans
      (by rw [Nat.cast_le, Walk.length_copy, Walk.length_map])

private lemma iso_eccent_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a : A) : GB.eccent (φ a) = GA.eccent a := by
  simp only [SimpleGraph.eccent_def]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_edist_eq GA GB φ a (φ.symm b)]
    exact le_iSup (GA.edist a) (φ.symm b)
  · rw [iSup_le_iff]
    intro a'
    rw [← iso_edist_eq GA GB φ a a']
    exact le_iSup (GB.edist (φ a)) (φ a')

private lemma iso_diam_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) : GA.diam = GB.diam := by
  simp only [SimpleGraph.diam, SimpleGraph.ediam]
  congr 1
  apply le_antisymm
  · rw [iSup_le_iff]
    intro a
    rw [← iso_eccent_eq GA GB φ a]
    exact le_iSup GB.eccent (φ a)
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_eccent_eq GA GB φ (φ.symm b)]
    exact le_iSup GA.eccent (φ.symm b)

private lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [Finset.mem_insert, Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [SimpleGraph.mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_insert_of_notMem hmap_not, Finset.card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega

private lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]

private lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩

private lemma induce_compl_singleton_dist_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hT' : (T.induce {v}ᶜ).IsTree)
    (a b : ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hT'.connected.exists_path_of_dist a b
  let g : T.induce {v}ᶜ →g T := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom
  have hmap : (p.map g).IsPath := hp.map Subtype.val_injective
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) hmap
  rw [Walk.length_map, hplen] at hdist
  exact hdist

private lemma induce_compl_singleton_diam_le {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).diam ≤ T.diam := by
  have : Nonempty U := hT.connected.nonempty
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := (T.induce {v}ᶜ).exists_dist_eq_diam
  rw [← hab, induce_compl_singleton_dist_eq T hT hT']
  exact dist_le_diam (connected_iff_ediam_ne_top.mp hT.connected)

private lemma ne_center_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (c : U)
    (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) : v ≠ c := by
  rintro rfl
  obtain ⟨u, huv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg1
  have huc : u ≠ v := huv.ne.symm
  have hle : T.eccent u ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y
    rw [← (hT.connected u y).coe_dist_eq_edist]
    norm_cast
    by_cases hyv : y = v
    · subst hyv
      have hd : T.dist u y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm
      omega
    · obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist v y
      have hnp : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hyv)
      have hsnd : p.snd = u := huniq p.snd (p.adj_snd hnp)
      let p' : T.Walk u y := p.tail.copy hsnd rfl
      have hp' : p'.IsPath := (Walk.isPath_copy _ _ _).mpr hp.tail
      have hdist_u : T.dist u y = p'.length :=
        (isTree_dist_eq_length_of_isPath T hT p' hp').symm
      have hvy_le : T.dist v y ≤ r := by
        have h1 : (T.dist v y : ℕ∞) ≤ r := by
          rw [(hT.connected v y).coe_dist_eq_edist, ← hecc]
          exact SimpleGraph.edist_le_eccent
        exact Nat.cast_le.mp h1
      rw [hdist_u, Walk.length_copy, Walk.length_tail, hplen]
      omega
  have hlt := huniq_c u huc
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

private lemma center_induce_compl_of_good_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r)
    (c : U) (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) (hdiam' : (T.induce {v}ᶜ).diam = 2 * r) :
    ∃ hc : c ∈ ({v}ᶜ : Set U),
      (T.induce {v}ᶜ).eccent ⟨c, hc⟩ = r ∧
      ∀ z' : ({v}ᶜ : Set U), z' ≠ ⟨c, hc⟩ → (r : ℕ∞) < (T.induce {v}ᶜ).eccent z' := by
  have hc : c ∈ ({v}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr (ne_center_of_deg_one T hT hr c hecc huniq_c hdeg1).symm
  refine ⟨hc, ?_⟩
  let T' := T.induce ({v}ᶜ : Set U)
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  let c' : ({v}ᶜ : Set U) := ⟨c, hc⟩
  have hle_r : ∀ y' : ({v}ᶜ : Set U), T'.dist c' y' ≤ r := by
    intro y'
    rw [induce_compl_singleton_dist_eq T hT hT']
    have h1 : (T.dist c y'.1 : ℕ∞) ≤ r := by
      rw [(hT.connected c y'.1).coe_dist_eq_edist, ← hecc]
      exact SimpleGraph.edist_le_eccent
    exact Nat.cast_le.mp h1
  have hecc_le : T'.eccent c' ≤ r := by
    rw [SimpleGraph.eccent_le_iff]
    intro y'
    rw [← (hT'.connected c' y').coe_dist_eq_edist]
    exact Nat.cast_le.mpr (hle_r y')
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := T'.exists_dist_eq_diam
  rw [hdiam'] at hab
  have hda : T'.dist c' a = r := by
    have htri := hT'.connected.dist_triangle (u := a) (v := c') (w := b)
    rw [SimpleGraph.dist_comm (u := a) (v := c')] at htri
    have ha := hle_r a
    have hb := hle_r b
    omega
  have hecc_ge : (r : ℕ∞) ≤ T'.eccent c' := by
    rw [← hda, (hT'.connected c' a).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  have hecc_eq : T'.eccent c' = r := le_antisymm hecc_le hecc_ge
  obtain ⟨c₀, _, huniq₀⟩ := exists_unique_center_of_diam_eq_two_mul T' hT' hr hdiam'
  have hc₀ : c' = c₀ := by
    by_contra hne
    have hlt := huniq₀ c' hne
    rw [hecc_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  subst hc₀
  exact ⟨hecc_eq, huniq₀⟩

private lemma iso_map_center_of_good_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 1 ≤ r) (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    {v : V} {w : W} (hv1 : G.degree v = 1) (hw1 : H.degree w = 1)
    (hdiamG' : (G.induce {v}ᶜ).diam = 2 * r)
    (φ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ∃ (hcG : cG ∈ ({v}ᶜ : Set V)) (hcH : cH ∈ ({w}ᶜ : Set W)), φ ⟨cG, hcG⟩ = ⟨cH, hcH⟩ := by
  have hdiamH' : (H.induce {w}ᶜ).diam = 2 * r :=
    (iso_diam_eq _ _ φ).symm.trans hdiamG'
  obtain ⟨hcG, heccG', _⟩ := center_induce_compl_of_good_leaf G hTG hr cG heccG huG hv1 hdiamG'
  obtain ⟨hcH, _, huH'⟩ := center_induce_compl_of_good_leaf H hTH hr cH heccH huH hw1 hdiamH'
  refine ⟨hcG, hcH, ?_⟩
  by_contra hne
  have hlt := huH' (φ ⟨cG, hcG⟩) hne
  rw [iso_eccent_eq _ _ φ ⟨cG, hcG⟩, heccG'] at hlt
  exact absurd hlt (lt_irrefl _)

private lemma three_le_leaves_card {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (hU : 3 ≤ Fintype.card U) (hdeg : ∃ v₀ : U, 3 ≤ T.degree v₀) :
    3 ≤ (Finset.univ.filter fun v : U => T.degree v = 1).card := by
  obtain ⟨v₀, hv₀⟩ := hdeg
  have : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let L : Finset U := Finset.univ.filter fun v : U => T.degree v = 1
  have hv₀_not : v₀ ∉ L := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpos : ∀ v : U, 1 ≤ T.degree v := fun v => hT.preconnected.degree_pos_of_nontrivial v
  have hge2 : ∀ v ∈ Lᶜ, 2 ≤ T.degree v := by
    intro v hv
    simp only [L, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have := hpos v
    omega
  have hsum_deg : ∑ v : U, T.degree v = 2 * Fintype.card U - 2 := by
    rw [T.sum_degrees_eq_twice_card_edges]
    have := hT.card_edgeFinset
    omega
  have hsplit : (∑ v ∈ L, T.degree v) + ∑ v ∈ Lᶜ, T.degree v = ∑ v : U, T.degree v :=
    Finset.sum_add_sum_compl L (fun v => T.degree v)
  have hsum_L : ∑ v ∈ L, T.degree v = L.card := by
    calc
      ∑ v ∈ L, T.degree v = ∑ _v ∈ L, 1 := Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2
      _ = L.card := by simp
  have hv₀_mem : v₀ ∈ Lᶜ := Finset.mem_compl.mpr hv₀_not
  have hsum_Lc : 2 * Lᶜ.card + 1 ≤ ∑ v ∈ Lᶜ, T.degree v := by
    have h1 : ∑ v ∈ Lᶜ, T.degree v = T.degree v₀ + ∑ v ∈ Lᶜ.erase v₀, T.degree v :=
      (Finset.add_sum_erase Lᶜ (fun v => T.degree v) hv₀_mem).symm
    have h2 : ∑ v ∈ Lᶜ.erase v₀, 2 ≤ ∑ v ∈ Lᶜ.erase v₀, T.degree v :=
      Finset.sum_le_sum fun v hv => hge2 v (Finset.mem_of_mem_erase hv)
    have hcard_er : (Lᶜ.erase v₀).card + 1 = Lᶜ.card := by
      rw [Finset.card_erase_of_mem hv₀_mem]
      have : 0 < Lᶜ.card := Finset.card_pos.mpr ⟨v₀, hv₀_mem⟩
      omega
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hcard_compl : L.card + Lᶜ.card = Fintype.card U := by
    rw [Finset.card_compl]
    have : L.card ≤ Fintype.card U := Finset.card_le_univ L
    omega
  change 3 ≤ L.card
  omega

private lemma good_leaf_of_ne_diam_ends {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {r : ℕ} (_hr : 2 ≤ r) (hdiam : T.diam = 2 * r) {x0 xd : U} (hxd : T.dist x0 xd = 2 * r)
    {v : U} (hv1 : T.degree v = 1) (hx0 : v ≠ x0) (hxd_ne : v ≠ xd) :
    (T.induce {v}ᶜ).diam = 2 * r := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hnot : v ∉ p.support := by
    intro hv_mem
    obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hv_mem
    have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hx0.symm
    have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hxd_ne
    have hadj1 : T.Adj v q.penultimate := (q.adj_penultimate hq_nn).symm
    have hadj2 : T.Adj v s.snd := s.adj_snd hs_nn
    have hne12 : q.penultimate ≠ s.snd := by
      have hdisj : q.support.Disjoint s.tail.support := by
        have h1 := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
        exact h1.2.2
      have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
      have hm2 : s.snd ∈ s.tail.support := by
        rw [Walk.support_tail_of_not_nil s hs_nn]
        exact s.snd_mem_tail_support hs_nn
      intro heq
      rw [heq] at hm1
      exact hdisj hm1 hm2
    have h2 : 2 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset v := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [SimpleGraph.mem_neighborFinset]
        rcases hz with rfl | rfl <;> assumption
      calc
        2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
        _ ≤ (T.neighborFinset v).card := Finset.card_le_card hsub
    omega
  have hw_supp : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set U) := fun x hx =>
    Set.mem_compl_singleton_iff.mpr fun heq => hnot (heq ▸ hx)
  let p' := p.induce ({v}ᶜ : Set U) hw_supp
  have hp' : p'.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({v}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  have hdist : (T.induce {v}ᶜ).dist ⟨x0, hw_supp x0 p.start_mem_support⟩
      ⟨xd, hw_supp xd p.end_mem_support⟩ = 2 * r := by
    have h1 := isTree_dist_eq_length_of_isPath (T.induce {v}ᶜ) hT' p' hp'
    rw [← h1, length_walk_induce, hplen, hxd]
  have hediam' : (T.induce {v}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
  have hge : 2 * r ≤ (T.induce {v}ᶜ).diam := hdist ▸ dist_le_diam hediam'
  have hle : (T.induce {v}ᶜ).diam ≤ 2 * r := hdiam ▸ induce_compl_singleton_diam_le T hT hv1
  omega

private lemma exists_good_leaf {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (hU : 3 ≤ Fintype.card U) (hdeg : ∃ v₀ : U, 3 ≤ T.degree v₀)
    {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ v : U, T.degree v = 1 ∧ (T.induce {v}ᶜ).diam = 2 * r := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  have hxd_r : T.dist x0 xd = 2 * r := hxd.trans hdiam
  let L : Finset U := Finset.univ.filter fun v : U => T.degree v = 1
  have hL3 : 3 ≤ L.card := three_le_leaves_card T hT hU hdeg
  have hdiff : 0 < (L \ {x0, xd}).card := by
    have hsub : L ⊆ (L \ {x0, xd}) ∪ {x0, xd} := fun z hz => by
      by_cases hzm : z ∈ ({x0, xd} : Finset U)
      · exact Finset.mem_union_right _ hzm
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hzm⟩)
    have hcard2 : ({x0, xd} : Finset U).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hdiff
  simp only [L, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact ⟨v, hv.1, good_leaf_of_ne_diam_ends T hT hr hdiam hxd_r hv.1 hv.2.1 hv.2.2⟩

private lemma iso_of_deg_center_eq_and_leaf_adj {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hTG : G.IsTree) (hTH : H.IsTree)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r)
    (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hdegc : G.degree cG = H.degree cH)
    {v : V} (hadj : G.Adj cG v) (hv1 : G.degree v = 1)
    (hσv : Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)) :
    Nonempty (G ≃g H) := by
  have : Nonempty V := hTG.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := G.exists_dist_eq_diam
  have hxd_r : G.dist x0 xd = 2 * r := hxd.trans hdiamG
  have hdist_c_x0 : G.dist cG x0 = r := by
    have htri := hTG.connected.dist_triangle (u := x0) (v := cG) (w := xd)
    have h1 : G.dist cG x0 ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG x0).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    have h2 : G.dist cG xd ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG xd).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    rw [SimpleGraph.dist_comm (u := x0) (v := cG)] at htri
    omega
  have hdist_c_xd : G.dist cG xd = r := by
    have htri := hTG.connected.dist_triangle (u := x0) (v := cG) (w := xd)
    have h2 : G.dist cG xd ≤ r := Nat.cast_le.mp (by
      rw [(hTG.connected cG xd).coe_dist_eq_edist, ← heccG]
      exact SimpleGraph.edist_le_eccent)
    rw [SimpleGraph.dist_comm (u := x0) (v := cG)] at htri
    omega
  have hdist_c_v : G.dist cG v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have hv_x0 : v ≠ x0 := fun h => by rw [h, hdist_c_x0] at hdist_c_v; omega
  have hv_xd : v ≠ xd := fun h => by rw [h, hdist_c_xd] at hdist_c_v; omega
  have hdiamG' : (G.induce {v}ᶜ).diam = 2 * r :=
    good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hv1 hv_x0 hv_xd
  have hw1 : H.degree (σ v) = 1 := by
    rw [← ncard_neighborSet_eq_degree, ← hdeg v, ncard_neighborSet_eq_degree, hv1]
  obtain ⟨φ⟩ := hσv
  obtain ⟨hcG, hcH, hφc⟩ :=
    iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH heccG huG heccH huH hv1 hw1 hdiamG' φ
  have hdeg_ind : (G.induce {v}ᶜ).degree ⟨cG, hcG⟩ = (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ := by
    rw [← hφc]
    exact (φ.degree_eq ⟨cG, hcG⟩).symm
  have hdeg_cG_ind := degree_induce_compl_singleton_of_adj G hcG hadj
  have hadjH : H.Adj cH (σ v) := by
    by_contra hnadj
    rw [degree_induce_compl_singleton_of_not_adj H hcH hnadj] at hdeg_ind
    have hG_pos : 0 < G.degree cG := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨v, (G.mem_neighborFinset cG v).mpr hadj⟩
    omega
  have huniqG := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv1)
  have huniqH := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw1)
  have hv_only : ∀ x : V, G.Adj v x ↔ x = cG := by
    intro x
    constructor
    · intro h
      obtain ⟨u, hu, hu_uniq⟩ := huniqG
      have h1 : cG = u := hu_uniq cG hadj.symm
      have h2 : x = u := hu_uniq x h
      exact h2.trans h1.symm
    · rintro rfl
      exact hadj.symm
  have hw_only : ∀ y : W, H.Adj (σ v) y ↔ y = cH := by
    intro y
    constructor
    · intro h
      obtain ⟨u, hu, hu_uniq⟩ := huniqH
      have h1 : cH = u := hu_uniq cH hadjH.symm
      have h2 : y = u := hu_uniq y h
      exact h2.trans h1.symm
    · rintro rfl
      exact hadjH.symm
  let toF : V → W := fun x => if hx : x ∈ ({v}ᶜ : Set V) then (φ ⟨x, hx⟩).1 else σ v
  let invF : W → V := fun y => if hy : y ∈ ({σ v}ᶜ : Set W) then (φ.symm ⟨y, hy⟩).1 else v
  have hleft : Function.LeftInverse invF toF := by
    intro x
    dsimp only [toF, invF]
    by_cases hx : x ∈ ({v}ᶜ : Set V)
    · rw [dif_pos hx]
      have hne : (φ ⟨x, hx⟩).1 ∈ ({σ v}ᶜ : Set W) := (φ ⟨x, hx⟩).2
      rw [dif_pos hne, Subtype.coe_eta]
      exact congrArg Subtype.val (φ.left_inv ⟨x, hx⟩)
    · rw [dif_neg hx]
      have hnv : σ v ∉ ({σ v}ᶜ : Set W) := fun h => h rfl
      rw [dif_neg hnv]
      exact (not_not.mp (mt Set.mem_compl_singleton_iff.mpr hx)).symm
  have hright : Function.RightInverse invF toF := by
    intro y
    dsimp only [toF, invF]
    by_cases hy : y ∈ ({σ v}ᶜ : Set W)
    · rw [dif_pos hy]
      have hne : (φ.symm ⟨y, hy⟩).1 ∈ ({v}ᶜ : Set V) := (φ.symm ⟨y, hy⟩).2
      rw [dif_pos hne, Subtype.coe_eta]
      exact congrArg Subtype.val (φ.right_inv ⟨y, hy⟩)
    · rw [dif_neg hy]
      have hnv : v ∉ ({v}ᶜ : Set V) := fun h => h rfl
      rw [dif_neg hnv]
      exact (not_not.mp (mt Set.mem_compl_singleton_iff.mpr hy)).symm
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro a b
  dsimp only [Equiv.coe_fn_mk, toF]
  by_cases ha : a = v <;> by_cases hb : b = v
  · have ha' : a ∉ ({v}ᶜ : Set V) := fun h => h ha
    have hb' : b ∉ ({v}ᶜ : Set V) := fun h => h hb
    rw [dif_neg ha', dif_neg hb', ha, hb]
    simp
  · have ha' : a ∉ ({v}ᶜ : Set V) := fun h => h ha
    have hb' : b ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr hb
    rw [dif_neg ha', dif_pos hb', ha, hw_only (φ ⟨b, hb'⟩).1, hv_only b]
    constructor
    · intro hval
      exact congrArg Subtype.val (φ.injective ((Subtype.ext hval : φ ⟨b, hb'⟩ = ⟨cH, hcH⟩).trans hφc.symm))
    · rintro rfl
      exact congrArg Subtype.val hφc
  · have ha' : a ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr ha
    have hb' : b ∉ ({v}ᶜ : Set V) := fun h => h hb
    rw [dif_pos ha', dif_neg hb', hb, H.adj_comm, G.adj_comm, hw_only (φ ⟨a, ha'⟩).1, hv_only a]
    constructor
    · intro hval
      exact congrArg Subtype.val (φ.injective ((Subtype.ext hval : φ ⟨a, ha'⟩ = ⟨cH, hcH⟩).trans hφc.symm))
    · rintro rfl
      exact congrArg Subtype.val hφc
  · have ha' : a ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr ha
    have hb' : b ∈ ({v}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr hb
    rw [dif_pos ha', dif_pos hb']
    exact φ.map_rel_iff (a := ⟨a, ha'⟩) (b := ⟨b, hb'⟩)

private lemma existsUnique_root_of_component {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃! u : ({c}ᶜ : Set U), u ∈ C.supp ∧ T.Adj c u.1 := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  have hzc : z.1 ≠ c := z.2
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist c z.1
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne hzc.symm
  let uVal : U := p.snd
  have hadj : T.Adj c uVal := p.adj_snd hnp
  have huc : uVal ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
  let u : ({c}ᶜ : Set U) := ⟨uVal, huc⟩
  have hsupp_tail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set U) := by
    intro x hx
    rw [Walk.support_tail_of_not_nil p hnp] at hx
    exact Set.mem_compl_singleton_iff.mpr fun hxc =>
      start_notMem_tail_support_of_isPath hp (hxc ▸ hx)
  let p' : (T.induce {c}ᶜ).Walk u z :=
    (p.tail.induce ({c}ᶜ : Set U) hsupp_tail).copy rfl (Subtype.ext rfl)
  have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨p'⟩
  have hu_mem : u ∈ C.supp := by
    rw [ConnectedComponent.mem_supp_iff] at hz ⊢
    exact (ConnectedComponent.sound hreach).trans hz
  refine ⟨u, ⟨hu_mem, hadj⟩, fun u' ⟨hu'_mem, hadj'⟩ => ?_⟩
  by_contra hne
  have hne_val : uVal ≠ u'.1 := fun h => hne (Subtype.ext h).symm
  obtain ⟨q⟩ := C.reachable_of_mem_supp hu_mem hu'_mem
  let q_path := q.toPath
  let g : T.induce {c}ᶜ →g T := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom
  have hqG : (q_path.val.map g).IsPath := q_path.isPath.map Subtype.val_injective
  have hc_not_q : c ∉ (q_path.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hxc⟩
    exact x.2 hxc
  let two_step : T.Walk uVal u'.1 := Walk.cons hadj.symm (Walk.cons hadj' Walk.nil)
  have htwo_path : two_step.IsPath := by
    simp [two_step, Walk.cons_isPath_iff, hne_val, hadj.ne.symm, hadj'.ne]
  have heq := isTree_path_eq T hT hqG htwo_path
  have hc_in : c ∈ two_step.support := by simp [two_step]
  rw [← heq] at hc_in
  exact hc_not_q hc_in

private lemma component_toSimpleGraph_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = (T.induce {c}ᶜ).degree x.1 := by
  let f : C.supp ↪ ({c}ᶜ : Set U) := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : (C.toSimpleGraph.neighborFinset x).map f = (T.induce {c}ᶜ).neighborFinset x.1 := by
    ext y
    rw [Finset.mem_map, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hz
      exact hz
    · intro hxy
      have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact hxy
  have hcard := congrArg Finset.card heq
  rw [Finset.card_map, C.toSimpleGraph.card_neighborFinset_eq_degree,
    (T.induce {c}ᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard

private lemma component_degree_sum {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∑ x : C.supp, T.degree x.1.1 = 2 * Fintype.card C.supp - 1 := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have hdeg_eq : ∀ x : C.supp,
      T.degree x.1.1 = C.toSimpleGraph.degree x + (if x = uC then 1 else 0) := by
    intro x
    rw [component_toSimpleGraph_degree T c C x]
    split_ifs with hxu
    · subst hxu
      exact (degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm).symm
    · have hnadj : ¬ T.Adj x.1.1 c := by
        intro hadj
        have hxeq : x.1 = u := hu_uniq x.1 ⟨x.2, hadj.symm⟩
        exact hxu (Subtype.ext hxeq)
      exact (degree_induce_compl_singleton_of_not_adj T x.1.2 hnadj).symm
  have hsum : ∑ x : C.supp, T.degree x.1.1 =
      (∑ x : C.supp, C.toSimpleGraph.degree x) + ∑ x : C.supp, (if x = uC then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hdeg_eq x
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hdeg_sum : (∑ x : C.supp, C.toSimpleGraph.degree x) = 2 * C.toSimpleGraph.edgeFinset.card := by
    convert C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    all_goals exact Iff.rfl
  rw [hdeg_sum] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  have hC_edges : C.toSimpleGraph.edgeFinset.card + 1 = Fintype.card C.supp := by
    convert hC_tree.card_edgeFinset
    all_goals exact Iff.rfl
  have hC_pos : 1 ≤ Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨uC⟩
  omega

private lemma component_leaves_formula {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    let LC := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
    LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) ∧
      ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
  have hT_pos : ∀ v : U, 1 ≤ T.degree v := by
    intro v
    obtain ⟨w, _⟩ := C.nonempty_supp
    have hwc : c ≠ w.1 := fun h => w.2 (h.symm)
    have : Nontrivial U := ⟨⟨c, w.1, hwc⟩⟩
    exact hT.preconnected.degree_pos_of_nontrivial v
  let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hge2 : ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
    intro x hx
    simp only [LC, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have := hT_pos x.1.1
    omega
  have hsum := component_degree_sum T hT c C
  have hsplit : (∑ x ∈ LC, T.degree x.1.1) + ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x : C.supp, T.degree x.1.1 :=
    Finset.sum_add_sum_compl LC (fun x => T.degree x.1.1)
  have hsum_L : ∑ x ∈ LC, T.degree x.1.1 = LC.card := by
    calc
      ∑ x ∈ LC, T.degree x.1.1 = ∑ _x ∈ LC, 1 := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
      _ = LC.card := by simp
  have hsum_Lc : ∑ x ∈ LCᶜ, T.degree x.1.1 = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by
    calc
      ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x ∈ LCᶜ, (2 + (T.degree x.1.1 - 2)) :=
        Finset.sum_congr rfl fun x hx => by have := hge2 x hx; omega
      _ = (∑ _x ∈ LCᶜ, 2) + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := Finset.sum_add_distrib
      _ = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by simp [mul_comm]
  have hcard_compl : LC.card + LCᶜ.card = Fintype.card C.supp := by
    rw [Finset.card_compl]
    have : LC.card ≤ Fintype.card C.supp := Finset.card_le_univ LC
    omega
  have hC_pos : 1 ≤ Fintype.card C.supp := by
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  refine ⟨?_, hge2⟩
  change LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2)
  omega

private lemma mem_support_tail_of_ne {U : Type} {T : SimpleGraph U}
    {a b x : U} (w : T.Walk a b) (hx : x ∈ w.support) (hne : x ≠ a) : x ∈ w.support.tail := by
  cases w with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hne
  | cons _ _ =>
    simpa [Walk.support_cons] using Or.resolve_left (List.mem_cons.mp hx) hne

private lemma diam_path_contains_center {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (c : U) (hecc : T.eccent c = r)
    {x0 xd : U} (p : T.Walk x0 xd) (hp : p.IsPath) (hplen : p.length = 2 * r) :
    c ∈ p.support ∧ T.dist c x0 = r ∧ T.dist c xd = r := by
  obtain ⟨q1, hq1, hq1len⟩ := hT.connected.exists_path_of_dist x0 c
  obtain ⟨q2, hq2, hq2len⟩ := hT.connected.exists_path_of_dist c xd
  have h1 : T.dist x0 c ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected x0 c).coe_dist_eq_edist, SimpleGraph.edist_comm, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have h2 : T.dist c xd ≤ r := Nat.cast_le.mp (by
    rw [(hT.connected c xd).coe_dist_eq_edist, ← hecc]
    exact SimpleGraph.edist_le_eccent)
  have hpdist : p.length = T.dist x0 xd := isTree_dist_eq_length_of_isPath T hT p hp
  have htri := hT.connected.dist_triangle (u := x0) (v := c) (w := xd)
  have h1eq : T.dist x0 c = r := by omega
  have h2eq : T.dist c xd = r := by omega
  have hq12_len : (q1.append q2).length = T.dist x0 xd := by
    rw [Walk.length_append, hq1len, hq2len, h1eq, h2eq, ← hpdist, hplen]
    omega
  have hq12_path : (q1.append q2).IsPath :=
    (q1.append q2).isPath_of_length_eq_dist hq12_len
  have heq : q1.append q2 = p := isTree_path_eq T hT hq12_path hp
  have hc_mem : c ∈ p.support := by
    rw [← heq, Walk.mem_support_append_iff]
    exact Or.inl q1.end_mem_support
  rw [SimpleGraph.dist_comm] at h1eq
  exact ⟨hc_mem, h1eq, h2eq⟩

private lemma deg_center_ge_two {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r)
    (hdiam : T.diam = 2 * r) (c : U) (hecc : T.eccent c = r) :
    2 ≤ T.degree c := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  obtain ⟨hc_mem, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp hplen_r
  obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hc_mem
  have hcx0_ne : c ≠ x0 := fun h => by rw [h, SimpleGraph.dist_self] at hcx0; omega
  have hcxd_ne : c ≠ xd := fun h => by rw [h, SimpleGraph.dist_self] at hcxd; omega
  have hq_nn : ¬ q.Nil := Walk.not_nil_of_ne hcx0_ne.symm
  have hs_nn : ¬ s.Nil := Walk.not_nil_of_ne hcxd_ne
  have hadj1 : T.Adj c q.penultimate := (q.adj_penultimate hq_nn).symm
  have hadj2 : T.Adj c s.snd := s.adj_snd hs_nn
  have hne12 : q.penultimate ≠ s.snd := by
    have hdisj : q.support.Disjoint s.tail.support := by
      have h1 := (hp_eq ▸ hp).support_nodup
      rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil s hs_nn] at h1
      exact h1.2.2
    have hm1 : q.penultimate ∈ q.support := Walk.getVert_mem_support q (q.length - 1)
    have hm2 : s.snd ∈ s.tail.support := by
      rw [Walk.support_tail_of_not_nil s hs_nn]
      exact s.snd_mem_tail_support hs_nn
    intro heq
    rw [heq] at hm1
    exact hdisj hm1 hm2
  rw [← T.card_neighborFinset_eq_degree]
  have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset c := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl <;> assumption
  calc
    2 = ({q.penultimate, s.snd} : Finset U).card := (Finset.card_pair hne12).symm
    _ ≤ (T.neighborFinset c).card := Finset.card_le_card hsub

private lemma card_component_eq_radius_of_unique_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent)
    {x_end : ({c}ᶜ : Set U)} (hx_mem : x_end ∈ C.supp)
    (hx_dist : T.dist c x_end.1 = r)
    (h_all_le2 : ∀ x : C.supp, T.degree x.1.1 ≤ 2)
    (h_uniq_leaf : ∀ x : C.supp, T.degree x.1.1 = 1 → x.1 = x_end) :
    Fintype.card C.supp = r := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  let xC : C.supp := ⟨x_end, hx_mem⟩
  have hux_ne : uC ≠ xC := by
    intro h
    have hval : u.1 = x_end.1 := congrArg (fun y : C.supp => y.1.1) h
    have hd : T.dist c u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
    rw [hval, hx_dist] at hd
    omega
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x_end.1
  have hp_len : p.length = r := hplen.trans hx_dist
  have hnp : ¬ p.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hx_dist; omega)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [Walk.support_tail_of_not_nil p hnp] at hy
    exact Set.mem_compl_singleton_iff.mpr fun hyc =>
      start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  have hsnd : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) = u := by
    have hreach : (T.induce {c}ᶜ).Reachable ⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ x_end :=
      ⟨(p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy rfl (Subtype.ext rfl)⟩
    have hsnd_mem : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) ∈ C.supp := by
      rw [ConnectedComponent.mem_supp_iff] at hx_mem ⊢
      exact (ConnectedComponent.sound hreach).trans hx_mem
    exact hu_uniq ⟨p.snd, _⟩ ⟨hsnd_mem, p.adj_snd hnp⟩
  let p' : (T.induce {c}ᶜ).Walk u x_end :=
    (p.tail.induce ({c}ᶜ : Set U) p_tail_supp).copy hsnd (Subtype.ext rfl)
  have hp' : p'.IsPath := by
    rw [Walk.isPath_copy]
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({c}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp.tail
  have hp'_len : p'.length = r - 1 := by
    rw [Walk.length_copy, length_walk_induce, Walk.length_tail, hp_len]
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hp'_mem_C : ∀ z ∈ p'.support, z ∈ C.supp := by
    intro z hz
    obtain ⟨q1, _, _, _, _⟩ := hp'.mem_support_iff_exists_append.mp hz
    have hreach : (T.induce {c}ᶜ).Reachable u z := ⟨q1⟩
    rw [ConnectedComponent.mem_supp_iff] at hu_mem ⊢
    exact (ConnectedComponent.sound hreach).symm.trans hu_mem
  let pC_ind : ((T.induce {c}ᶜ).induce C.supp).Walk uC xC := p'.induce C.supp hp'_mem_C
  have hpC_ind : pC_ind.IsPath := by
    refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce C.supp).toHom) ?_
    rw [Walk.map_induce]
    exact hp'
  have hpC_ind_len : pC_ind.length = r - 1 :=
    (length_walk_induce (T.induce {c}ᶜ) C.supp p' hp'_mem_C).trans hp'_len
  let pC : C.toSimpleGraph.Walk uC xC := pC_ind
  have hpC : pC.IsPath := hpC_ind
  have hpC_len : pC.length = r - 1 := hpC_ind_len
  have hdeg_uC : C.toSimpleGraph.degree uC = 1 := by
    rw [component_toSimpleGraph_degree T c C uC]
    dsimp only [uC]
    have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
    rw [Subtype.coe_eta] at h1
    have hge1 : 1 ≤ (T.induce {c}ᶜ).degree u := by
      rw [← component_toSimpleGraph_degree T c C uC]
      have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
      exact hC_tree.preconnected.degree_pos_of_nontrivial uC
    have hle2 : T.degree u.1 ≤ 2 := h_all_le2 uC
    omega
  have hdeg_xC : C.toSimpleGraph.degree xC = 1 := by
    rw [component_toSimpleGraph_degree T c C xC]
    have hx_nadj : ¬ T.Adj x_end.1 c := by
      intro hadj
      have hd : T.dist c x_end.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      rw [hx_dist] at hd
      omega
    rw [degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj]
    have : Nontrivial C.supp := ⟨⟨uC, xC, hux_ne⟩⟩
    have hge1 : 1 ≤ T.degree x_end.1 := by
      rw [← degree_induce_compl_singleton_of_not_adj T x_end.2 hx_nadj,
        ← component_toSimpleGraph_degree T c C xC]
      exact hC_tree.preconnected.degree_pos_of_nontrivial xC
    have hle1 : ¬ 2 ≤ T.degree x_end.1 := by
      intro h2
      obtain ⟨hLC_eq, _⟩ := component_leaves_formula T hT c C
      let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => T.degree x.1.1 = 1
      have hpos : 0 < LC.card := by dsimp [LC] at hLC_eq ⊢; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hwx : w.1 = x_end := h_uniq_leaf w hw
      rw [hwx] at hw
      omega
    omega
  have hdeg_int : ∀ y : C.supp, y ≠ uC → y ≠ xC → C.toSimpleGraph.degree y ≤ 2 := by
    intro y _ _
    rw [component_toSimpleGraph_degree T c C y]
    exact (degree_induce_compl_le T y.1.2).trans (h_all_le2 y)
  have hsupp_eq : ∀ y : C.supp, y ∈ pC.support := by
    intro y
    by_contra hy
    obtain ⟨q, hq, _⟩ := hC_tree.connected.exists_path_of_dist y uC
    obtain ⟨z, q₁, _, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem C.toSimpleGraph {w | w ∈ pC.support} q pC.start_mem_support
    have hq1_nn : ¬ q₁.Nil := Walk.not_nil_of_ne (fun h => hy (h ▸ hz_mem))
    have hadj_z : C.toSimpleGraph.Adj z q₁.penultimate := (q₁.adj_penultimate hq1_nn).symm
    have hpen_not : q₁.penultimate ∉ pC.support := by
      intro hm
      have hmem1 : q₁.penultimate ∈ q₁.support := Walk.getVert_mem_support q₁ (q₁.length - 1)
      have heq : q₁.penultimate = z := hq_first q₁.penultimate hmem1 hm
      exact C.toSimpleGraph.ne_of_adj hadj_z heq.symm
    by_cases hzu : z = uC
    · subst hzu
      have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
      have hadj_p : C.toSimpleGraph.Adj uC pC.snd := pC.adj_snd hpC_nn
      have hsnd_mem : pC.snd ∈ pC.support := List.mem_of_mem_tail (pC.snd_mem_tail_support hpC_nn)
      have hne : pC.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hsnd_mem)
      have h2 : 2 ≤ C.toSimpleGraph.degree uC := by
        rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
        have hsub : {pC.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset uC := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rw [SimpleGraph.mem_neighborFinset]
          rcases ha with rfl | rfl <;> assumption
        calc
          2 = ({pC.snd, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
          _ ≤ (C.toSimpleGraph.neighborFinset uC).card := Finset.card_le_card hsub
      omega
    · by_cases hzx : z = xC
      · subst hzx
        have hpC_nn : ¬ pC.Nil := Walk.not_nil_of_ne hux_ne
        have hadj_p : C.toSimpleGraph.Adj xC pC.penultimate := (pC.adj_penultimate hpC_nn).symm
        have hpen_p_mem : pC.penultimate ∈ pC.support := Walk.getVert_mem_support pC (pC.length - 1)
        have hne : pC.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hpen_p_mem)
        have h2 : 2 ≤ C.toSimpleGraph.degree xC := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {pC.penultimate, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset xC := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rw [SimpleGraph.mem_neighborFinset]
            rcases ha with rfl | rfl <;> assumption
          calc
            2 = ({pC.penultimate, q₁.penultimate} : Finset C.supp).card := (Finset.card_pair hne).symm
            _ ≤ (C.toSimpleGraph.neighborFinset xC).card := Finset.card_le_card hsub
        omega
      · obtain ⟨a, b, ha, hb, hpC_eq⟩ := hpC.mem_support_iff_exists_append.mp hz_mem
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne (fun h => hzu h.symm)
        have hb_nn : ¬ b.Nil := Walk.not_nil_of_ne hzx
        have hadj1 : C.toSimpleGraph.Adj z a.penultimate := (a.adj_penultimate ha_nn).symm
        have hadj2 : C.toSimpleGraph.Adj z b.snd := b.adj_snd hb_nn
        have ha_pen_mem : a.penultimate ∈ a.support := Walk.getVert_mem_support a (a.length - 1)
        have hm1 : a.penultimate ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_left a b ha_pen_mem
        have hm2 : b.snd ∈ pC.support := hpC_eq ▸ Walk.support_subset_support_append_right a b (List.mem_of_mem_tail (b.snd_mem_tail_support hb_nn))
        have hne12 : a.penultimate ≠ b.snd := by
          have hdisj : a.support.Disjoint b.tail.support := by
            have h1 := (hpC_eq ▸ hpC).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil b hb_nn] at h1
            exact h1.2.2
          have hb_snd : b.snd ∈ b.tail.support := by
            rw [Walk.support_tail_of_not_nil b hb_nn]
            exact b.snd_mem_tail_support hb_nn
          intro heq
          rw [heq] at ha_pen_mem
          exact hdisj ha_pen_mem hb_snd
        have hne13 : a.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm1)
        have hne23 : b.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm2)
        have h3 : 3 ≤ C.toSimpleGraph.degree z := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {a.penultimate, b.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset z := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rw [SimpleGraph.mem_neighborFinset]
            rcases hw with rfl | rfl | rfl <;> assumption
          have hc3 : ({a.penultimate, b.snd, q₁.penultimate} : Finset C.supp).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hne23]
            simp [hne12, hne13]
          exact hc3 ▸ Finset.card_le_card hsub
        have := hdeg_int z hzu hzx
        omega
  have hsupp_ind : ∀ y : C.supp, y ∈ pC_ind.support := hsupp_eq
  have hcard_eq : Fintype.card C.supp = pC_ind.support.toFinset.card := by
    have huniv : pC_ind.support.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun y => List.mem_toFinset.mpr (hsupp_ind y)
    rw [huniv, Finset.card_univ]
  rw [hcard_eq, List.toFinset_card_of_nodup hpC_ind.support_nodup, pC_ind.length_support, hpC_ind_len]
  omega

private lemma card_connectedComponent_eq_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) :
    Fintype.card (T.induce {c}ᶜ).ConnectedComponent = T.degree c := by
  let f : (T.induce {c}ᶜ).ConnectedComponent → T.neighborFinset c := fun C =>
    let u := (existsUnique_root_of_component T hT c C).choose
    ⟨u.1, (T.mem_neighborFinset c u.1).mpr (existsUnique_root_of_component T hT c C).choose_spec.1.2⟩
  let g : T.neighborFinset c → (T.induce {c}ᶜ).ConnectedComponent := fun u =>
    (T.induce {c}ᶜ).connectedComponentMk ⟨u.1, Set.mem_compl_singleton_iff.mpr ((T.mem_neighborFinset c u.1).mp u.2).ne.symm⟩
  have hleft : Function.LeftInverse g f := by
    intro C
    dsimp only [f, g]
    have hu := (existsUnique_root_of_component T hT c C).choose_spec.1.1
    exact (ConnectedComponent.mem_supp_iff C _).mp hu
  have hright : Function.RightInverse g f := by
    intro u
    dsimp only [f, g]
    apply Subtype.ext
    have hadj : T.Adj c u.1 := (T.mem_neighborFinset c u.1).mp u.2
    have huc : u.1 ∈ ({c}ᶜ : Set U) := Set.mem_compl_singleton_iff.mpr hadj.ne.symm
    let u_sub : ({c}ᶜ : Set U) := ⟨u.1, huc⟩
    let C := (T.induce {c}ᶜ).connectedComponentMk u_sub
    have hu_mem : u_sub ∈ C.supp := rfl
    have h_eq := ((existsUnique_root_of_component T hT c C).choose_spec.2 u_sub ⟨hu_mem, hadj⟩).symm
    exact congrArg (fun z : ({c}ᶜ : Set U) => z.1) h_eq
  rw [Fintype.card_congr ⟨f, g, hleft, hright⟩, Fintype.card_coe, T.card_neighborFinset_eq_degree]

private lemma sum_card_connectedComponent_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) :
    (∑ C : (T.induce {c}ᶜ).ConnectedComponent, Fintype.card C.supp) + 1 = Fintype.card U := by
  have h1 : (∑ C : (T.induce {c}ᶜ).ConnectedComponent, Fintype.card C.supp) =
      Fintype.card ({c}ᶜ : Set U) := by
    rw [← Fintype.card_sigma]
    refine Fintype.card_congr
      ⟨fun ⟨_, ⟨x, _⟩⟩ => x, fun (x : ({c}ᶜ : Set U)) => ⟨(T.induce {c}ᶜ).connectedComponentMk x, ⟨x, rfl⟩⟩, ?_, ?_⟩
    · rintro ⟨C, ⟨x, hx⟩⟩
      have hCx : (T.induce {c}ᶜ).connectedComponentMk x = C := (ConnectedComponent.mem_supp_iff C x).mp hx
      subst hCx
      rfl
    · intro x
      rfl
  have h2 : Fintype.card ({c}ᶜ : Set U) + 1 = Fintype.card U := by
    have e : ({c}ᶜ : Set U) ≃ ↥(Finset.univ.erase c) :=
      ⟨fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩,
       fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
       fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ c),
      Finset.card_univ]
    have : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨c⟩
    omega
  omega

private lemma degree_pathG_le_two (n : ℕ) (i : Fin n) : (pathG n).degree i ≤ 2 := by
  rw [← (pathG n).card_neighborFinset_eq_degree]
  have hsub : (pathG n).neighborFinset i ⊆
      (if h1 : i.val + 1 < n then {⟨i.val + 1, h1⟩} else ∅) ∪
      (if h2 : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅) := by
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    rcases hj with h | h
    · refine Finset.mem_union_left _ ?_
      have hj1 : i.val + 1 < n := by rw [h]; exact j.isLt
      rw [dif_pos hj1, Finset.mem_singleton]
      exact Fin.ext h.symm
    · refine Finset.mem_union_right _ ?_
      have hj2 : 0 < i.val := by omega
      rw [dif_pos hj2, Finset.mem_singleton]
      exact Fin.ext (by simp; omega)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  split_ifs <;> simp

private lemma card_edgeFinset_pathG (n : ℕ) (hn : 1 ≤ n) :
    (pathG n).edgeFinset.card + 1 = n := by
  have hconn : (pathG n).Connected := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine Connected.mk fun i j => ?_
    suffices h0 : ∀ k : Fin n, (pathG n).Reachable ⟨0, hn⟩ k from
      (h0 i).symm.trans (h0 j)
    intro ⟨k, hk⟩
    induction k with
    | zero => exact Reachable.rfl
    | succ k ih =>
      have hk' : k < n := by omega
      have hadj : (pathG n).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := Or.inl rfl
      exact (ih hk').trans hadj.reachable
  have hacyc : (pathG n).IsAcyclic := by
    intro u c hc
    have hne : c.support.toFinset.Nonempty := ⟨u, List.mem_toFinset.mpr c.start_mem_support⟩
    let m := c.support.toFinset.max' hne
    have hm_mem : m ∈ c.support := List.mem_toFinset.mp (Finset.max'_mem _ hne)
    let c' := c.rotate m hm_mem
    have hc' : c'.IsCycle := hc.rotate hm_mem
    have hperm := (c.support_rotate m hm_mem).perm
    have hadj1 : (pathG n).Adj m c'.snd := c'.adj_snd hc'.not_nil
    have hadj2 : (pathG n).Adj m c'.penultimate := (c'.adj_penultimate hc'.not_nil).symm
    have hsnd_tail : c'.snd ∈ c'.support.tail := c'.snd_mem_tail_support hc'.not_nil
    have hsnd_mem : c'.snd ∈ c.support := List.mem_of_mem_tail (hperm.subset hsnd_tail)
    have hpen_ne : c'.penultimate ≠ m := hadj2.ne.symm
    have hpen_tail : c'.penultimate ∈ c'.support.tail :=
      mem_support_tail_of_ne c' (Walk.getVert_mem_support c' (c'.length - 1)) hpen_ne
    have hpen_mem : c'.penultimate ∈ c.support := List.mem_of_mem_tail (hperm.subset hpen_tail)
    have hsnd_le : c'.snd.val ≤ m.val :=
      Finset.le_max' c.support.toFinset c'.snd (List.mem_toFinset.mpr hsnd_mem)
    have hpen_le : c'.penultimate.val ≤ m.val :=
      Finset.le_max' c.support.toFinset c'.penultimate (List.mem_toFinset.mpr hpen_mem)
    have h1 : m.val + 1 = c'.snd.val ∨ c'.snd.val + 1 = m.val := hadj1
    have h2 : m.val + 1 = c'.penultimate.val ∨ c'.penultimate.val + 1 = m.val := hadj2
    have heq : c'.snd = c'.penultimate := Fin.ext (by omega)
    exact hc'.snd_ne_penultimate heq
  have htree := SimpleGraph.IsTree.card_edgeFinset ⟨hconn, hacyc⟩
  simpa [Fintype.card_fin] using htree

private lemma path_in_walk_support {U : Type} (T : SimpleGraph U) {a b z₁ z₂ : U}
    (p : T.Walk a b) (hp : p.IsPath) (hz1 : z₁ ∈ p.support) (hz2 : z₂ ∈ p.support) :
    ∃ q : T.Walk z₁ z₂, q.IsPath ∧ ∀ x ∈ q.support, x ∈ p.support := by
  obtain ⟨p1, p2, hp1, hp2, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hz1
  have hz2' : z₂ ∈ p1.support ∨ z₂ ∈ p2.support :=
    (Walk.mem_support_append_iff p1 p2).mp (hp_eq ▸ hz2)
  rcases hz2' with hz2_1 | hz2_2
  · let q := (p1.dropUntil z₂ hz2_1).reverse
    refine ⟨q, (hp1.dropUntil hz2_1).reverse, fun x hx => ?_⟩
    rw [Walk.support_reverse, List.mem_reverse] at hx
    exact hp_eq ▸ Walk.support_subset_support_append_left p1 p2
      (p1.support_dropUntil_subset_support hz2_1 hx)
  · let q := p2.takeUntil z₂ hz2_2
    refine ⟨q, hp2.takeUntil hz2_2, fun x hx => ?_⟩
    exact hp_eq ▸ Walk.support_subset_support_append_right p1 p2
      (p2.support_takeUntil_subset_support hz2_2 hx)

private lemma contradict_of_deg_center_lt {V W : Type} [Fintype V] [Fintype W]
    (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hTG : G.IsTree) (hTH : H.IsTree)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hsub : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (hlt : H.degree cH < G.degree cG) :
    False := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnonpath' : ∃ v : V, 3 ≤ G.degree v := by
    obtain ⟨v, hv⟩ := hnonpath
    exact ⟨v, by rw [← ncard_neighborSet_eq_degree]; exact hv⟩
  have hgood_adj : ∀ v : V, G.degree v = 1 → (G.induce {v}ᶜ).diam = 2 * r →
      G.Adj cG v ∧ G.degree cG = H.degree cH + 1 := by
    intro v hv1 hdiam'
    have hw1 : H.degree (σ v) = 1 := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg v, ncard_neighborSet_eq_degree, hv1]
    obtain ⟨φ⟩ := hσ v
    obtain ⟨hcG, hcH, hφc⟩ :=
      iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH heccG huG heccH huH hv1 hw1 hdiam' φ
    have hdeg_ind : (G.induce {v}ᶜ).degree ⟨cG, hcG⟩ = (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ := by
      rw [← hφc]
      exact (φ.degree_eq ⟨cG, hcG⟩).symm
    have hleH : (H.induce {σ v}ᶜ).degree ⟨cH, hcH⟩ ≤ H.degree cH :=
      degree_induce_compl_le H hcH
    have hadjG : G.Adj cG v := by
      by_contra hnadj
      rw [degree_induce_compl_singleton_of_not_adj G hcG hnadj] at hdeg_ind
      omega
    refine ⟨hadjG, ?_⟩
    have h_eq1 := degree_induce_compl_singleton_of_adj G hcG hadjG
    omega
  obtain ⟨v_good, hv_good1, hv_good_diam⟩ := exists_good_leaf G hTG hV hnonpath' hr hdiamG
  have hdeg_eq : G.degree cG = H.degree cH + 1 := (hgood_adj v_good hv_good1 hv_good_diam).2
  have : Nonempty V := hTG.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hTG.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiamG)
  have hxd_r : G.dist x0 xd = 2 * r := hxd.trans hdiamG
  obtain ⟨hcG_mem, hcG_x0, hcG_xd⟩ := diam_path_contains_center G hTG cG heccG p hp hplen_r
  have hx0_ne : x0 ≠ cG := fun h => by rw [← h, SimpleGraph.dist_self] at hcG_x0; omega
  have hxd_ne : xd ≠ cG := fun h => by rw [← h, SimpleGraph.dist_self] at hcG_xd; omega
  let x0' : ({cG}ᶜ : Set V) := ⟨x0, hx0_ne⟩
  let xd' : ({cG}ᶜ : Set V) := ⟨xd, hxd_ne⟩
  let C₁ := (G.induce {cG}ᶜ).connectedComponentMk x0'
  let C₂ := (G.induce {cG}ᶜ).connectedComponentMk xd'
  have hC12 : C₁ ≠ C₂ := by
    intro heq
    have hreach : (G.induce {cG}ᶜ).Reachable x0' xd' := ConnectedComponent.exact heq
    obtain ⟨q⟩ := hreach
    let q_path := q.toPath
    let g : G.induce {cG}ᶜ →g G := (SimpleGraph.Embedding.induce ({cG}ᶜ : Set V)).toHom
    have hqp : q_path.val.map g = p :=
      isTree_path_eq G hTG (q_path.isPath.map Subtype.val_injective) hp
    have hc_not : cG ∉ (q_path.val.map g).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨y, _, hyc⟩
      exact y.2 hyc
    rw [hqp] at hc_not
    exact hc_not hcG_mem
  have h_other_card : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent,
      C ≠ C₁ → C ≠ C₂ → Fintype.card C.supp = 1 := by
    intro C hne1 hne2
    by_contra hcard1
    obtain ⟨z0, hz0⟩ := C.nonempty_supp
    have hC_pos : 1 ≤ Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨⟨z0, hz0⟩⟩
    have hC_ge2 : 2 ≤ Fintype.card C.supp := by omega
    have hx0_not : x0' ∉ C.supp := fun hm => hne1 ((ConnectedComponent.mem_supp_iff C x0').mp hm).symm
    have hxd_not : xd' ∉ C.supp := fun hm => hne2 ((ConnectedComponent.mem_supp_iff C xd').mp hm).symm
    obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C
    let uC : C.supp := ⟨u, hu_mem⟩
    have hC_tree : C.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C
    have hC_nt : Nontrivial C.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hC_deg_u : 1 ≤ C.toSimpleGraph.degree uC := hC_tree.preconnected.degree_pos_of_nontrivial uC
    have hu_deg2 : 2 ≤ G.degree u.1 := by
      rw [component_toSimpleGraph_degree G cG C uC] at hC_deg_u
      dsimp only [uC] at hC_deg_u
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      omega
    obtain ⟨hLC_eq, _⟩ := component_leaves_formula G hTG cG C
    let LC : Finset C.supp := Finset.univ.filter fun x : C.supp => G.degree x.1.1 = 1
    have hLC_pos : 0 < LC.card := by dsimp [LC] at hLC_eq ⊢; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hLC_pos
    simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hwx0 : w.1.1 ≠ x0 := fun h => hx0_not ((Subtype.ext h : w.1 = x0') ▸ w.2)
    have hwxd : w.1.1 ≠ xd := fun h => hxd_not ((Subtype.ext h : w.1 = xd') ▸ w.2)
    have hw_diam : (G.induce {w.1.1}ᶜ).diam = 2 * r :=
      good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hw hwx0 hwxd
    have hw_adj : G.Adj cG w.1.1 := (hgood_adj w.1.1 hw hw_diam).1
    have hwu : w.1 = u := hu_uniq w.1 ⟨w.2, hw_adj⟩
    rw [hwu] at hw
    omega
  have h_C1_props : (∀ x : C₁.supp, G.degree x.1.1 ≤ 2) ∧ Fintype.card C₁.supp = r := by
    have hxd_not : xd' ∉ C₁.supp := fun hm => hC12 ((ConnectedComponent.mem_supp_iff C₁ xd').mp hm).symm
    have huniq1 : ∀ x : C₁.supp, G.degree x.1.1 = 1 → x.1 = x0' := by
      intro x hx1
      by_contra hx_ne
      have hx_x0 : x.1.1 ≠ x0 := fun h => hx_ne (Subtype.ext h)
      have hx_xd : x.1.1 ≠ xd := fun h => hxd_not ((Subtype.ext h : x.1 = xd') ▸ x.2)
      have hxdiam : (G.induce {x.1.1}ᶜ).diam = 2 * r :=
        good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hx1 hx_x0 hx_xd
      have hx_adj : G.Adj cG x.1.1 := (hgood_adj x.1.1 hx1 hxdiam).1
      obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C₁
      have hxu : x.1 = u := hu_uniq x.1 ⟨x.2, hx_adj⟩
      have hC1_ge2 : 2 ≤ Fintype.card C₁.supp := by
        have hux_ne : (⟨u, hu_mem⟩ : C₁.supp) ≠ ⟨x0', rfl⟩ := by
          intro heq
          have hval : u.1 = x0 := congrArg (fun y : C₁.supp => y.1.1) heq
          have hd : G.dist cG u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
          rw [hval, hcG_x0] at hd
          omega
        exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hux_ne⟩⟩
      have hC1_tree : C₁.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₁
      have hC1_nt : Nontrivial C₁.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hdu : 1 ≤ C₁.toSimpleGraph.degree (⟨u, hu_mem⟩ : C₁.supp) :=
        hC1_tree.preconnected.degree_pos_of_nontrivial _
      rw [component_toSimpleGraph_degree] at hdu
      dsimp only at hdu
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      rw [hxu] at hx1
      omega
    obtain ⟨hLC_eq, hLC_ge2⟩ := component_leaves_formula G hTG cG C₁
    let LC : Finset C₁.supp := Finset.univ.filter fun x : C₁.supp => G.degree x.1.1 = 1
    have hLC_sub : LC ⊆ {⟨x0', rfl⟩} := by
      intro x hx
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton]
      exact Subtype.ext (huniq1 x hx)
    have hLC_le1 : LC.card ≤ 1 := (Finset.card_le_card hLC_sub).trans (by simp)
    have hsum_zero : ∑ x ∈ LCᶜ, (G.degree x.1.1 - 2) = 0 := by
      dsimp [LC] at hLC_eq hLC_le1 ⊢
      omega
    have hall_le2 : ∀ x : C₁.supp, G.degree x.1.1 ≤ 2 := by
      intro x
      by_cases hxL : x ∈ LC
      · simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
        omega
      · have hxLc : x ∈ LCᶜ := Finset.mem_compl.mpr hxL
        have hle_sum : G.degree x.1.1 - 2 ≤ ∑ y ∈ LCᶜ, (G.degree y.1.1 - 2) :=
          Finset.single_le_sum (f := fun y : C₁.supp => G.degree y.1.1 - 2) (fun _ _ => Nat.zero_le _) hxLc
        rw [hsum_zero] at hle_sum
        have := hLC_ge2 x hxLc
        omega
    exact ⟨hall_le2, card_component_eq_radius_of_unique_leaf G hTG hr cG C₁ rfl hcG_x0 hall_le2 huniq1⟩
  have h_C2_props : (∀ x : C₂.supp, G.degree x.1.1 ≤ 2) ∧ Fintype.card C₂.supp = r := by
    have hx0_not : x0' ∉ C₂.supp := fun hm => hC12 ((ConnectedComponent.mem_supp_iff C₂ x0').mp hm)
    have huniq2 : ∀ x : C₂.supp, G.degree x.1.1 = 1 → x.1 = xd' := by
      intro x hx1
      by_contra hx_ne
      have hx_x0 : x.1.1 ≠ x0 := fun h => hx0_not ((Subtype.ext h : x.1 = x0') ▸ x.2)
      have hx_xd : x.1.1 ≠ xd := fun h => hx_ne (Subtype.ext h)
      have hxdiam : (G.induce {x.1.1}ᶜ).diam = 2 * r :=
        good_leaf_of_ne_diam_ends G hTG hr hdiamG hxd_r hx1 hx_x0 hx_xd
      have hx_adj : G.Adj cG x.1.1 := (hgood_adj x.1.1 hx1 hxdiam).1
      obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component G hTG cG C₂
      have hxu : x.1 = u := hu_uniq x.1 ⟨x.2, hx_adj⟩
      have hC2_ge2 : 2 ≤ Fintype.card C₂.supp := by
        have hux_ne : (⟨u, hu_mem⟩ : C₂.supp) ≠ ⟨xd', rfl⟩ := by
          intro heq
          have hval : u.1 = xd := congrArg (fun y : C₂.supp => y.1.1) heq
          have hd : G.dist cG u.1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hu_adj
          rw [hval, hcG_xd] at hd
          omega
        exact Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hux_ne⟩⟩
      have hC2_tree : C₂.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₂
      have hC2_nt : Nontrivial C₂.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hdu : 1 ≤ C₂.toSimpleGraph.degree (⟨u, hu_mem⟩ : C₂.supp) :=
        hC2_tree.preconnected.degree_pos_of_nontrivial _
      rw [component_toSimpleGraph_degree] at hdu
      dsimp only at hdu
      have h_eq := degree_induce_compl_singleton_of_adj G u.2 hu_adj.symm
      rw [Subtype.coe_eta] at h_eq
      rw [hxu] at hx1
      omega
    obtain ⟨hLC_eq, hLC_ge2⟩ := component_leaves_formula G hTG cG C₂
    let LC : Finset C₂.supp := Finset.univ.filter fun x : C₂.supp => G.degree x.1.1 = 1
    have hLC_sub : LC ⊆ {⟨xd', rfl⟩} := by
      intro x hx
      simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_singleton]
      exact Subtype.ext (huniq2 x hx)
    have hLC_le1 : LC.card ≤ 1 := (Finset.card_le_card hLC_sub).trans (by simp)
    have hsum_zero : ∑ x ∈ LCᶜ, (G.degree x.1.1 - 2) = 0 := by
      dsimp [LC] at hLC_eq hLC_le1 ⊢
      omega
    have hall_le2 : ∀ x : C₂.supp, G.degree x.1.1 ≤ 2 := by
      intro x
      by_cases hxL : x ∈ LC
      · simp only [LC, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
        omega
      · have hxLc : x ∈ LCᶜ := Finset.mem_compl.mpr hxL
        have hle_sum : G.degree x.1.1 - 2 ≤ ∑ y ∈ LCᶜ, (G.degree y.1.1 - 2) :=
          Finset.single_le_sum (f := fun y : C₂.supp => G.degree y.1.1 - 2) (fun _ _ => Nat.zero_le _) hxLc
        rw [hsum_zero] at hle_sum
        have := hLC_ge2 x hxLc
        omega
    exact ⟨hall_le2, card_component_eq_radius_of_unique_leaf G hTG hr cG C₂ rfl hcG_xd hall_le2 huniq2⟩
  have hG_other_le2 : ∀ v : V, v ≠ cG → G.degree v ≤ 2 := by
    intro v hvc
    let C := (G.induce {cG}ᶜ).connectedComponentMk ⟨v, hvc⟩
    by_cases h1 : C = C₁
    · exact h_C1_props.1 ⟨⟨v, hvc⟩, h1⟩
    · by_cases h2 : C = C₂
      · exact h_C2_props.1 ⟨⟨v, hvc⟩, h2⟩
      · have hC1 : Fintype.card C.supp = 1 := h_other_card C h1 h2
        have hC_tree : C.toSimpleGraph.IsTree := (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C
        have hss : Subsingleton C.supp := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hdeg0 : C.toSimpleGraph.degree (⟨⟨v, hvc⟩, rfl⟩ : C.supp) = 0 := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hemp : C.toSimpleGraph.neighborFinset (⟨⟨v, hvc⟩, rfl⟩ : C.supp) = ∅ := by
            ext y
            simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
            intro hadj
            exact C.toSimpleGraph.ne_of_adj hadj (Subsingleton.elim _ _)
          rw [hemp, Finset.card_empty]
        rw [component_toSimpleGraph_degree] at hdeg0
        dsimp only at hdeg0
        have := degree_induce_compl_le G (Set.mem_compl_singleton_iff.mpr hvc)
        by_cases hadj : G.Adj v cG
        · have h_eq := degree_induce_compl_singleton_of_adj G hvc hadj
          rw [hdeg0] at h_eq
          omega
        · have h_eq := degree_induce_compl_singleton_of_not_adj G hvc hadj
          rw [hdeg0] at h_eq
          omega
  have hH_c_ge2 : 2 ≤ H.degree cH := deg_center_ge_two H hTH hr hdiamH cH heccH
  by_cases hH_c_ge3 : 3 ≤ H.degree cH
  · have hσc_deg : H.degree (σ cG) = G.degree cG := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg cG, ncard_neighborSet_eq_degree]
    have hσc_ne : σ cG ≠ cH := fun h => by rw [h] at hσc_deg; omega
    let v_bad := σ.symm cH
    have hv_bad_ne : v_bad ≠ cG := by
      intro h
      apply hσc_ne
      rw [← h]
      exact σ.apply_symm_apply cH
    have hv_bad_deg : 3 ≤ G.degree v_bad := by
      rw [← ncard_neighborSet_eq_degree, hdeg v_bad, Equiv.apply_symm_apply, ncard_neighborSet_eq_degree]
      exact hH_c_ge3
    have := hG_other_le2 v_bad hv_bad_ne
    omega
  · have hH_c_eq2 : H.degree cH = 2 := by omega
    have hG_c_eq3 : G.degree cG = 3 := by omega
    have hcc_card : Fintype.card (G.induce {cG}ᶜ).ConnectedComponent = 3 := by
      rw [card_connectedComponent_eq_degree G hTG cG, hG_c_eq3]
    have hcomp_rem : 0 < (Finset.univ \ ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent)).card := by
      have hsub2 : ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent).card = 2 := Finset.card_pair hC12
      have hcard_sdiff := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (G.induce {cG}ᶜ).ConnectedComponent) {C₁, C₂}
      have : (Finset.univ ∩ ({C₁, C₂} : Finset (G.induce {cG}ᶜ).ConnectedComponent)).card = 2 := by
        simpa using hsub2
      rw [Finset.card_univ, hcc_card] at hcard_sdiff
      omega
    obtain ⟨C₃, hC3⟩ := Finset.card_pos.mp hcomp_rem
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hC3
    have hC31 : C₃ ≠ C₁ := hC3.2.1
    have hC32 : C₃ ≠ C₂ := hC3.2.2
    have huniv3 : (Finset.univ : Finset (G.induce {cG}ᶜ).ConnectedComponent) = {C₁, C₂, C₃} := by
      refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
      have hc3 : ({C₁, C₂, C₃} : Finset (G.induce {cG}ᶜ).ConnectedComponent).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hC32.symm]
        simp [hC12, hC31.symm]
      rw [hc3, Finset.card_univ, hcc_card]
    have hC3_card : Fintype.card C₃.supp = 1 := h_other_card C₃ hC31 hC32
    have hsum_V : Fintype.card V = 2 * r + 2 := by
      have hs := sum_card_connectedComponent_eq G cG
      have hsum3 : (∑ C : (G.induce {cG}ᶜ).ConnectedComponent, Fintype.card C.supp) =
          Fintype.card C₁.supp + Fintype.card C₂.supp + Fintype.card C₃.supp := by
        have h_eq : (∑ C : (G.induce {cG}ᶜ).ConnectedComponent, Fintype.card C.supp) =
            ∑ C ∈ ({C₁, C₂, C₃} : Finset (G.induce {cG}ᶜ).ConnectedComponent), Fintype.card C.supp := by
          rw [← huniv3]
        rw [h_eq, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
        · omega
        · simp [hC32.symm]
        · simp [hC12, hC31.symm]
      omega
    have hcardW : Fintype.card W = 2 * r + 2 := hcard.symm.trans hsum_V
    have hG_edges : G.edgeFinset.card = 2 * r + 1 := by
      have := hTG.card_edgeFinset
      omega
    obtain ⟨v₀_sub, ⟨hv0_mem, hv0_adj⟩, hv0_uniq⟩ := existsUnique_root_of_component G hTG cG C₃
    let v₀ : V := v₀_sub.1
    have hv0_ne : v₀ ≠ cG := hv0_adj.ne.symm
    have hv0_deg1 : G.degree v₀ = 1 := by
      have hss : Subsingleton C₃.supp := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hdeg0 : C₃.toSimpleGraph.degree (⟨v₀_sub, hv0_mem⟩ : C₃.supp) = 0 := by
        rw [← C₃.toSimpleGraph.card_neighborFinset_eq_degree]
        have hemp : C₃.toSimpleGraph.neighborFinset (⟨v₀_sub, hv0_mem⟩ : C₃.supp) = ∅ := by
          ext y
          simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
          intro hadj
          exact C₃.toSimpleGraph.ne_of_adj hadj (Subsingleton.elim _ _)
        rw [hemp, Finset.card_empty]
      rw [component_toSimpleGraph_degree] at hdeg0
      dsimp only at hdeg0
      have h_eq := degree_induce_compl_singleton_of_adj G v₀_sub.2 hv0_adj.symm
      rw [Subtype.coe_eta] at h_eq
      dsimp only [v₀]
      omega
    -- Now analyze H on 2 * r + 2 vertices
    have : Nonempty W := hTH.connected.nonempty
    obtain ⟨y0, yd, hyd⟩ := H.exists_dist_eq_diam
    obtain ⟨pH, hpH, hpH_len⟩ := hTH.connected.exists_path_of_dist y0 yd
    have hpH_len_r : pH.length = 2 * r := hpH_len.trans (hyd.trans hdiamH)
    obtain ⟨hcH_mem, hcH_y0, hcH_yd⟩ := diam_path_contains_center H hTH cH heccH pH hpH hpH_len_r
    have hpH_card : pH.support.toFinset.card = 2 * r + 1 := by
      rw [List.toFinset_card_of_nodup hpH.support_nodup, pH.length_support, hpH_len_r]
    have hcomp_card : pH.support.toFinsetᶜ.card = 1 := by
      rw [Finset.card_compl, hpH_card, hcardW]
      omega
    obtain ⟨w₀, hw₀_eq⟩ := Finset.card_eq_one.mp hcomp_card
    have hw₀_not : w₀ ∉ pH.support := by
      have : w₀ ∈ pH.support.toFinsetᶜ := by rw [hw₀_eq]; exact Finset.mem_singleton_self w₀
      simpa using this
    have hall_mem_pH : ∀ w : W, w ≠ w₀ → w ∈ pH.support := by
      intro w hne
      by_contra hnot
      have hw_mem : w ∈ pH.support.toFinsetᶜ := by simpa using hnot
      rw [hw₀_eq, Finset.mem_singleton] at hw_mem
      exact hne hw_mem
    have hw0_pos : 1 ≤ H.degree w₀ := by
      have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      exact hTH.preconnected.degree_pos_of_nontrivial w₀
    have hw0_deg1 : H.degree w₀ = 1 := by
      by_contra hne1
      have hge2 : 1 < (H.neighborFinset w₀).card := by
        rw [H.card_neighborFinset_eq_degree]
        omega
      obtain ⟨z₁, hz1, z₂, hz2, hz12⟩ := Finset.one_lt_card.mp hge2
      rw [SimpleGraph.mem_neighborFinset] at hz1 hz2
      have hz1_mem : z₁ ∈ pH.support := hall_mem_pH z₁ hz1.ne.symm
      have hz2_mem : z₂ ∈ pH.support := hall_mem_pH z₂ hz2.ne.symm
      obtain ⟨q, hq, hq_sub⟩ := path_in_walk_support H pH hpH hz1_mem hz2_mem
      have hw0_not_q : w₀ ∉ q.support := fun hm => hw₀_not (hq_sub w₀ hm)
      let q2 : H.Walk z₁ z₂ := Walk.cons hz1.symm (Walk.cons hz2 Walk.nil)
      have hq2 : q2.IsPath := by
        simp [q2, Walk.cons_isPath_iff, hz12, hz1.ne.symm, hz2.ne]
      have hq_eq : q = q2 := isTree_path_eq H hTH hq hq2
      have hw0_in : w₀ ∈ q2.support := by simp [q2]
      rw [← hq_eq] at hw0_in
      exact hw0_not_q hw0_in
    obtain ⟨z, hz_adj, hz_uniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw0_deg1
    have hz_mem : z ∈ pH.support := hall_mem_pH z hz_adj.ne.symm
    have hpH_finset_eq : pH.support.toFinset = Finset.univ.erase w₀ := by
      ext w
      simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun hm hweq => hw₀_not (hweq ▸ hm), hall_mem_pH w⟩
    have h_ind_w0 : Nonempty (H.induce {w₀}ᶜ ≃g pathG (2 * r + 1)) := by
      have h1 := induce_support_iso_pathG H hTH pH hpH
      rw [hpH_len_r, hpH_finset_eq] at h1
      have hset : (({w₀}ᶜ : Set W)) = ((Finset.univ.erase w₀ : Finset W) : Set W) := by
        ext w; simp
      rw [hset]
      exact h1
    obtain ⟨φ₀⟩ := h_ind_w0
    have hH_le2_ne_z : ∀ w : W, w ≠ z → H.degree w ≤ 2 := by
      intro w hwz
      by_cases hww0 : w = w₀
      · subst hww0; omega
      · have hww0' : w ∈ ({w₀}ᶜ : Set W) := Set.mem_compl_singleton_iff.mpr hww0
        have hnadj : ¬ H.Adj w w₀ := fun hadj => hwz (hz_uniq w hadj.symm)
        rw [← degree_induce_compl_singleton_of_not_adj H hww0' hnadj, ← φ₀.degree_eq ⟨w, hww0'⟩]
        exact degree_pathG_le_two (2 * r + 1) (φ₀ ⟨w, hww0'⟩)
    have hσc_deg : H.degree (σ cG) = 3 := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg cG, ncard_neighborSet_eq_degree, hG_c_eq3]
    have hz_eq_σc : z = σ cG := by
      by_contra hne
      have := hH_le2_ne_z (σ cG) (Ne.symm hne)
      omega
    have hz_deg3 : H.degree z = 3 := hz_eq_σc ▸ hσc_deg
    have hz_ne_cH : z ≠ cH := fun h => by rw [h, hH_c_eq2] at hz_deg3; omega
    have hy0_deg1 : H.degree y0 = 1 := by
      have hy0_ne_w0 : y0 ≠ w₀ := fun h => hw₀_not (h ▸ pH.start_mem_support)
      have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
      have hall_y0 : ∀ a : W, H.Adj y0 a → a = w₀ ∨ a = pH.snd := by
        intro a hadj
        by_cases haw0 : a = w₀
        · exact Or.inl haw0
        · exact Or.inr (hTH.isAcyclic.eq_snd_of_adj_start hpH hadj (hall_mem_pH a haw0))
      have hne_y0_z : y0 ≠ z := by
        intro heq
        have hsub_y0 : H.neighborFinset y0 ⊆ {w₀, pH.snd} := by
          intro a ha
          rw [SimpleGraph.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hall_y0 a ha
        have hle2 : H.degree y0 ≤ 2 := by
          rw [← H.card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsub_y0).trans ((Finset.card_insert_le _ _).trans (by simp))
        rw [heq, hz_deg3] at hle2
        omega
      have hsub_y0 : H.neighborFinset y0 ⊆ {pH.snd} := by
        intro a ha
        rw [SimpleGraph.mem_neighborFinset] at ha
        rw [Finset.mem_singleton]
        rcases hall_y0 a ha with rfl | h
        · exact False.elim (hne_y0_z (hz_uniq y0 ha.symm))
        · exact h
      have hpos : 1 ≤ H.degree y0 := by
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        exact hTH.preconnected.degree_pos_of_nontrivial y0
      have hle1 : H.degree y0 ≤ 1 := by
        rw [← H.card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsub_y0).trans (by simp)
      omega
    have hyd_deg1 : H.degree yd = 1 := by
      have hyd_ne_w0 : yd ≠ w₀ := fun h => hw₀_not (h ▸ pH.end_mem_support)
      have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
      have hall_yd : ∀ a : W, H.Adj yd a → a = w₀ ∨ a = pH.penultimate := by
        intro a hadj
        by_cases haw0 : a = w₀
        · exact Or.inl haw0
        · exact Or.inr (hTH.isAcyclic.eq_penultimate_of_adj_end hpH hadj (hall_mem_pH a haw0))
      have hne_yd_z : yd ≠ z := by
        intro heq
        have hsub_yd : H.neighborFinset yd ⊆ {w₀, pH.penultimate} := by
          intro a ha
          rw [SimpleGraph.mem_neighborFinset] at ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact hall_yd a ha
        have hle2 : H.degree yd ≤ 2 := by
          rw [← H.card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsub_yd).trans ((Finset.card_insert_le _ _).trans (by simp))
        rw [heq, hz_deg3] at hle2
        omega
      have hsub_yd : H.neighborFinset yd ⊆ {pH.penultimate} := by
        intro a ha
        rw [SimpleGraph.mem_neighborFinset] at ha
        rw [Finset.mem_singleton]
        rcases hall_yd a ha with rfl | h
        · exact False.elim (hne_yd_z (hz_uniq yd ha.symm))
        · exact h
      have hpos : 1 ≤ H.degree yd := by
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        exact hTH.preconnected.degree_pos_of_nontrivial yd
      have hle1 : H.degree yd ≤ 1 := by
        rw [← H.card_neighborFinset_eq_degree]
        exact (Finset.card_le_card hsub_yd).trans (by simp)
      omega
    by_cases hadj_end : H.Adj z y0 ∨ H.Adj z yd
    · -- Subcase A: H has >= 2 induced copies of pathG (2 * r + 1), G has <= 1
      have h_two_copies : ∃ y_alt : W, y_alt ≠ w₀ ∧
          Nonempty (H.induce ({y_alt}ᶜ : Set W) ≃g pathG (2 * r + 1)) := by
        rcases hadj_end with hadj_z_y0 | hadj_z_yd
        · have hsnd_eq : z = pH.snd :=
            hTH.isAcyclic.eq_snd_of_adj_start hpH hadj_z_y0.symm hz_mem
          have hpH_nn : ¬ pH.Nil := Walk.not_nil_of_ne (fun h => by rw [← h, SimpleGraph.dist_self] at hyd; omega)
          let q : H.Walk w₀ yd := Walk.cons (hsnd_eq ▸ hz_adj) pH.tail
          have hq_path : q.IsPath := by
            rw [Walk.cons_isPath_iff]
            refine ⟨hpH.tail, fun hm => ?_⟩
            rw [Walk.support_tail_of_not_nil pH hpH_nn] at hm
            exact hw₀_not (List.mem_of_mem_tail hm)
          have hq_len : q.length = 2 * r := by
            rw [Walk.length_cons, Walk.length_tail, hpH_len_r]
            omega
          have hy0_not_q : y0 ∉ q.support := by
            rw [Walk.support_cons, List.mem_cons, Walk.support_tail_of_not_nil pH hpH_nn]
            rintro (rfl | hm)
            · exact hw₀_not pH.start_mem_support
            · exact start_notMem_tail_support_of_isPath hpH hm
          have hq_finset : q.support.toFinset = Finset.univ.erase y0 := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              rw [List.mem_toFinset] at hw
              exact Finset.mem_erase.mpr ⟨fun heq => hy0_not_q (heq ▸ hw), Finset.mem_univ _⟩
            · rw [List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len,
                Finset.card_erase_of_mem (Finset.mem_univ y0), Finset.card_univ, hcardW]
              omega
          have h1 := induce_support_iso_pathG H hTH q hq_path
          rw [hq_len, hq_finset] at h1
          have hset : (({y0}ᶜ : Set W)) = ((Finset.univ.erase y0 : Finset W) : Set W) := by
            ext w; simp
          rw [← hset] at h1
          exact ⟨y0, fun h => hw₀_not (h ▸ pH.start_mem_support), h1⟩
        · have hrev := hpH.reverse
          have hsnd_eq : z = pH.reverse.snd :=
            hTH.isAcyclic.eq_snd_of_adj_start hrev hadj_z_yd.symm (by simpa using hz_mem)
          have hrev_nn : ¬ pH.reverse.Nil := Walk.not_nil_of_ne (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          let q : H.Walk w₀ y0 := Walk.cons (hsnd_eq ▸ hz_adj) pH.reverse.tail
          have hq_path : q.IsPath := by
            rw [Walk.cons_isPath_iff]
            refine ⟨hrev.tail, fun hm => ?_⟩
            rw [Walk.support_tail_of_not_nil pH.reverse hrev_nn, Walk.support_reverse] at hm
            exact hw₀_not (List.mem_reverse.mp (List.mem_of_mem_tail hm))
          have hq_len : q.length = 2 * r := by
            rw [Walk.length_cons, Walk.length_tail, Walk.length_reverse, hpH_len_r]
            omega
          have hyd_not_q : yd ∉ q.support := by
            rw [Walk.support_cons, List.mem_cons, Walk.support_tail_of_not_nil pH.reverse hrev_nn]
            rintro (rfl | hm)
            · exact hw₀_not pH.end_mem_support
            · exact start_notMem_tail_support_of_isPath hrev hm
          have hq_finset : q.support.toFinset = Finset.univ.erase yd := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              rw [List.mem_toFinset] at hw
              exact Finset.mem_erase.mpr ⟨fun heq => hyd_not_q (heq ▸ hw), Finset.mem_univ _⟩
            · rw [List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len,
                Finset.card_erase_of_mem (Finset.mem_univ yd), Finset.card_univ, hcardW]
              omega
          have h1 := induce_support_iso_pathG H hTH q hq_path
          rw [hq_len, hq_finset] at h1
          have hset : (({yd}ᶜ : Set W)) = ((Finset.univ.erase yd : Finset W) : Set W) := by
            ext w; simp
          rw [← hset] at h1
          exact ⟨yd, fun h => hw₀_not (h ▸ pH.end_mem_support), h1⟩
      obtain ⟨y_alt, hy_alt_ne, hy_alt_iso⟩ := h_two_copies
      let Af : Finset (Finset V) :=
        Finset.univ.filter fun S : Finset V => Nonempty (G.induce (S : Set V) ≃g pathG (2 * r + 1))
      let Bf : Finset (Finset W) :=
        Finset.univ.filter fun T : Finset W => Nonempty (H.induce (T : Set W) ≃g pathG (2 * r + 1))
      have hB_ge2 : 2 ≤ Bf.card := by
        let Tw0 : Finset W := Finset.univ.erase w₀
        let Talt : Finset W := Finset.univ.erase y_alt
        have hneT : Tw0 ≠ Talt := by
          intro h
          have h1 : w₀ ∈ Talt := by simp [Talt, hy_alt_ne.symm]
          rw [← h] at h1
          simp [Tw0] at h1
        have hm1 : Tw0 ∈ Bf := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hset : (({w₀}ᶜ : Set W)) = (Tw0 : Set W) := by ext w; simp [Tw0]
          rw [← hset]
          exact ⟨φ₀⟩
        have hm2 : Talt ∈ Bf := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hset : (({y_alt}ᶜ : Set W)) = (Talt : Set W) := by ext w; simp [Talt]
          rw [← hset]
          exact hy_alt_iso
        calc
          2 = ({Tw0, Talt} : Finset (Finset W)).card := (Finset.card_pair hneT).symm
          _ ≤ Bf.card := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hm1, Finset.singleton_subset_iff.mpr hm2⟩)
      have hA_le1 : Af.card ≤ 1 := by
        have hsubA : Af ⊆ {Finset.univ.erase v₀} := by
          intro S hS
          simp only [Af, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          obtain ⟨ψ⟩ := hS
          have hScard : S.card = 2 * r + 1 := by
            rw [← Fintype.card_coe]
            exact (Fintype.card_congr ψ.toEquiv).trans (Fintype.card_fin (2 * r + 1))
          have hSc_card : Sᶜ.card = 1 := by
            rw [Finset.card_compl, hScard, hsum_V]
            omega
          obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hSc_card
          have hS_eq : S = Finset.univ.erase u := by
            ext x
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            have hx : x ∉ Sᶜ ↔ x ∉ ({u} : Finset V) := by rw [hu_eq]
            simpa using hx
          have hset : (S : Set V) = ({u}ᶜ : Set V) := by
            rw [hS_eq]; ext x; simp
          rw [hset] at ψ
          have hE_eq : (G.induce {u}ᶜ).edgeFinset.card = 2 * r := by
            rw [Iso.card_edgeFinset_eq ψ]
            have := card_edgeFinset_pathG (2 * r + 1) (by omega)
            omega
          have hG_deg_u : G.degree u = 1 := by
            have h1 : (G.induce {u}ᶜ).edgeFinset.card + G.degree u = G.edgeFinset.card := by
              rw [G.card_edgeFinset_induce_compl_singleton u, G.card_edgeFinset_deleteIncidenceSet u]
              have := G.degree_le_card_edgeFinset u
              omega
            omega
          have huc : u ∈ ({cG}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr (fun h => by rw [h, hG_c_eq3] at hG_deg_u; omega)
          have hcGu : cG ∈ ({u}ᶜ : Set V) := Set.mem_compl_singleton_iff.mpr (Ne.symm huc)
          have hdeg_ind_cG : (G.induce {u}ᶜ).degree ⟨cG, hcGu⟩ ≤ 2 := by
            rw [← ψ.degree_eq ⟨cG, hcGu⟩]
            exact degree_pathG_le_two (2 * r + 1) (ψ ⟨cG, hcGu⟩)
          have hadj_cG_u : G.Adj cG u := by
            by_contra hnadj
            rw [degree_induce_compl_singleton_of_not_adj G hcGu hnadj, hG_c_eq3] at hdeg_ind_cG
            omega
          have hu_v0 : u = v₀ := by
            let u' : ({cG}ᶜ : Set V) := ⟨u, huc⟩
            let Cu := (G.induce {cG}ᶜ).connectedComponentMk u'
            by_cases h1 : Cu = C₁
            · exfalso
              obtain ⟨u1, ⟨hu1_mem, hu1_adj⟩, hu1_uniq⟩ := existsUnique_root_of_component G hTG cG C₁
              have hu_eq_u1 : u' = u1 :=
                (hu1_uniq u' ⟨h1, hadj_cG_u⟩).trans (hu1_uniq u1 ⟨hu1_mem, hu1_adj⟩).symm
              have hC1_nt : Nontrivial C₁.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
              have hdu1 : 1 ≤ C₁.toSimpleGraph.degree (⟨u1, hu1_mem⟩ : C₁.supp) :=
                (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₁ |>.preconnected.degree_pos_of_nontrivial _
              rw [component_toSimpleGraph_degree] at hdu1
              change 1 ≤ (G.induce {cG}ᶜ).degree u1 at hdu1
              rw [← hu_eq_u1] at hdu1
              have h_eq := degree_induce_compl_singleton_of_adj G u'.2 hadj_cG_u.symm
              rw [Subtype.coe_eta] at h_eq
              dsimp only [u'] at hdu1 h_eq
              omega
            · by_cases h2 : Cu = C₂
              · exfalso
                obtain ⟨u2, ⟨hu2_mem, hu2_adj⟩, hu2_uniq⟩ := existsUnique_root_of_component G hTG cG C₂
                have hu_eq_u2 : u' = u2 :=
                  (hu2_uniq u' ⟨h2, hadj_cG_u⟩).trans (hu2_uniq u2 ⟨hu2_mem, hu2_adj⟩).symm
                have hC2_nt : Nontrivial C₂.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
                have hdu2 : 1 ≤ C₂.toSimpleGraph.degree (⟨u2, hu2_mem⟩ : C₂.supp) :=
                  (hTG.isAcyclic.induce {cG}ᶜ).isTree_connectedComponent C₂ |>.preconnected.degree_pos_of_nontrivial _
                rw [component_toSimpleGraph_degree] at hdu2
                change 1 ≤ (G.induce {cG}ᶜ).degree u2 at hdu2
                rw [← hu_eq_u2] at hdu2
                have h_eq := degree_induce_compl_singleton_of_adj G u'.2 hadj_cG_u.symm
                rw [Subtype.coe_eta] at h_eq
                dsimp only [u'] at hdu2 h_eq
                omega
              · have hCu_mem : Cu ∈ ({C₁, C₂, C₃} : Finset _) := by rw [← huniv3]; exact Finset.mem_univ _
                simp only [Finset.mem_insert, Finset.mem_singleton] at hCu_mem
                have hCu3 : Cu = C₃ := by tauto
                have hu_in_C3 : u' ∈ C₃.supp := hCu3
                exact congrArg Subtype.val (hv0_uniq u' ⟨hu_in_C3, hadj_cG_u⟩)
          rw [Finset.mem_singleton, hS_eq, hu_v0]
        exact (Finset.card_le_card hsubA).trans (by simp)
      have hAB : Af.card = Bf.card := by
        have hA_eq : {S : Finset V | Nonempty (G.induce (S : Set V) ≃g pathG (2 * r + 1))} = (Af : Set (Finset V)) := by
          ext S; simp [Af]
        have hB_eq : {T : Finset W | Nonempty (H.induce (T : Set W) ≃g pathG (2 * r + 1))} = (Bf : Set (Finset W)) := by
          ext T; simp [Bf]
        rw [← Set.ncard_coe_finset Af, ← Set.ncard_coe_finset Bf, ← hA_eq, ← hB_eq]
        exact hsub (Fin (2 * r + 1)) (pathG (2 * r + 1)) (by simp [hsum_V])
      omega
    · -- Subcase B: ¬ H.Adj z y0 ∧ ¬ H.Adj z yd
      push Not at hadj_end
      rcases hadj_end with ⟨hnadj_y0, hnadj_yd⟩
      let pH1 : H.Walk y0 (pH.getVert r) := pH.take r
      let pH2 : H.Walk (pH.getVert r) yd := pH.drop r
      have hpH1 : pH1.IsPath := hpH.take r
      have hpH2 : pH2.IsPath := hpH.drop r
      have hpH1_len : pH1.length = r := by rw [Walk.take_length]; omega
      have hpH2_len : pH2.length = r := by rw [Walk.drop_length]; omega
      have hcH_get : cH = pH.getVert r := by
        obtain ⟨q1, q2, hq1, hq2, hpH_eq⟩ := hpH.mem_support_iff_exists_append.mp hcH_mem
        have hq1_dist : q1.length = H.dist y0 cH := isTree_dist_eq_length_of_isPath H hTH q1 hq1
        have hq1_len : q1.length = r := by rw [hq1_dist, SimpleGraph.dist_comm, hcH_y0]
        have hget : pH.getVert q1.length = cH := by
          rw [hpH_eq, Walk.getVert_append]
          simp
        rw [hq1_len] at hget
        exact hget.symm
      have hpH_app : pH1.append pH2 = pH := pH.append_take_drop_eq r
      have hz12 : z ∈ pH1.support ∨ z ∈ pH2.support :=
        (Walk.mem_support_append_iff pH1 pH2).mp (hpH_app.symm ▸ hz_mem)
      have hcontra_leaf : ∀ (y_del y_opp : W) (hy_deg1 : H.degree y_del = 1)
          (hy_nadj : ¬ H.Adj z y_del) (hy_ne : z ∈ ({y_del}ᶜ : Set W)) (hy_opp_ne : y_opp ∈ ({y_del}ᶜ : Set W))
          (q : H.Walk z y_opp), q.IsPath → r + 1 ≤ q.length → y_del ∉ q.support → False := by
        intro y_del y_opp hy_deg1 hy_nadj hy_ne hy_opp_ne q hq hq_len hy_not
        have hHy_tree : (H.induce {y_del}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one H hTH hy_deg1
        have hdeg_z_ind : (H.induce {y_del}ᶜ).degree ⟨z, hy_ne⟩ = 3 := by
          rw [degree_induce_compl_singleton_of_not_adj H hy_ne hy_nadj, hz_deg3]
        have hq_supp : ∀ w ∈ q.support, w ∈ ({y_del}ᶜ : Set W) := fun w hw =>
          Set.mem_compl_singleton_iff.mpr fun h => hy_not (h ▸ hw)
        let q' := q.induce ({y_del}ᶜ : Set W) hq_supp
        have hq' : q'.IsPath := by
          refine Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce ({y_del}ᶜ : Set W)).toHom) ?_
          rw [Walk.map_induce]
          exact hq
        have hdist_z : (H.induce {y_del}ᶜ).dist ⟨z, hy_ne⟩ ⟨y_opp, hy_opp_ne⟩ = q.length := by
          have h1 := isTree_dist_eq_length_of_isPath (H.induce {y_del}ᶜ) hHy_tree q' hq'
          rw [← h1, length_walk_induce]
        have hecc_z_gt : (r : ℕ∞) < (H.induce {y_del}ᶜ).eccent ⟨z, hy_ne⟩ := by
          have hlt : (r : ℕ∞) < ((H.induce {y_del}ᶜ).dist ⟨z, hy_ne⟩ ⟨y_opp, hy_opp_ne⟩ : ℕ∞) :=
            Nat.cast_lt.mpr (by omega)
          rw [(hHy_tree.connected _ _).coe_dist_eq_edist] at hlt
          exact lt_of_lt_of_le hlt SimpleGraph.edist_le_eccent
        let u := σ.symm y_del
        have hσu : σ u = y_del := σ.apply_symm_apply y_del
        have hu_deg1 : G.degree u = 1 := by
          rw [← ncard_neighborSet_eq_degree, hdeg u, hσu, ncard_neighborSet_eq_degree, hy_deg1]
        obtain ⟨φ⟩ := hσ u
        rw [hσu] at φ
        let c' : ({u}ᶜ : Set V) := φ.symm ⟨z, hy_ne⟩
        have hdeg_c' : (G.induce {u}ᶜ).degree c' = 3 := by
          dsimp [c']
          rw [φ.symm.degree_eq ⟨z, hy_ne⟩]
          exact hdeg_z_ind
        have hG_deg_c' : 3 ≤ G.degree c'.1 := hdeg_c'.symm.le.trans (degree_induce_compl_le G c'.2)
        have hc'_eq : c'.1 = cG := by
          by_contra hne
          have := hG_other_le2 c'.1 hne
          omega
        have hecc_c'_gt : (r : ℕ∞) < (G.induce {u}ᶜ).eccent c' := by
          dsimp [c']
          rw [iso_eccent_eq _ _ φ.symm ⟨z, hy_ne⟩]
          exact hecc_z_gt
        have hGu_tree : (G.induce {u}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one G hTG hu_deg1
        have hecc_c'_le : (G.induce {u}ᶜ).eccent c' ≤ r := by
          rw [SimpleGraph.eccent_le_iff]
          intro x'
          rw [← (hGu_tree.connected c' x').coe_dist_eq_edist,
            induce_compl_singleton_dist_eq G hTG hGu_tree, hc'_eq]
          rw [(hTG.connected cG x'.1).coe_dist_eq_edist, ← heccG]
          exact SimpleGraph.edist_le_eccent
        exact absurd (lt_of_lt_of_le hecc_c'_gt hecc_c'_le) (lt_irrefl _)
      rcases hz12 with hz1 | hz2
      · obtain ⟨a, b, ha, hb, hpH1_eq⟩ := hpH1.mem_support_iff_exists_append.mp hz1
        let q : H.Walk z yd := b.append pH2
        have hpH_decomp : pH = a.append q := by
          rw [← hpH_app, hpH1_eq, Walk.append_assoc]
        have hq : q.IsPath := (hpH_decomp ▸ hpH).of_append_right
        have hb_nn : ¬ b.Nil := Walk.not_nil_of_ne (fun h => hz_ne_cH (h.trans hcH_get.symm))
        have hq_len : r + 1 ≤ q.length := by
          rw [Walk.length_append, hpH2_len]
          have : 1 ≤ b.length := Walk.not_nil_iff_lt_length.mp hb_nn
          omega
        have hz_ne_y0 : z ≠ y0 := fun h => by
          rw [h, hy0_deg1] at hz_deg3
          omega
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne hz_ne_y0.symm
        have hy0_not : y0 ∉ q.support := by
          intro hm
          have hq_nn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr ((Nat.zero_lt_succ r).trans_le hq_len)
          have hdisj : a.support.Disjoint q.tail.support := by
            have h1 := (hpH_decomp ▸ hpH).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil q hq_nn] at h1
            exact h1.2.2
          have hy0_a : y0 ∈ a.support := a.start_mem_support
          have hy0_qtail : y0 ∈ q.tail.support := by
            rw [Walk.support_tail_of_not_nil q hq_nn]
            exact mem_support_tail_of_ne q hm hz_ne_y0.symm
          exact hdisj hy0_a hy0_qtail
        exact hcontra_leaf y0 yd hy0_deg1 hnadj_y0 hz_ne_y0 (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          q hq hq_len hy0_not
      · obtain ⟨a, b, ha, hb, hpH2_eq⟩ := hpH2.mem_support_iff_exists_append.mp hz2
        let q : H.Walk z y0 := a.reverse.append pH1.reverse
        have hpH_rev : pH.reverse = b.reverse.append q := by
          rw [← hpH_app, hpH2_eq, Walk.reverse_append, Walk.reverse_append, Walk.append_assoc]
        have hq : q.IsPath := (hpH_rev ▸ hpH.reverse).of_append_right
        have ha_nn : ¬ a.Nil := Walk.not_nil_of_ne (fun h => hz_ne_cH (hcH_get.trans h).symm)
        have hq_len : r + 1 ≤ q.length := by
          rw [Walk.length_append, Walk.length_reverse, Walk.length_reverse, hpH1_len]
          have : 1 ≤ a.length := Walk.not_nil_iff_lt_length.mp ha_nn
          omega
        have hz_ne_yd : z ≠ yd := fun h => by
          rw [h, hyd_deg1] at hz_deg3
          omega
        have hyd_not : yd ∉ q.support := by
          intro hm
          have hq_nn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr ((Nat.zero_lt_succ r).trans_le hq_len)
          have hdisj : b.reverse.support.Disjoint q.tail.support := by
            have h1 := (hpH_rev ▸ hpH.reverse).support_nodup
            rw [Walk.support_append, List.nodup_append', ← Walk.support_tail_of_not_nil q hq_nn] at h1
            exact h1.2.2
          have hyd_b : yd ∈ b.reverse.support := by
            rw [Walk.support_reverse, List.mem_reverse]
            exact Walk.end_mem_support _
          have hyd_qtail : yd ∈ q.tail.support := by
            rw [Walk.support_tail_of_not_nil q hq_nn]
            exact mem_support_tail_of_ne q hm hz_ne_yd.symm
          exact hdisj hyd_b hyd_qtail
        exact hcontra_leaf yd y0 hyd_deg1 hnadj_yd hz_ne_yd (fun h => by rw [h, SimpleGraph.dist_self] at hyd; omega)
          q hq hq_len hyd_not

private lemma tree_R1_H3_R1_H2 :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H2 := by
  intro V W _ _ hV G H σ hTG hTH hσ hdeg hnonpath r cG cH hr hdiamG hdiamH heccG heccH huG huH hsub
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hW : 3 ≤ Fintype.card W := hcard ▸ hV
  have hσ_rev : ∀ w : W, Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := by
    intro w
    obtain ⟨φ⟩ := hσ (σ.symm w)
    rw [σ.apply_symm_apply w] at φ
    exact ⟨φ.symm⟩
  have hdeg_rev : ∀ w : W, (H.neighborSet w).ncard = (G.neighborSet (σ.symm w)).ncard := by
    intro w
    have h := hdeg (σ.symm w)
    rw [σ.apply_symm_apply w] at h
    exact h.symm
  have hnonpath_rev : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v₀, hv₀⟩ := hnonpath
    exact ⟨σ v₀, by rw [← hdeg v₀]; exact hv₀⟩
  have hsub_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card W →
      {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard :=
    fun U _ Q hU => (hsub U Q (hcard ▸ hU)).symm
  by_cases hdegc : G.degree cG = H.degree cH
  · by_cases hleafG : ∃ v : V, G.Adj cG v ∧ (G.neighborSet v).ncard < 2
    · obtain ⟨v, hadj, hv_lt⟩ := hleafG
      have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      have hv_pos : 1 ≤ G.degree v := hTG.preconnected.degree_pos_of_nontrivial v
      rw [ncard_neighborSet_eq_degree] at hv_lt
      have hv1 : G.degree v = 1 := by omega
      exact Or.inl (iso_of_deg_center_eq_and_leaf_adj G H σ hTG hTH hdeg hr hdiamG
        cG cH heccG huG heccH huH hdegc hadj hv1 (hσ v))
    · by_cases hleafH : ∃ w : W, H.Adj cH w ∧ (H.neighborSet w).ncard < 2
      · obtain ⟨w, hadj, hw_lt⟩ := hleafH
        have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have hw_pos : 1 ≤ H.degree w := hTH.preconnected.degree_pos_of_nontrivial w
        rw [ncard_neighborSet_eq_degree] at hw_lt
        have hw1 : H.degree w = 1 := by omega
        obtain ⟨ψ⟩ := iso_of_deg_center_eq_and_leaf_adj H G σ.symm hTH hTG hdeg_rev hr hdiamH
          cH cG heccH huH heccG huG hdegc.symm hadj hw1 (hσ_rev w)
        exact Or.inl ⟨ψ.symm⟩
      · push Not at hleafG hleafH
        refine Or.inr ⟨?_, hleafG, hleafH⟩
        rw [ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree, hdegc]
  · exfalso
    rcases Nat.lt_or_gt_of_ne hdegc with hlt | hgt
    · exact contradict_of_deg_center_lt hW H G σ.symm hTH hTG hσ_rev hdeg_rev hnonpath_rev
        hr hdiamH hdiamG cH cG heccH heccG huH huG hsub_rev hlt
    · exact contradict_of_deg_center_lt hV G H σ hTG hTH hσ hdeg hnonpath
        hr hdiamG hdiamH cG cH heccG heccH huG huH hsub hgt

end TreeR1H3R1H2

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H2 := by
  exact tree_R1_H3_R1_H2
