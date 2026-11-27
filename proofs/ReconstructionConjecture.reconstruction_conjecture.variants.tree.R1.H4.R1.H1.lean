import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

-- Step ReconstructionConjecture.reconstruction_conjecture.variants.tree.R1.H4.R1.H1
-- Credit: @jared-jasinski

namespace ReconTreeH4R1H1

open SimpleGraph

private abbrev pathG (m : ℕ) : SimpleGraph (Fin m) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma pathG_neighborSet_ncard_le_two (m : ℕ) (i : Fin m) :
    ((pathG m).neighborSet i).ncard ≤ 2 := by
  have hsub : (pathG m).neighborSet i ⊆
      ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}) := by
    intro j hj
    rcases hj with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have h1 : ({j : Fin m | j.val = i.val + 1}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val = i.val + 1 at ha
      change b.val = i.val + 1 at hb
      exact Fin.ext (ha.trans hb.symm)
  have h2 : ({j : Fin m | j.val + 1 = i.val}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr fun a ha b hb => by
      change a.val + 1 = i.val at ha
      change b.val + 1 = i.val at hb
      exact Fin.ext (by omega)
  calc
    ((pathG m).neighborSet i).ncard
        ≤ ({j : Fin m | j.val = i.val + 1} ∪ {j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_le_ncard hsub
    _ ≤ ({j : Fin m | j.val = i.val + 1}).ncard + ({j : Fin m | j.val + 1 = i.val}).ncard :=
          Set.ncard_union_le _ _
    _ ≤ 2 := by omega

-- Walk of length k in G along an induced pathG m, for k < m.
private lemma walk_of_pathG_iso {V : Type} {G : SimpleGraph V} {S : Finset V} {m : ℕ}
    (e : G.induce (S : Set V) ≃g pathG m) :
    ∀ (k : ℕ) (hk : k < m),
      ∃ p : G.Walk (e.symm ⟨0, by omega⟩).val (e.symm ⟨k, hk⟩).val,
        p.length = k ∧ p.IsPath ∧
        ∀ x ∈ p.support, ∃ i : Fin m, i.val ≤ k ∧ x = (e.symm i).val := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨Walk.nil, rfl, Walk.IsPath.nil, ?_⟩
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact ⟨⟨0, hk⟩, le_rfl, hx⟩
  | succ k ih =>
    intro hk
    obtain ⟨p, hlen, hpath, hsupp⟩ := ih (by omega)
    have hadj_path : (pathG m).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
    have hadj_G : G.Adj (e.symm ⟨k, by omega⟩).val (e.symm ⟨k + 1, hk⟩).val :=
      (e.symm.map_rel_iff).mpr hadj_path
    have hnotmem : (e.symm ⟨k + 1, hk⟩).val ∉ p.support := by
      intro hmem
      obtain ⟨i, hi, heq⟩ := hsupp _ hmem
      have hsub : e.symm ⟨k + 1, hk⟩ = e.symm i := Subtype.ext heq
      have hfin : (⟨k + 1, hk⟩ : Fin m) = i := e.symm.injective hsub
      have : k + 1 = i.val := congrArg Fin.val hfin
      omega
    let q := p.concat hadj_G
    refine ⟨q, by simp [q, hlen], ?_, ?_⟩
    · rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
      refine ⟨hpath.support_nodup, List.nodup_singleton _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact fun heq => hnotmem (heq ▸ hx)
    · intro x hx
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · obtain ⟨i, hi, rfl⟩ := hsupp x hx
        exact ⟨i, by omega, rfl⟩
      · exact ⟨⟨k + 1, hk⟩, le_rfl, rfl⟩

private lemma le_diam_of_induced_pathG {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) {S : Finset V} {d : ℕ}
    (e : G.induce (S : Set V) ≃g pathG (d + 1)) :
    d ≤ G.diam := by
  classical
  obtain ⟨p, hlen, hpath, -⟩ := walk_of_pathG_iso e d (Nat.lt_succ_self d)
  let u := (e.symm ⟨0, Nat.zero_lt_succ d⟩).val
  let v := (e.symm ⟨d, Nat.lt_succ_self d⟩).val
  have : Nonempty V := ⟨u⟩
  obtain ⟨q, hqlen⟩ := hT.connected.exists_walk_length_eq_dist u v
  have : Subsingleton (G.Path u v) :=
    (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) u v
  have huniq : (⟨q.bypass, q.bypass_isPath⟩ : G.Path u v) = ⟨p, hpath⟩ :=
    Subsingleton.elim _ _
  have hle : p.length ≤ q.length := by
    have h1 : q.bypass.length ≤ q.length := q.length_bypass_le_length
    have h2 : q.bypass = p := congrArg Subtype.val huniq
    rw [h2] at h1
    exact h1
  have hdist : d ≤ G.dist u v := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist.trans (G.dist_le_diam hediam)

private lemma exists_induced_pathG_diam {V : Type} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hT : G.IsTree) :
    ∃ S : Finset V, S.card = G.diam + 1 ∧ Nonempty (G.induce (S : Set V) ≃g pathG (G.diam + 1)) := by
  classical
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  obtain ⟨p0, hp0len⟩ := hT.connected.exists_walk_length_eq_dist u v
  let p : G.Walk u v := p0.bypass
  have hp_path : p.IsPath := p0.bypass_isPath
  have hp_dist : p.length = G.dist u v := by
    have hle : p.length ≤ p0.length := p0.length_bypass_le_length
    have hge : G.dist u v ≤ p.length := G.dist_le p
    omega
  have hp_len : p.length = G.diam := hp_dist.trans huv
  let f : Fin (G.diam + 1) → V := fun i => p.getVert i.val
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hi : i.val ≤ p.length := by omega
    have hj : j.val ≤ p.length := by omega
    have hi' : i.val < p.support.length := by rw [Walk.length_support]; omega
    have hj' : j.val < p.support.length := by rw [Walk.length_support]; omega
    change p.getVert i.val = p.getVert j.val at hij
    rw [Walk.getVert_eq_support_getElem p hi, Walk.getVert_eq_support_getElem p hj] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp_path.support_nodup).mp hij)
  let S : Finset V := Finset.univ.image f
  have hScard : S.card = G.diam + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  have hf_mem : ∀ i : Fin (G.diam + 1), f i ∈ (S : Set V) := fun i =>
    Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let toFun : Fin (G.diam + 1) → (S : Set V) := fun i => ⟨f i, hf_mem i⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  let eqv : Fin (G.diam + 1) ≃ (S : Set V) := Equiv.ofBijective toFun hbij
  have hrel : ∀ i j : Fin (G.diam + 1), (pathG (G.diam + 1)).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    constructor
    · intro h
      simp only [pathG] at h
      rcases h with h | h
      · have hi : i.val < p.length := by omega
        have := p.adj_getVert_succ hi
        simpa [f, h] using this
      · have hj : j.val < p.length := by omega
        have := p.adj_getVert_succ hj
        exact (by simpa [f, h] using this : G.Adj (f j) (f i)).symm
    · intro hadj
      by_contra hnot
      have hnot1 : i.val + 1 ≠ j.val := fun h => hnot (Or.inl h)
      have hnot2 : j.val + 1 ≠ i.val := fun h => hnot (Or.inr h)
      have hne : i.val ≠ j.val := fun he => G.ne_of_adj hadj (congrArg f (Fin.ext he))
      have hlt_or : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
      have shortcut : ∀ a b : Fin (G.diam + 1), a.val + 1 < b.val → G.Adj (f a) (f b) → False := by
        intro a b hab hAB
        have ha_le : a.val ≤ p.length := by omega
        have hb_le : b.val ≤ p.length := by omega
        have ha_lt : a.val < p.support.length := by rw [Walk.length_support]; omega
        have hb_lt : b.val < p.support.length := by rw [Walk.length_support]; omega
        let p1 := p.takeUntil (p.getVert a.val) (p.getVert_mem_support a.val)
        let p2 := p.dropUntil (p.getVert b.val) (p.getVert_mem_support b.val)
        have hidx_a : p.support.idxOf (p.getVert a.val) = a.val := by
          rw [Walk.getVert_eq_support_getElem p ha_le]
          exact hp_path.support_nodup.idxOf_getElem a.val ha_lt
        have hidx_b : p.support.idxOf (p.getVert b.val) = b.val := by
          rw [Walk.getVert_eq_support_getElem p hb_le]
          exact hp_path.support_nodup.idxOf_getElem b.val hb_lt
        have hp1_len : p1.length = a.val := by
          rw [Walk.length_takeUntil, hidx_a]
        have hp2_len : p2.length = p.length - b.val := by
          have hspec := p.take_spec (p.getVert_mem_support b.val)
          have hsum := congrArg Walk.length hspec
          rw [Walk.length_append, Walk.length_takeUntil, hidx_b] at hsum
          change b.val + p2.length = p.length at hsum
          omega
        let q : G.Walk u v := p1.append (Walk.cons hAB p2)
        have hqlen : q.length < p.length := by
          simp only [q, Walk.length_append, Walk.length_cons]
          omega
        have hdist_le : G.dist u v ≤ q.length := G.dist_le q
        omega
      rcases hlt_or with h | h
      · exact shortcut i j h hadj
      · exact shortcut j i h hadj.symm
  refine ⟨S, hScard, ⟨(RelIso.mk eqv (fun {i j} => (hrel i j).symm)).symm⟩⟩

private lemma diam_add_one_lt_card {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    G.diam + 1 < Fintype.card V := by
  classical
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  obtain ⟨S, hScard, ⟨e⟩⟩ := exists_induced_pathG_diam hT
  have hle : S.card ≤ Fintype.card V := Finset.card_le_univ S
  by_contra hnot
  have heq : S.card = Fintype.card V := by omega
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S heq
  have hv₀S : v₀ ∈ (S : Set V) := by simp [hSuniv]
  let i0 : Fin (G.diam + 1) := e ⟨v₀, hv₀S⟩
  have hnb_le : (G.neighborSet v₀).ncard ≤ ((pathG (G.diam + 1)).neighborSet i0).ncard := by
    let g : G.neighborSet v₀ → (pathG (G.diam + 1)).neighborSet i0 := fun ⟨w, hw⟩ =>
      ⟨e ⟨w, by simp [hSuniv]⟩, by
        change (pathG (G.diam + 1)).Adj (e ⟨v₀, hv₀S⟩) (e ⟨w, by simp [hSuniv]⟩)
        exact e.map_rel_iff.mpr hw⟩
    have hginj : Function.Injective g := by
      intro ⟨w1, hw1⟩ ⟨w2, hw2⟩ h
      have h1 : e ⟨w1, by simp [hSuniv]⟩ = e ⟨w2, by simp [hSuniv]⟩ := congrArg Subtype.val h
      have hw : w1 = w2 := congrArg Subtype.val (e.injective h1)
      exact Subtype.ext hw
    have hcard := Fintype.card_le_of_injective g hginj
    simpa [Set.ncard_eq_toFinset_card'] using hcard
  have hle2 := pathG_neighborSet_ncard_le_two (G.diam + 1) i0
  omega

private lemma two_le_diam_of_deg3 {V : Type} [Fintype V] {G : SimpleGraph V}
    (hT : G.IsTree) (hdeg3 : ∃ v : V, 3 ≤ (G.neighborSet v).ncard) :
    2 ≤ G.diam := by
  obtain ⟨v₀, hv₀⟩ := hdeg3
  have : Nonempty V := ⟨v₀⟩
  have h1lt : 1 < (G.neighborSet v₀).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp h1lt
  have hnotadj : ¬ G.Adj a b := by
    intro hAB
    have ha' : G.Adj v₀ a := ha
    have hb' : G.Adj v₀ b := hb
    have ha_ne : a ≠ v₀ := (G.ne_of_adj ha').symm
    have hb_ne : b ≠ v₀ := (G.ne_of_adj hb').symm
    let p1 : G.Walk a b := Walk.cons hAB Walk.nil
    let p2 : G.Walk a b := Walk.cons ha'.symm (Walk.cons hb' Walk.nil)
    have hp1 : p1.IsPath := by
      rw [Walk.isPath_def]
      simp [p1, hab]
    have hp2 : p2.IsPath := by
      dsimp only [p2]
      rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
      simp [ha_ne, hb_ne.symm, hab]
    have hsub : Subsingleton (G.Path a b) :=
      (SimpleGraph.isAcyclic_iff_subsingleton_path.mp hT.isAcyclic) a b
    have heq : (⟨p1, hp1⟩ : G.Path a b) = ⟨p2, hp2⟩ := Subsingleton.elim _ _
    have hlen : p1.length = p2.length := congrArg (fun x : G.Path a b => x.1.length) heq
    simp [p1, p2] at hlen
  have hdist_ne0 : G.dist a b ≠ 0 := by
    intro h0
    exact hab ((hT.connected.dist_eq_zero_iff).mp h0)
  have hdist_ne1 : G.dist a b ≠ 1 := by
    intro h1
    exact hnotadj (G.dist_eq_one_iff_adj.mp h1)
  have hdist_ge2 : 2 ≤ G.dist a b := by omega
  have hediam : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hT.connected
  exact hdist_ge2.trans (G.dist_le_diam hediam)

end ReconTreeH4R1H1

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H1 := by
  intro V W _ _ hV G H σ hTG hTH hdeg hnonpath hodd hkelly
  have hcardVW : Fintype.card V = Fintype.card W := Fintype.card_congr σ
  have hnonpathH : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
    obtain ⟨v₀, hv₀⟩ := hnonpath
    exact ⟨σ v₀, by rw [← hdeg v₀]; exact hv₀⟩
  have hG2 : 2 ≤ G.diam := ReconTreeH4R1H1.two_le_diam_of_deg3 hTG hnonpath
  have hG3 : 3 ≤ G.diam := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hGlt : G.diam + 1 < Fintype.card V := ReconTreeH4R1H1.diam_add_one_lt_card hTG hnonpath
  have hHlt : H.diam + 1 < Fintype.card V := by
    rw [hcardVW]
    exact ReconTreeH4R1H1.diam_add_one_lt_card hTH hnonpathH
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have : Nonempty W := ⟨σ (Classical.arbitrary V)⟩
  have hGH : G.diam ≤ H.diam := by
    obtain ⟨S, -, hSiso⟩ := ReconTreeH4R1H1.exists_induced_pathG_diam hTG
    have hpos : 0 < {S : Finset V | Nonempty (G.induce (S : Set V) ≃g ReconTreeH4R1H1.pathG (G.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨S, hSiso⟩
    rw [hkelly (Fin (G.diam + 1)) (ReconTreeH4R1H1.pathG (G.diam + 1)) (by simpa using hGlt)] at hpos
    obtain ⟨T, ⟨eT⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH4R1H1.le_diam_of_induced_pathG hTH eT
  have hHG : H.diam ≤ G.diam := by
    obtain ⟨T, -, hTiso⟩ := ReconTreeH4R1H1.exists_induced_pathG_diam hTH
    have hpos : 0 < {T : Finset W | Nonempty (H.induce (T : Set W) ≃g ReconTreeH4R1H1.pathG (H.diam + 1))}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨T, hTiso⟩
    rw [← hkelly (Fin (H.diam + 1)) (ReconTreeH4R1H1.pathG (H.diam + 1)) (by simpa using hHlt)] at hpos
    obtain ⟨S, ⟨eS⟩⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    exact ReconTreeH4R1H1.le_diam_of_induced_pathG hTG eS
  exact ⟨hG3, le_antisymm hGH hHG⟩
