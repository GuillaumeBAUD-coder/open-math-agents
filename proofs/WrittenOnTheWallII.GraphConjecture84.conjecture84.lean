import FormalConjectures.WrittenOnTheWallII.GraphConjecture84

/-!
# Proof of Written on the Wall II - Conjecture 84

For every finite simple connected graph `G` on a nontrivial vertex set with `0 < G.minDegree`,
we prove `2 * G.radius.toNat / G.minDegree ≤ largestInducedTreeSize G`.

1. If `2 ≤ G.minDegree`, a shortest walk of length at least `G.radius.toNat` induces a tree of
   order at least `G.radius.toNat + 1`, giving the bound directly.
2. We prove Chung / Erdos-Saks-Sos's theorem: every finite nonempty connected graph of radius `r`
   contains an induced path on at least `2 * r - 1` vertices, via Camby-Schaudt's characterization
   of minimum connected dominating sets in `P_k`-free graphs.
3. We prove Gebendorfer's cut-vertex theorem: every finite connected graph with a cut vertex
   satisfies `2 * G.radius.toNat ≤ largestInducedTreeSize G`, by minimal-counterexample reduction
   to a 2-connected core with uniform-length pendant paths.
-/

open SimpleGraph Finset

namespace GraphConj84Proof

section BasicTransfer

variable {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}

private lemma connected_mk {H : SimpleGraph V} (x : V) (h : H.Preconnected) : H.Connected :=
  @SimpleGraph.Connected.mk _ _ h ⟨x⟩

private def induceMonoHom {S T : Set V} (h : S ⊆ T) : G.induce S →g G.induce T :=
  ⟨fun x => ⟨x.val, h x.property⟩, fun hadj => hadj⟩

private lemma walk_length_induce {S : Set V} {u v : V}
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (p.map_induce hp)
  rwa [Walk.length_map] at h

private lemma mem_support_map_induce {S : Set V} {u v : ↥S}
    {p : (G.induce S).Walk u v} {x : V}
    (hx : x ∈ (p.map (SimpleGraph.Embedding.induce S).toHom).support) :
    ∃ z : ↥S, z ∈ p.support ∧ z.val = x := by
  rw [Walk.support_map, List.mem_map] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨z, hz, rfl⟩

private lemma not_mem_takeUntil_and_dropUntil_of_isPath [DecidableEq V] {a b w v : V}
    {p : G.Walk a b} (hp : p.IsPath) (hw : w ∈ p.support)
    (hv1 : v ∈ (p.takeUntil w hw).support) (hv2 : v ∈ (p.dropUntil w hw).support)
    (hvw : v ≠ w) : False := by
  have hsplit : p.support = (p.takeUntil w hw).support ++ (p.dropUntil w hw).support.tail := by
    have := congrArg Walk.support (p.take_spec hw)
    rw [Walk.support_append] at this
    exact this.symm
  have hv2' : v ∈ (p.dropUntil w hw).support.tail := by
    have hcons := (p.dropUntil w hw).support_eq_cons
    rw [hcons] at hv2
    rcases List.mem_cons.mp hv2 with rfl | htail
    · exact (hvw rfl).elim
    · exact htail
  have hnd := hp.support_nodup
  rw [hsplit, List.nodup_append] at hnd
  exact hnd.2.2 v hv1 v hv2' rfl

private lemma edist_hom_le (f : G →g K) (u v : V) : K.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    calc K.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = (p.length : ℕ∞) := by simp
  · rw [edist_eq_top_of_not_reachable h]
    exact le_top

private lemma dist_hom_le (f : G →g K) {u v : V} (h : G.Reachable u v) :
    K.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp, ← Walk.length_map f]
  exact K.dist_le (p.map f)

private lemma induced_subgraph_dist_ge {S : Set V} {a b : ↥S} (h : (G.induce S).Reachable a b) :
    G.dist a.val b.val ≤ (G.induce S).dist a b :=
  dist_hom_le (SimpleGraph.Embedding.induce S).toHom h

private lemma edist_iso (e : G ≃g K) (u v : V) : K.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (edist_hom_le e.toHom u v)
  have := edist_hom_le e.symm.toHom (e u) (e v)
  simpa using this

private lemma radius_iso (e : G ≃g K) : K.radius = G.radius := by
  rw [radius_eq_iInf_iSup_edist, radius_eq_iInf_iSup_edist, ← e.surjective.iInf_comp]
  congr 1
  funext u
  rw [← e.surjective.iSup_comp]
  simp only [edist_iso]

private lemma tree_iso_le [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (e : G ≃g K) :
    largestInducedTreeSize K ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t, rfl, ht⟩
  let s : Finset V := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_, e.injective.injOn, ?_⟩
    · intro x hx
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨y, hy, rfl⟩
  have hs : (G.induce (s : Set V)).IsTree := (Iso.induce e hbij).isTree_iff.mpr ht
  have hcard : s.card = t.card := by simp [s]
  have := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at this
  omega

private lemma tree_induce_le [Fintype V] [DecidableEq V] (S : Finset V) :
    largestInducedTreeSize (G.induce (S : Set V)) ≤ largestInducedTreeSize G := by
  classical
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t, rfl, ht⟩
  let s : Finset V := t.map ⟨Subtype.val, Subtype.val_injective⟩
  have hbij : Set.BijOn Subtype.val (t : Set ↥(S : Set V)) (s : Set V) := by
    refine ⟨?_, Subtype.val_injective.injOn, ?_⟩
    · intro x hx
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · intro y hy
      simp only [s, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, hx, rfl⟩
  let e : (G.induce (S : Set V)).induce (t : Set ↥(S : Set V)) ≃g G.induce (s : Set V) :=
    { toEquiv := hbij.equiv Subtype.val
      map_rel_iff' := fun {_ _} => Iff.rfl }
  have hs : (G.induce (s : Set V)).IsTree := e.isTree_iff.mp ht
  have hcard : s.card = t.card := by simp [s]
  have := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at this
  omega

private lemma connected_eccent_ne_top [Finite V] (hG : G.Connected) (u : V) :
    G.eccent u ≠ ⊤ := by
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  rw [← hv, edist_ne_top_iff_reachable]
  exact hG u v

private lemma connected_radius_ne_top [Finite V] [Nonempty V] (hG : G.Connected) :
    G.radius ≠ ⊤ :=
  G.radius_ne_top_iff.mpr hG

private lemma dist_le_eccent_toNat [Finite V] (hG : G.Connected) (u v : V) :
    G.dist u v ≤ (G.eccent u).toNat :=
  ENat.toNat_le_toNat G.edist_le_eccent (connected_eccent_ne_top hG u)

private lemma exists_dist_eq_eccent_toNat [Finite V] (u : V) :
    ∃ v : V, G.dist u v = (G.eccent u).toNat := by
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  exact ⟨v, by simp [SimpleGraph.dist, hv]⟩

private lemma radius_toNat_le_eccent_toNat [Finite V] (hG : G.Connected) (u : V) :
    G.radius.toNat ≤ (G.eccent u).toNat :=
  ENat.toNat_le_toNat G.radius_le_eccent (connected_eccent_ne_top hG u)

private lemma exists_dist_ge_radius_toNat [Finite V] (hG : G.Connected) (u : V) :
    ∃ v : V, G.radius.toNat ≤ G.dist u v := by
  obtain ⟨v, hv⟩ := exists_dist_eq_eccent_toNat (G := G) u
  exact ⟨v, hv ▸ radius_toNat_le_eccent_toNat hG u⟩

private lemma radius_toNat_le_of_exists_forall_dist_le [Finite V] [Nonempty V]
    (hG : G.Connected) {r : ℕ} (h : ∃ c : V, ∀ v : V, G.dist c v ≤ r) :
    G.radius.toNat ≤ r := by
  obtain ⟨c, hc⟩ := h
  have hecc : G.eccent c ≤ (r : ℕ∞) := by
    rw [eccent_le_iff]
    intro v
    rw [← (hG c v).coe_dist_eq_edist]
    exact_mod_cast hc v
  have hrad : G.radius ≤ (r : ℕ∞) := G.radius_le_eccent.trans hecc
  exact (ENat.toNat_le_toNat hrad (ENat.natCast_ne_top r)).trans (by simp)

private lemma exists_center_forall_dist_le [Finite V] [Nonempty V] (hG : G.Connected) :
    ∃ c : V, ∀ v : V, G.dist c v ≤ G.radius.toNat := by
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  refine ⟨c, fun v => ?_⟩
  have h := dist_le_eccent_toNat hG c v
  rwa [hc] at h

end BasicTransfer

section InducedPaths

variable {V : Type*} {G : SimpleGraph V}

private def finCons {k : ℕ} (y : V) (f : Fin k → V) : Fin (k + 1) → V :=
  Fin.cases y f

private lemma finCons_zero {k : ℕ} (y : V) (f : Fin k → V) :
    finCons y f 0 = y := rfl

private lemma finCons_succ {k : ℕ} (y : V) (f : Fin k → V) (i : Fin k) :
    finCons y f i.succ = f i := rfl

private def finSnoc {k : ℕ} (f : Fin k → V) (z : V) : Fin (k + 1) → V :=
  Fin.lastCases z f

private lemma finSnoc_last {k : ℕ} (f : Fin k → V) (z : V) :
    finSnoc f z (Fin.last k) = z := by
  simp [finSnoc]

private lemma finSnoc_castSucc {k : ℕ} (f : Fin k → V) (z : V) (i : Fin k) :
    finSnoc f z i.castSucc = f i := by
  simp [finSnoc]

/-- An induced path of order `k` in `G`, represented by an injective map `Fin k → V`. -/
private def IsInducedPath (G : SimpleGraph V) (k : ℕ) (f : Fin k → V) : Prop :=
  Function.Injective f ∧
    ∀ i j : Fin k, G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

private lemma IsInducedPath.adj_succ {k : ℕ} {f : Fin k → V} (hf : IsInducedPath G k f)
    {i : ℕ} (hi : i + 1 < k) : G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) :=
  (hf.2 ⟨i, by omega⟩ ⟨i + 1, hi⟩).mpr (Or.inl rfl)

private lemma IsInducedPath.rev {k : ℕ} {f : Fin k → V} (hf : IsInducedPath G k f) :
    IsInducedPath G k (fun i => f i.rev) := by
  refine ⟨fun a b hab => Fin.rev_injective (hf.1 hab), fun i j => ?_⟩
  rw [hf.2]
  simp only [Fin.val_rev]
  omega

private lemma IsInducedPath.take {k m : ℕ} (hmk : m ≤ k) {f : Fin k → V}
    (hf : IsInducedPath G k f) :
    IsInducedPath G m (fun i => f (Fin.castLE hmk i)) := by
  refine ⟨fun a b hab => Fin.castLE_injective hmk (hf.1 hab), fun i j => ?_⟩
  simpa using hf.2 (Fin.castLE hmk i) (Fin.castLE hmk j)

private lemma IsInducedPath.cast {k m : ℕ} (h : k = m) {f : Fin k → V}
    (hf : IsInducedPath G k f) :
    IsInducedPath G m (fun i => f (Fin.cast h.symm i)) := by
  subst h
  exact hf

private lemma IsInducedPath.cons {k : ℕ} (hk : 1 ≤ k) {f : Fin k → V}
    (hf : IsInducedPath G k f) {y : V}
    (hy_not : ∀ i : Fin k, y ≠ f i)
    (hy0 : G.Adj y (f ⟨0, by omega⟩))
    (hy_rest : ∀ i : Fin k, i.val ≠ 0 → ¬ G.Adj y (f i)) :
    IsInducedPath G (k + 1) (finCons y f) := by
  refine ⟨?_, ?_⟩
  · intro a b
    refine Fin.cases ?_ ?_ a
    · refine Fin.cases ?_ ?_ b
      · intro _; rfl
      · intro j hab
        rw [finCons_zero, finCons_succ] at hab
        exact (hy_not j hab).elim
    · intro i
      refine Fin.cases ?_ ?_ b
      · intro hab
        rw [finCons_zero, finCons_succ] at hab
        exact (hy_not i hab.symm).elim
      · intro j hab
        rw [finCons_succ, finCons_succ] at hab
        exact congrArg Fin.succ (hf.1 hab)
  · intro a b
    refine Fin.cases ?_ ?_ a
    · refine Fin.cases ?_ ?_ b
      · simp [finCons_zero, G.irrefl]
      · intro j
        rw [finCons_zero, finCons_succ]
        simp only [Fin.val_zero, Fin.val_succ]
        by_cases hj : j.val = 0
        · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
          rw [hj0]
          simp [hy0]
        · constructor
          · intro hadj
            exact (hy_rest j hj hadj).elim
          · omega
    · intro i
      refine Fin.cases ?_ ?_ b
      · rw [finCons_zero, finCons_succ]
        simp only [Fin.val_zero, Fin.val_succ]
        by_cases hi : i.val = 0
        · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
          rw [hi0]
          simp [hy0.symm]
        · constructor
          · intro hadj
            exact (hy_rest i hi hadj.symm).elim
          · omega
      · intro j
        rw [finCons_succ, finCons_succ]
        simp only [Fin.val_succ]
        rw [hf.2]
        omega

private lemma IsInducedPath.snoc {k : ℕ} (hk : 1 ≤ k) {f : Fin k → V}
    (hf : IsInducedPath G k f) {z : V}
    (hz_not : ∀ i : Fin k, z ≠ f i)
    (hzlast : G.Adj z (f ⟨k - 1, by omega⟩))
    (hz_rest : ∀ i : Fin k, i.val ≠ k - 1 → ¬ G.Adj z (f i)) :
    IsInducedPath G (k + 1) (finSnoc f z) := by
  refine ⟨?_, ?_⟩
  · intro a b
    refine Fin.lastCases ?_ ?_ a
    · refine Fin.lastCases ?_ ?_ b
      · intro _; rfl
      · intro j hab
        rw [finSnoc_last, finSnoc_castSucc] at hab
        exact (hz_not j hab).elim
    · intro i
      refine Fin.lastCases ?_ ?_ b
      · intro hab
        rw [finSnoc_last, finSnoc_castSucc] at hab
        exact (hz_not i hab.symm).elim
      · intro j hab
        rw [finSnoc_castSucc, finSnoc_castSucc] at hab
        exact congrArg Fin.castSucc (hf.1 hab)
  · intro a b
    refine Fin.lastCases ?_ ?_ a
    · refine Fin.lastCases ?_ ?_ b
      · simp [finSnoc_last, G.irrefl]
      · intro j
        rw [finSnoc_last, finSnoc_castSucc]
        simp only [Fin.val_last, Fin.val_castSucc]
        by_cases hj : j.val = k - 1
        · have hjl : j = ⟨k - 1, by omega⟩ := Fin.ext hj
          rw [hjl]
          have : k - 1 + 1 = k := by omega
          simp [hzlast, this]
        · constructor
          · intro hadj
            exact (hz_rest j hj hadj).elim
          · omega
    · intro i
      refine Fin.lastCases ?_ ?_ b
      · rw [finSnoc_last, finSnoc_castSucc]
        simp only [Fin.val_last, Fin.val_castSucc]
        by_cases hi : i.val = k - 1
        · have hil : i = ⟨k - 1, by omega⟩ := Fin.ext hi
          rw [hil]
          have : k - 1 + 1 = k := by omega
          simp [hzlast.symm, this]
        · constructor
          · intro hadj
            exact (hz_rest i hi hadj.symm).elim
          · omega
      · intro j
        rw [finSnoc_castSucc, finSnoc_castSucc]
        simp only [Fin.val_castSucc]
        exact hf.2 i j

private lemma IsInducedPath.map_induce {S : Set V} {k : ℕ}
    {f : Fin k → ↥S} (hf : IsInducedPath (G.induce S) k f) :
    IsInducedPath G k (fun i => (f i : V)) :=
  ⟨fun _ _ h => hf.1 (Subtype.ext h), fun i j => hf.2 i j⟩

private lemma IsInducedPath.of_mem {S : Set V} {k : ℕ}
    {f : Fin k → V} (hf : IsInducedPath G k f) (hmem : ∀ i, f i ∈ S) :
    IsInducedPath (G.induce S) k (fun i => ⟨f i, hmem i⟩) :=
  ⟨fun _ _ h => hf.1 (congrArg Subtype.val h), fun i j => hf.2 i j⟩

private lemma IsInducedPath.dist_le_natAbs {k : ℕ} {f : Fin k → V}
    (hf : IsInducedPath G k f) (i j : Fin k) :
    G.dist (f i) (f j) ≤ Int.natAbs ((i.val : ℤ) - (j.val : ℤ)) := by
  have hstep : ∀ d : ℕ, ∀ (a b : Fin k), a.val + d = b.val → G.dist (f a) (f b) ≤ d := by
    intro d
    induction d with
    | zero =>
        intro a b hab
        have hEq : a = b := Fin.ext (by omega)
        subst hEq
        simp
    | succ d ih =>
        intro a b hab
        let c : Fin k := ⟨a.val + d, by omega⟩
        have hac : G.dist (f a) (f c) ≤ d := ih a c rfl
        have hcb : G.Adj (f c) (f b) := (hf.2 c b).mpr (Or.inl (by simp [c]; omega))
        have htri : G.dist (f a) (f b) ≤ G.dist (f a) (f c) + G.dist (f c) (f b) :=
          hcb.reachable.dist_triangle_right (f a)
        have h1 : G.dist (f c) (f b) = 1 := dist_eq_one_iff_adj.mpr hcb
        omega
  rcases le_total i.val j.val with hij | hji
  · have h := hstep (j.val - i.val) i j (by omega)
    have hnat : Int.natAbs ((i.val : ℤ) - (j.val : ℤ)) = j.val - i.val := by omega
    omega
  · have h := hstep (i.val - j.val) j i (by omega)
    rw [G.dist_comm] at h
    have hnat : Int.natAbs ((i.val : ℤ) - (j.val : ℤ)) = i.val - j.val := by omega
    omega

private lemma IsInducedPath.isTree_image [DecidableEq V] :
    ∀ {k : ℕ} (_hk : 1 ≤ k) {f : Fin k → V} (_hf : IsInducedPath G k f),
      (G.induce ((Finset.univ.image f : Finset V) : Set V)).IsTree
  | 0, hk, _, _ => by omega
  | 1, _, f, _ => by
      have hset : ((Finset.univ.image f : Finset V) : Set V) = {f 0} := by
        ext x
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩
          rw [Fin.eq_zero i]
        · rintro rfl
          exact ⟨0, rfl⟩
      rw [hset]
      let : Nonempty ↥({f 0} : Set V) := ⟨⟨f 0, by simp⟩⟩
      let : Subsingleton ↥({f 0} : Set V) := ⟨fun a b => Subtype.ext (by
        have ha := Set.mem_singleton_iff.mp a.property
        have hb := Set.mem_singleton_iff.mp b.property
        exact ha.trans hb.symm)⟩
      exact IsTree.of_subsingleton
  | k + 2, _, f, hf => by
      let f' : Fin (k + 1) → V := fun i => f (Fin.castSucc i)
      have hf' : IsInducedPath G (k + 1) f' := hf.take (by omega)
      have hT' := IsInducedPath.isTree_image (by omega : 1 ≤ k + 1) hf'
      let s : Finset V := Finset.univ.image f'
      let z : V := f (Fin.last (k + 1))
      have hz_not : z ∉ s := by
        simp only [s, Finset.mem_image, Finset.mem_univ, true_and, not_exists, f', z]
        intro i hi
        have := hf.1 hi
        have hval := congrArg Fin.val this
        simp at hval
        omega
      let a : V := f' (Fin.last k)
      have ha : a ∈ s := Finset.mem_image_of_mem f' (Finset.mem_univ _)
      have hza : G.Adj z a := (hf.2 (Fin.last (k + 1)) (Fin.castSucc (Fin.last k))).mpr
        (Or.inr (by simp))
      have huniq : ∀ ⦃b : V⦄, b ∈ s → G.Adj z b → b = a := by
        intro b hb hzb
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
        have h := (hf.2 (Fin.last (k + 1)) (Fin.castSucc i)).mp hzb
        simp only [Fin.val_last, Fin.val_castSucc] at h
        have hi : i = Fin.last k := Fin.ext (by simp; omega)
        simp [a, hi]
      have hT := hT'.induce_insert_of_unique_adj hz_not ha hza huniq
      have himg : Finset.univ.image f = insert z s := by
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, s, f', z]
        constructor
        · rintro ⟨i, rfl⟩
          refine Fin.lastCases ?_ ?_ i
          · exact Or.inl rfl
          · intro j
            exact Or.inr ⟨j, rfl⟩
        · rintro (rfl | ⟨j, rfl⟩)
          · exact ⟨Fin.last (k + 1), rfl⟩
          · exact ⟨Fin.castSucc j, rfl⟩
      rwa [himg]

private lemma IsInducedPath.le_largestInducedTreeSize [Fintype V] [DecidableEq V]
    {k : ℕ} (hk : 1 ≤ k) {f : Fin k → V} (hf : IsInducedPath G k f) :
    k ≤ largestInducedTreeSize G := by
  have hT := hf.isTree_image hk
  have hcard : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf.1, Finset.card_fin]
  have hle := card_le_largestInducedTreeSize hT
  omega

private lemma isInducedPath_of_length_eq_dist {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    IsInducedPath G (p.length + 1) (fun i => p.getVert i.val) := by
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hnd := hpath.support_nodup
    have hi : i.val < p.support.length := by rw [Walk.length_support]; exact i.isLt
    have hj : j.val < p.support.length := by rw [Walk.length_support]; exact j.isLt
    have hget : p.support[i.val]'hi = p.support[j.val]'hj := by
      rw [p.support_getElem_eq_getVert hi, p.support_getElem_eq_getVert hj]
      exact hij
    have hfin : (⟨i.val, hi⟩ : Fin p.support.length) = ⟨j.val, hj⟩ :=
      (List.nodup_iff_injective_getElem.mp hnd) hget
    exact Fin.ext (Fin.mk.inj hfin)
  · intro i j
    constructor
    · intro hadj
      by_contra hne
      push Not at hne
      have hne_val : i.val ≠ j.val := by
        intro heq
        dsimp only at hadj
        exact G.irrefl (congrArg p.getVert heq ▸ hadj)
      have hshort : ∀ (a b : Fin (p.length + 1)), a.val + 1 < b.val →
          G.Adj (p.getVert a.val) (p.getVert b.val) → False := by
        intro a b hab hAB
        let w : G.Walk u v := (p.take a.val).append (Walk.cons hAB (p.drop b.val))
        have hdist : G.dist u v ≤ w.length := G.dist_le w
        have hlen : w.length = a.val + 1 + (p.length - b.val) := by
          simp only [w, Walk.length_append, Walk.take_length, Walk.length_cons, Walk.drop_length]
          rw [Nat.min_eq_left (by omega)]
          omega
        omega
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · exact hshort i j (by omega) hadj
      · exact hshort j i (by omega) hadj.symm
    · rintro (h | h)
      · have h1 := p.adj_getVert_succ (i := i.val) (by omega)
        rwa [h] at h1
      · have h1 := p.adj_getVert_succ (i := j.val) (by omega)
        rw [h] at h1
        exact h1.symm

end InducedPaths

section CambySchaudt

variable {V : Type*} [Fintype V] [DecidableEq V]

private def IsCDS (G : SimpleGraph V) (X : Finset V) : Prop :=
  X.Nonempty ∧ (G.induce (X : Set V)).Connected ∧ ∀ v : V, v ∈ X ∨ ∃ x ∈ X, G.Adj x v

private def IsMinimalCDS (G : SimpleGraph V) (X : Finset V) : Prop :=
  IsCDS G X ∧ ∀ x ∈ X, ¬ IsCDS G (X.erase x)

private def IsMinimumCDS (G : SimpleGraph V) (X : Finset V) : Prop :=
  IsCDS G X ∧ ∀ Y : Finset V, IsCDS G Y → X.card ≤ Y.card

private lemma IsMinimumCDS.isMinimal {G : SimpleGraph V} {X : Finset V}
    (h : IsMinimumCDS G X) : IsMinimalCDS G X := by
  refine ⟨h.1, fun x hx hY => ?_⟩
  have hle := h.2 (X.erase x) hY
  have hlt := Finset.card_erase_lt_of_mem hx
  omega

private lemma exists_isMinimumCDS [Nonempty V] {G : SimpleGraph V} (hG : G.Connected) :
    ∃ X : Finset V, IsMinimumCDS G X := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter (fun X => IsCDS G X)
  have huniv : Finset.univ ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.univ_nonempty, ?_, fun v => Or.inl (Finset.mem_univ v)⟩
    have hset : ((Finset.univ : Finset V) : Set V) = Set.univ := by simp
    rw [hset]
    exact (induceUnivIso G).connected_iff.mpr hG
  obtain ⟨X, hXF, hmin⟩ := Finset.exists_min_image F Finset.card ⟨Finset.univ, huniv⟩
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hXF
  refine ⟨X, hXF, fun Y hY => hmin Y ?_⟩
  simp [F, hY]

private lemma exists_private_neighbor_of_non_cut {G : SimpleGraph V} {X : Finset V}
    (hX : IsMinimalCDS G X) {x : V} (hx : x ∈ X)
    (hconn : (G.induce ((X.erase x : Finset V) : Set V)).Connected) :
    ∃ y : V, y ∉ X ∧ G.Adj y x ∧ ∀ z ∈ X, G.Adj y z → z = x := by
  have hne : (X.erase x).Nonempty := by
    obtain ⟨⟨u, hu⟩⟩ := hconn.nonempty
    exact ⟨u, Finset.mem_coe.mp hu⟩
  have hnot := hX.2 x hx
  unfold IsCDS at hnot
  push Not at hnot
  obtain ⟨y, hy_not, hy_nadj⟩ := hnot hne hconn
  have hyx : y ≠ x := by
    intro heq
    obtain ⟨u, hu⟩ := hne
    obtain ⟨p⟩ := hX.1.2.1 ⟨x, Finset.mem_coe.mpr hx⟩
      ⟨u, Finset.mem_coe.mpr (Finset.mem_of_mem_erase hu)⟩
    have hnp : ¬ p.Nil := by
      intro hnil
      have hEq : (⟨x, Finset.mem_coe.mpr hx⟩ : ↥(X : Set V)) =
          ⟨u, Finset.mem_coe.mpr (Finset.mem_of_mem_erase hu)⟩ :=
        Walk.Nil.eq hnil
      exact (Finset.ne_of_mem_erase hu) (congrArg Subtype.val hEq).symm
    let w := p.snd
    have hxw : G.Adj x w.val := p.adj_snd hnp
    have hwx_ne : w.val ≠ x := hxw.ne'
    have hw_er : w.val ∈ X.erase x := Finset.mem_erase.mpr ⟨hwx_ne, Finset.mem_coe.mp w.property⟩
    exact hy_nadj w.val hw_er (heq ▸ hxw.symm)
  have hy_notX : y ∉ X := fun hyX => hy_not (Finset.mem_erase.mpr ⟨hyx, hyX⟩)
  rcases hX.1.2.2 y with hyX | ⟨z, hzX, hzy⟩
  · exact (hy_notX hyX).elim
  · have hzx : z = x := by
      by_contra hne'
      exact hy_nadj z (Finset.mem_erase.mpr ⟨hne', hzX⟩) hzy
    subst hzx
    refine ⟨y, hy_notX, hzy.symm, fun w hwX hyw => ?_⟩
    by_contra hne'
    exact hy_nadj w (Finset.mem_erase.mpr ⟨hne', hwX⟩) hyw.symm

/-- If the first vertex of an induced path `f` (`m ≥ 2`) in a connected graph `H` is a cut vertex
of `H`, then `f` can be extended on the left to an induced path of order `m + 1`. -/
private lemma extend_inducedPath_left_of_cut {W : Type*} {H : SimpleGraph W}
    (hH : H.Connected) {m : ℕ} (hm : 2 ≤ m) {f : Fin m → W} (hf : IsInducedPath H m f)
    (hcut : ¬ (H.induce ({f ⟨0, by omega⟩}ᶜ : Set W)).Connected) :
    ∃ y : W, (∀ i : Fin m, y ≠ f i) ∧ H.Adj y (f ⟨0, by omega⟩) ∧
      ∀ i : Fin m, i.val ≠ 0 → ¬ H.Adj y (f i) := by
  let u : W := f ⟨0, by omega⟩
  let H' := H.induce ({u}ᶜ : Set W)
  have hf1_ne : f ⟨1, by omega⟩ ≠ u := fun h => by
    have := hf.1 h
    have hv := congrArg Fin.val this
    simp at hv
  let v₁ : ↥({u}ᶜ : Set W) := ⟨f ⟨1, by omega⟩, hf1_ne⟩
  have hnot_pre : ¬ H'.Preconnected := fun hpre => hcut (connected_mk v₁ hpre)
  have hnot_all : ¬ ∀ z : ↥({u}ᶜ : Set W), H'.Reachable v₁ z := by
    intro hall
    apply hnot_pre
    intro a b
    exact (hall a).symm.trans (hall b)
  push Not at hnot_all
  obtain ⟨z, hz_not⟩ := hnot_all
  obtain ⟨p, hp_path, -⟩ := hH.exists_path_of_dist u z.val
  have hnp : ¬ p.Nil := fun hnil => z.property (Walk.Nil.eq hnil).symm
  let y : W := p.snd
  have huy : H.Adj u y := p.adj_snd hnp
  have hy_ne : y ≠ u := huy.ne'
  have hy_reach_z : H'.Reachable ⟨y, hy_ne⟩ z := by
    have htail_mem : ∀ w ∈ p.tail.support, w ∈ ({u}ᶜ : Set W) := by
      intro w hw
      have hnd := hp_path.support_nodup
      have hsupp : p.support = u :: p.tail.support := by
        rw [p.support_eq_cons, p.support_tail_of_not_nil hnp]
      rw [hsupp] at hnd
      have hmem : u ∉ p.tail.support := (List.nodup_cons.mp hnd).1
      intro hwu
      subst w
      exact hmem hw
    exact ⟨p.tail.induce ({u}ᶜ : Set W) htail_mem⟩
  have hv₁_not_y : ¬ H'.Reachable v₁ ⟨y, hy_ne⟩ := fun h => hz_not (h.trans hy_reach_z)
  have hf_reach : ∀ i : Fin m, i.val ≠ 0 →
      ∃ hi : f i ≠ u, H'.Reachable v₁ ⟨f i, hi⟩ := by
    intro i hi
    have hne : f i ≠ u := fun h => by
      have := hf.1 h
      have hv := congrArg Fin.val this
      simp at hv
      omega
    refine ⟨hne, ?_⟩
    have hind : ∀ t : ℕ, (ht : t + 1 < m) →
        H'.Reachable v₁ ⟨f ⟨t + 1, ht⟩, fun h => by
          have := hf.1 h; have hv := congrArg Fin.val this; simp at hv⟩ := by
      intro t
      induction t with
      | zero =>
          intro _
          exact Reachable.refl v₁
      | succ t ih =>
          intro ht
          have hprev := ih (by omega)
          have hne1 : f ⟨t + 1, by omega⟩ ∉ ({u} : Set W) := fun h => by
            have := hf.1 h; have hv := congrArg Fin.val this; simp at hv
          have hne2 : f ⟨t + 2, ht⟩ ∉ ({u} : Set W) := fun h => by
            have := hf.1 h; have hv := congrArg Fin.val this; simp at hv
          have hadj : H'.Adj ⟨f ⟨t + 1, by omega⟩, hne1⟩ ⟨f ⟨t + 2, ht⟩, hne2⟩ :=
            hf.adj_succ ht
          exact hprev.trans hadj.reachable
    have hi1 : i.val - 1 + 1 = i.val := by omega
    have h := hind (i.val - 1) (by omega)
    have hEq : (⟨i.val - 1 + 1, by omega⟩ : Fin m) = i := Fin.ext hi1
    simpa [hEq] using h
  refine ⟨y, ?_, huy.symm, ?_⟩
  · intro i hyi
    by_cases hi : i.val = 0
    · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi0] at hyi
      exact hy_ne hyi
    · obtain ⟨hne, hr⟩ := hf_reach i hi
      apply hv₁_not_y
      have hEq : (⟨f i, hne⟩ : ↥({u}ᶜ : Set W)) = ⟨y, hy_ne⟩ := Subtype.ext hyi.symm
      rwa [hEq] at hr
  · intro i hi hadj
    obtain ⟨hne, hr⟩ := hf_reach i hi
    have hstep : H'.Adj ⟨f i, hne⟩ ⟨y, hy_ne⟩ := hadj.symm
    exact hv₁_not_y (hr.trans hstep.reachable)

/-- Camby-Schaudt Lemma 1: if `G` has no induced path of order `k` (`k ≥ 3`) and `X` is a
minimal connected dominating set of `G`, then `G[X]` has no induced path of order `k - 1`. -/
private lemma minimalCDS_path_free {G : SimpleGraph V} {X : Finset V}
    {k : ℕ} (hk : 3 ≤ k) (hfree : ∀ f : Fin k → V, ¬ IsInducedPath G k f)
    (hX : IsMinimalCDS G X) :
    ∀ f : Fin (k - 1) → V, (∀ i, f i ∈ X) → ¬ IsInducedPath G (k - 1) f := by
  classical
  intro f₀ hf₀X hf₀
  let S : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter (fun m =>
    ∃ g : Fin m → V, (∀ i, g i ∈ X) ∧ IsInducedPath G m g)
  have hmem0 : k - 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, f₀, hf₀X, hf₀⟩
    have hle : k - 1 ≤ Fintype.card V := by
      have := Fintype.card_le_of_injective f₀ hf₀.1
      simpa using this
    omega
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S id ⟨k - 1, hmem0⟩
  have hm_ge : k - 1 ≤ m := hmax (k - 1) hmem0
  simp only [S, Finset.mem_filter, Finset.mem_range] at hmS
  obtain ⟨_, g, hgX, hg⟩ := hmS
  have hm2 : 2 ≤ m := by omega
  let H := G.induce (X : Set V)
  let gH : Fin m → ↥(X : Set V) := fun i => ⟨g i, Finset.mem_coe.mpr (hgX i)⟩
  have hgH : IsInducedPath H m gH := hg.of_mem (fun i => Finset.mem_coe.mpr (hgX i))
  have hno_ext : ∀ (h : Fin (m + 1) → V), (∀ i, h i ∈ X) → ¬ IsInducedPath G (m + 1) h := by
    intro h hhX hh
    have hm1S : m + 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, h, hhX, hh⟩
      have hle : m + 1 ≤ Fintype.card V := by
        have := Fintype.card_le_of_injective h hh.1
        simpa using this
      omega
    have := hmax (m + 1) hm1S
    simp at this
  have hnoncut_left : (G.induce ((X.erase (g ⟨0, by omega⟩) : Finset V) : Set V)).Connected := by
    by_contra hcut
    have hcutH : ¬ (H.induce ({gH ⟨0, by omega⟩}ᶜ : Set ↥(X : Set V))).Connected := by
      intro hconn
      apply hcut
      let e : H.induce ({gH ⟨0, by omega⟩}ᶜ : Set ↥(X : Set V)) ≃g
          G.induce ((X.erase (g ⟨0, by omega⟩) : Finset V) : Set V) :=
        { toFun := fun a => ⟨a.val.val, Finset.mem_coe.mpr (Finset.mem_erase.mpr
            ⟨fun heq => a.property (Subtype.ext heq), Finset.mem_coe.mp a.val.property⟩)⟩
          invFun := fun b => ⟨⟨b.val, Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp b.property))⟩,
            fun heq => (Finset.ne_of_mem_erase (Finset.mem_coe.mp b.property)) (congrArg Subtype.val heq)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact e.connected_iff.mp hconn
    obtain ⟨y, hy_not, hy0, hy_rest⟩ := extend_inducedPath_left_of_cut hX.1.2.1 hm2 hgH hcutH
    have hcons := hgH.cons (by omega) hy_not hy0 hy_rest
    exact hno_ext (fun i => (finCons y gH i).val)
      (fun i => Finset.mem_coe.mp (finCons y gH i).property) hcons.map_induce
  have hnoncut_right : (G.induce ((X.erase (g ⟨m - 1, by omega⟩) : Finset V) : Set V)).Connected := by
    by_contra hcut
    let gHr : Fin m → ↥(X : Set V) := fun i => gH i.rev
    have hgHr : IsInducedPath H m gHr := hgH.rev
    have h0rev : gHr ⟨0, by omega⟩ = gH ⟨m - 1, by omega⟩ := by
      dsimp only [gHr]; exact congrArg gH (Fin.ext (by simp))
    have hcutH : ¬ (H.induce ({gHr ⟨0, by omega⟩}ᶜ : Set ↥(X : Set V))).Connected := by
      intro hconn
      apply hcut
      rw [h0rev] at hconn
      let e : H.induce ({gH ⟨m - 1, by omega⟩}ᶜ : Set ↥(X : Set V)) ≃g
          G.induce ((X.erase (g ⟨m - 1, by omega⟩) : Finset V) : Set V) :=
        { toFun := fun a => ⟨a.val.val, Finset.mem_coe.mpr (Finset.mem_erase.mpr
            ⟨fun heq => a.property (Subtype.ext heq), Finset.mem_coe.mp a.val.property⟩)⟩
          invFun := fun b => ⟨⟨b.val, Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp b.property))⟩,
            fun heq => (Finset.ne_of_mem_erase (Finset.mem_coe.mp b.property)) (congrArg Subtype.val heq)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact e.connected_iff.mp hconn
    obtain ⟨y, hy_not, hy0, hy_rest⟩ := extend_inducedPath_left_of_cut hX.1.2.1 hm2 hgHr hcutH
    have hcons := hgHr.cons (by omega) hy_not hy0 hy_rest
    exact hno_ext (fun i => (finCons y gHr i).val)
      (fun i => Finset.mem_coe.mp (finCons y gHr i).property) hcons.map_induce
  obtain ⟨p₁, hp₁_not, hp₁_adj, hp₁_uniq⟩ :=
    exists_private_neighbor_of_non_cut hX (hgX ⟨0, by omega⟩) hnoncut_left
  obtain ⟨p₂, hp₂_not, hp₂_adj, hp₂_uniq⟩ :=
    exists_private_neighbor_of_non_cut hX (hgX ⟨m - 1, by omega⟩) hnoncut_right
  have hp₁_ne_p₂ : p₁ ≠ p₂ := by
    intro heq
    subst heq
    have hEq := hp₁_uniq (g ⟨m - 1, by omega⟩) (hgX ⟨m - 1, by omega⟩) hp₂_adj
    have hidx : (⟨m - 1, by omega⟩ : Fin m) = ⟨0, by omega⟩ := hg.1 hEq
    have hv := congrArg Fin.val hidx
    simp at hv
    omega
  by_cases hadj12 : G.Adj p₁ p₂
  · let g_rev_init : Fin (m - 1) → V := fun i => (fun j => g j.rev) (Fin.castLE (by omega) i)
    have hgrev : IsInducedPath G (m - 1) g_rev_init := hg.rev.take (by omega)
    have h0_eq : g_rev_init ⟨0, by omega⟩ = g ⟨m - 1, by omega⟩ := by
      dsimp only [g_rev_init]; exact congrArg g (Fin.ext (by simp))
    have hp₂_cons : IsInducedPath G (m - 1 + 1) (finCons p₂ g_rev_init) := by
      refine hgrev.cons (by omega) (fun i h => hp₂_not (h ▸ hgX _)) (by rwa [h0_eq]) ?_
      intro i hi hadj
      have hEq := hp₂_uniq _ (hgX _) hadj
      have hidx := hg.1 hEq
      have hv := congrArg Fin.val hidx
      simp [Fin.val_rev] at hv
      omega
    have hp₁_cons : IsInducedPath G (m - 1 + 1 + 1) (finCons p₁ (finCons p₂ g_rev_init)) := by
      refine hp₂_cons.cons (by omega) ?_ ?_ ?_
      · intro i
        refine Fin.cases ?_ ?_ i
        · rw [finCons_zero]; exact hp₁_ne_p₂
        · intro j; rw [finCons_succ]; exact fun h => hp₁_not (h ▸ hgX _)
      · change G.Adj p₁ (finCons p₂ g_rev_init 0)
        rw [finCons_zero]
        exact hadj12
      · intro i
        refine Fin.cases ?_ ?_ i
        · intro hi _; exact (hi rfl).elim
        · intro j _ hadj
          rw [finCons_succ] at hadj
          have hEq := hp₁_uniq _ (hgX _) hadj
          have hidx := hg.1 hEq
          have hv := congrArg Fin.val hidx
          simp [Fin.val_rev] at hv
          omega
    exact hfree _ ((hp₁_cons.cast (by omega : m - 1 + 1 + 1 = m + 1)).take (by omega))
  · have hg1 : IsInducedPath G (m + 1) (finCons p₁ g) :=
      hg.cons (by omega) (fun i h => hp₁_not (h ▸ hgX i)) hp₁_adj
        (fun i hi hadj => by
          have := hp₁_uniq (g i) (hgX i) hadj
          have hidx := hg.1 this
          have hv := congrArg Fin.val hidx
          simp at hv
          omega)
    have hg2 : IsInducedPath G (m + 2) (finSnoc (finCons p₁ g) p₂) := by
      refine hg1.snoc (by omega) ?_ ?_ ?_
      · intro i
        refine Fin.cases ?_ ?_ i
        · rw [finCons_zero]; exact hp₁_ne_p₂.symm
        · intro j; rw [finCons_succ]; exact fun h => hp₂_not (h ▸ hgX j)
      · have hlast : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = (⟨m - 1, by omega⟩ : Fin m).succ := by
          ext; simp; omega
        rw [hlast, finCons_succ]
        exact hp₂_adj
      · intro i
        refine Fin.cases ?_ ?_ i
        · intro _ h0
          rw [finCons_zero] at h0
          exact hadj12 h0.symm
        · intro j hi hj
          rw [finCons_succ] at hj
          have := hp₂_uniq (g j) (hgX j) hj
          have hidx := hg.1 this
          have hv := congrArg Fin.val hidx
          simp at hv
          simp only [Fin.val_succ] at hi
          omega
    exact hfree _ (hg2.take (by omega))

/-- Camby-Schaudt Lemma 2 (substitution): sliding an induced `P_{k-2}` in a minimal CDS `X`
by adding a private neighbor of `f 0` and deleting `f (k - 3)` yields a CDS of the same size. -/
private lemma camby_schaudt_step {G : SimpleGraph V} {X : Finset V}
    {k : ℕ} (hk : 4 ≤ k) (hfree : ∀ f : Fin k → V, ¬ IsInducedPath G k f)
    (hX : IsMinimalCDS G X) {f : Fin (k - 2) → V}
    (hfX : ∀ i, f i ∈ X) (hf : IsInducedPath G (k - 2) f) :
    ∃ y : V, y ∉ X ∧ G.Adj y (f ⟨0, by omega⟩) ∧
      (∀ z ∈ X, G.Adj y z → z = f ⟨0, by omega⟩) ∧
      IsCDS G ((insert y X).erase (f ⟨k - 3, by omega⟩)) ∧
      ((insert y X).erase (f ⟨k - 3, by omega⟩)).card = X.card := by
  have hk2 : 2 ≤ k - 2 := by omega
  have hfreeX := minimalCDS_path_free (by omega) hfree hX
  let H := G.induce (X : Set V)
  let fH : Fin (k - 2) → ↥(X : Set V) := fun i => ⟨f i, Finset.mem_coe.mpr (hfX i)⟩
  have hfH : IsInducedPath H (k - 2) fH := hf.of_mem (fun i => Finset.mem_coe.mpr (hfX i))
  have hnoncut : ∀ (j : Fin (k - 2)), j.val = 0 ∨ j.val = k - 3 →
      (G.induce ((X.erase (f j) : Finset V) : Set V)).Connected := by
    intro j hj
    by_contra hcut
    have hcutH : ¬ (H.induce ({fH j}ᶜ : Set ↥(X : Set V))).Connected := by
      intro hconn
      apply hcut
      let e : H.induce ({fH j}ᶜ : Set ↥(X : Set V)) ≃g
          G.induce ((X.erase (f j) : Finset V) : Set V) :=
        { toFun := fun a => ⟨a.val.val, Finset.mem_coe.mpr (Finset.mem_erase.mpr
            ⟨fun heq => a.property (Subtype.ext heq), Finset.mem_coe.mp a.val.property⟩)⟩
          invFun := fun b => ⟨⟨b.val, Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp b.property))⟩,
            fun heq => (Finset.ne_of_mem_erase (Finset.mem_coe.mp b.property)) (congrArg Subtype.val heq)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact e.connected_iff.mp hconn
    rcases hj with hj0 | hjlast
    · have hjEq : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [hjEq] at hcutH
      obtain ⟨y, hy_not, hy0, hy_rest⟩ := extend_inducedPath_left_of_cut hX.1.2.1 hk2 hfH hcutH
      have hcons := (hfH.cons (by omega) hy_not hy0 hy_rest).map_induce.cast (by omega : k - 2 + 1 = k - 1)
      exact hfreeX _ (fun i => Finset.mem_coe.mp (finCons y fH _).property) hcons
    · let fHr : Fin (k - 2) → ↥(X : Set V) := fun i => fH i.rev
      have hfHr : IsInducedPath H (k - 2) fHr := hfH.rev
      have h0rev : fHr ⟨0, by omega⟩ = fH j := by
        simp only [fHr]; congr 1; ext; simp [Fin.val_rev]; omega
      rw [← h0rev] at hcutH
      obtain ⟨y, hy_not, hy0, hy_rest⟩ := extend_inducedPath_left_of_cut hX.1.2.1 hk2 hfHr hcutH
      have hcons := (hfHr.cons (by omega) hy_not hy0 hy_rest).map_induce.cast (by omega : k - 2 + 1 = k - 1)
      exact hfreeX _ (fun i => Finset.mem_coe.mp (finCons y fHr _).property) hcons
  have hnc0 := hnoncut ⟨0, by omega⟩ (Or.inl rfl)
  have hnclast := hnoncut ⟨k - 3, by omega⟩ (Or.inr rfl)
  obtain ⟨y, hy_not, hy0, hy_uniq⟩ :=
    exists_private_neighbor_of_non_cut hX (hfX ⟨0, by omega⟩) hnc0
  let xlast := f ⟨k - 3, by omega⟩
  let Y := (insert y X).erase xlast
  have hy_ne_last : y ≠ xlast := fun h => hy_not (h ▸ hfX ⟨k - 3, by omega⟩)
  have hf0_ne_last : f ⟨0, by omega⟩ ≠ xlast := fun h => by
    have := hf.1 h; have hv := congrArg Fin.val this; simp at hv; omega
  have hY_eq : Y = insert y (X.erase xlast) := by
    ext z
    simp only [Y, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hz, rfl | hzX⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hz, hzX⟩
    · rintro (rfl | ⟨hz, hzX⟩)
      · exact ⟨hy_ne_last, Or.inl rfl⟩
      · exact ⟨hz, Or.inr hzX⟩
  have hY_card : Y.card = X.card := by
    rw [hY_eq, Finset.card_insert_of_notMem (fun h => hy_not (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem (hfX ⟨k - 3, by omega⟩)]
    have : 1 ≤ X.card := Finset.card_pos.mpr hX.1.1
    omega
  have hY_conn : (G.induce (Y : Set V)).Connected := by
    rw [hY_eq, Finset.coe_insert]
    have hpre1 : (G.induce ({y} : Set V)).Preconnected := .of_subsingleton
    have hpre2 : (G.induce ((X.erase xlast : Finset V) : Set V)).Preconnected := hnclast.preconnected
    have h := connected_induce_union (v := y) (w := f ⟨0, by omega⟩)
      (s := ({y} : Set V)) (t := ((X.erase xlast : Finset V) : Set V))
      hpre1 hpre2 (by simp)
      (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hf0_ne_last, hfX ⟨0, by omega⟩⟩)) hy0
    simpa only [Set.singleton_union] using h
  have hy_in_Y : y ∈ Y := by
    rw [hY_eq]; exact Finset.mem_insert_self y _
  have hY_dom : ∀ v : V, v ∈ Y ∨ ∃ u ∈ Y, G.Adj u v := by
    intro v
    by_contra hnot
    push Not at hnot
    obtain ⟨hv_notY, hv_nadjY⟩ := hnot
    have hv_ne_y : v ≠ y := fun h => hv_notY (h ▸ hy_in_Y)
    have hv_not_er : v ∉ X.erase xlast := fun h => hv_notY (hY_eq ▸ Finset.mem_insert_of_mem h)
    have hv_ne_last : v ≠ xlast := by
      rintro rfl
      have hidx_lt : k - 4 + 1 < k - 2 := by omega
      have hadj_prev : G.Adj (f ⟨k - 4, by omega⟩) (f ⟨k - 4 + 1, hidx_lt⟩) := hf.adj_succ hidx_lt
      have hEq_idx : (⟨k - 4 + 1, hidx_lt⟩ : Fin (k - 2)) = ⟨k - 3, by omega⟩ := Fin.ext (by simp; omega)
      rw [hEq_idx] at hadj_prev
      have hprev_ne : f ⟨k - 4, by omega⟩ ≠ xlast := hadj_prev.ne
      have hprev_Y : f ⟨k - 4, by omega⟩ ∈ Y :=
        hY_eq ▸ Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hprev_ne, hfX ⟨k - 4, by omega⟩⟩)
      exact hv_nadjY _ hprev_Y hadj_prev
    have hv_notX : v ∉ X := fun h => hv_not_er (Finset.mem_erase.mpr ⟨hv_ne_last, h⟩)
    have hv_nadj_y : ¬ G.Adj y v := hv_nadjY y hy_in_Y
    have hv_nadj_er : ∀ u ∈ X.erase xlast, ¬ G.Adj u v :=
      fun u hu => hv_nadjY u (hY_eq ▸ Finset.mem_insert_of_mem hu)
    rcases hX.1.2.2 v with hvX | ⟨u, huX, huv⟩
    · exact hv_notX hvX
    · have hu_last : u = xlast := by
        by_contra hne
        exact hv_nadj_er u (Finset.mem_erase.mpr ⟨hne, huX⟩) huv
      subst hu_last
      have h1 : IsInducedPath G (k - 2 + 1) (finCons y f) :=
        hf.cons (by omega) (fun i h => hy_not (h ▸ hfX i)) hy0
          (fun i hi hadj => by
            have := hy_uniq (f i) (hfX i) hadj
            have hidx := hf.1 this
            have hv := congrArg Fin.val hidx
            simp at hv
            omega)
      have h2 : IsInducedPath G (k - 2 + 2) (finSnoc (finCons y f) v) := by
        refine h1.snoc (by omega) ?_ ?_ ?_
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [finCons_zero]; exact hv_ne_y
          · intro j; rw [finCons_succ]; exact fun h => hv_notX (h ▸ hfX j)
        · have hlast : (⟨k - 2 + 1 - 1, by omega⟩ : Fin (k - 2 + 1)) =
              (⟨k - 3, by omega⟩ : Fin (k - 2)).succ := by ext; simp; omega
          rw [hlast, finCons_succ]
          exact huv.symm
        · intro i
          refine Fin.cases ?_ ?_ i
          · intro _ h0; rw [finCons_zero] at h0; exact hv_nadj_y h0.symm
          · intro j hi hj
            rw [finCons_succ] at hj
            have hj_ne : f j ≠ xlast := fun heq => by
              have hidx := hf.1 heq
              have hv := congrArg Fin.val hidx
              simp at hv
              simp only [Fin.val_succ] at hi
              omega
            exact hv_nadj_er (f j) (Finset.mem_erase.mpr ⟨hj_ne, hfX j⟩) hj.symm
      exact hfree _ (h2.cast (by omega : k - 2 + 2 = k))
  exact ⟨y, hy_not, hy0, hy_uniq, ⟨⟨y, hy_in_Y⟩, hY_conn, hY_dom⟩, hY_card⟩

/-- Camby-Schaudt Theorem: in a connected `P_k`-free graph (`k ≥ 4`), if a minimum CDS `X`
contains an induced `P_{k-2}` given by `f`, then `X` equals the image of `f`. -/
private lemma camby_schaudt {G : SimpleGraph V} {X : Finset V}
    {k : ℕ} (hk : 4 ≤ k) (hfree : ∀ f : Fin k → V, ¬ IsInducedPath G k f)
    (hX : IsMinimumCDS G X) {f : Fin (k - 2) → V}
    (hfX : ∀ i, f i ∈ X) (hf : IsInducedPath G (k - 2) f) :
    X = Finset.univ.image f := by
  let R : Finset V := X \ Finset.univ.image f
  have hstep : ∀ t : ℕ, t ≤ k - 2 →
      ∃ (Y : Finset V) (g : Fin (k - 2) → V),
        IsMinimumCDS G Y ∧ IsInducedPath G (k - 2) g ∧ (∀ i, g i ∈ Y) ∧
        R ⊆ Y ∧
        (∀ j : Fin (k - 2), j.val < t → g j ∉ R ∧ ∀ z ∈ R, ¬ G.Adj (g j) z) ∧
        (∀ j : Fin (k - 2), t ≤ j.val → g j = f ⟨j.val - t, by omega⟩) ∧
        (∀ u ∈ Y, u ∈ R ∨ ∃ j : Fin (k - 2), g j = u) := by
    intro t
    induction t with
    | zero =>
        intro _
        refine ⟨X, f, hX, hf, hfX, Finset.sdiff_subset,
          fun j hj => by omega,
          fun j _ => by simp,
          fun u hu => ?_⟩
        by_cases huf : u ∈ Finset.univ.image f
        · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp huf
          exact Or.inr ⟨j, rfl⟩
        · exact Or.inl (Finset.mem_sdiff.mpr ⟨hu, huf⟩)
    | succ t ih =>
        intro ht
        obtain ⟨Y, g, hYmin, hg, hgY, hRY, hclean, hshift, hcover⟩ := ih (by omega)
        obtain ⟨y, hy_notY, hy0, hy_uniq, hY'_cds, hY'_card⟩ :=
          camby_schaudt_step hk hfree hYmin.isMinimal hgY hg
        let Y' := (insert y Y).erase (g ⟨k - 3, by omega⟩)
        have hY'min : IsMinimumCDS G Y' :=
          ⟨hY'_cds, fun Z hZ => hY'_card ▸ hYmin.2 Z hZ⟩
        let g_init : Fin (k - 3) → V := fun i => g (Fin.castLE (by omega) i)
        have hgi : IsInducedPath G (k - 3) g_init := hg.take (by omega)
        have hEq_len : k - 3 + 1 = k - 2 := by omega
        let g' : Fin (k - 2) → V := fun i => finCons y g_init (Fin.cast hEq_len.symm i)
        have hg'_zero : g' ⟨0, by omega⟩ = y := by
          simp only [g']
          have h0 : Fin.cast hEq_len.symm (⟨0, by omega⟩ : Fin (k - 2)) = 0 := by ext; simp
          rw [h0, finCons_zero]
        have hg'_pos : ∀ (j : Fin (k - 2)), j.val ≠ 0 → g' j = g ⟨j.val - 1, by omega⟩ := by
          intro j hj
          simp only [g']
          have hcast : Fin.cast hEq_len.symm j = (⟨j.val - 1, by omega⟩ : Fin (k - 3)).succ := by
            ext; simp; omega
          rw [hcast, finCons_succ]
          rfl
        have hlast_eq : g ⟨k - 3, by omega⟩ = f ⟨k - 3 - t, by omega⟩ :=
          hshift ⟨k - 3, by omega⟩ (by show t ≤ k - 3; omega)
        have hlast_notR : g ⟨k - 3, by omega⟩ ∉ R := by
          rw [hlast_eq]
          simp only [R, Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and, not_and, not_not]
          intro _
          exact ⟨⟨k - 3 - t, by omega⟩, rfl⟩
        have hy_notR : y ∉ R := fun h => hy_notY (hRY h)
        have hy_nadjR : ∀ z ∈ R, ¬ G.Adj y z := fun z hz hadj => by
          have hz_eq := hy_uniq z (hRY hz) hadj
          by_cases ht0 : t = 0
          · have hg0 : g ⟨0, by omega⟩ = f ⟨0, by omega⟩ := by
              have h0 := hshift ⟨0, by omega⟩ (by show t ≤ 0; omega)
              simpa [ht0] using h0
            rw [hg0] at hz_eq
            have : f ⟨0, by omega⟩ ∈ Finset.univ.image f :=
              Finset.mem_image_of_mem f (Finset.mem_univ _)
            exact (Finset.mem_sdiff.mp hz).2 (hz_eq ▸ this)
          · exact (hclean ⟨0, by omega⟩ (by show 0 < t; omega)).1 (hz_eq ▸ hz)
        have hg'_path : IsInducedPath G (k - 2) g' := by
          have hcons := hgi.cons (y := y) (by omega)
            (fun i h => hy_notY (by rw [h]; exact hgY _))
            (by simpa [g_init] using hy0)
            (fun i hi hadj => by
              have hEq := hy_uniq _ (hgY _) hadj
              have hidx := hg.1 hEq
              have hv := congrArg Fin.val hidx
              simp at hv
              omega)
          exact hcons.cast hEq_len
        have hg'Y' : ∀ i : Fin (k - 2), g' i ∈ Y' := by
          intro i
          by_cases hi : i.val = 0
          · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
            rw [hi0, hg'_zero]
            exact Finset.mem_erase.mpr ⟨fun h => hy_notY (by rw [h]; exact hgY _),
              Finset.mem_insert_self _ _⟩
          · rw [hg'_pos i hi]
            simp only [Y', Finset.mem_erase, Finset.mem_insert]
            refine ⟨fun h => ?_, Or.inr (hgY _)⟩
            have hidx := hg.1 h
            have hv := congrArg Fin.val hidx
            simp at hv
            omega
        have hRY' : R ⊆ Y' := fun z hz => by
          simp only [Y', Finset.mem_erase, Finset.mem_insert]
          exact ⟨fun h => hlast_notR (h.symm ▸ hz), Or.inr (hRY hz)⟩
        refine ⟨Y', g', hY'min, hg'_path, hg'Y', hRY', ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj0 : j.val = 0
          · have hEq0 : j = ⟨0, by omega⟩ := Fin.ext hj0
            rw [hEq0, hg'_zero]
            exact ⟨hy_notR, hy_nadjR⟩
          · rw [hg'_pos j hj0]
            exact hclean ⟨j.val - 1, by omega⟩ (by show j.val - 1 < t; omega)
        · intro j hj
          have hj0 : j.val ≠ 0 := by omega
          rw [hg'_pos j hj0]
          have h := hshift ⟨j.val - 1, by omega⟩ (by show t ≤ j.val - 1; omega)
          have hsub : j.val - 1 - t = j.val - (t + 1) := by omega
          simpa [hsub] using h
        · intro u hu
          simp only [Y', Finset.mem_erase, Finset.mem_insert] at hu
          rcases hu with ⟨hu_ne, rfl | huY⟩
          · exact Or.inr ⟨⟨0, by omega⟩, hg'_zero⟩
          · rcases hcover u huY with huR | ⟨j, rfl⟩
            · exact Or.inl huR
            · have hj_lt : j.val < k - 3 := by
                have hne : j ≠ ⟨k - 3, by omega⟩ := fun h => hu_ne (congrArg g h)
                have hval := Fin.val_ne_of_ne hne
                simp at hval
                omega
              refine Or.inr ⟨⟨j.val + 1, by omega⟩, ?_⟩
              rw [hg'_pos ⟨j.val + 1, by omega⟩ (by simp)]
              simp
  obtain ⟨Y, g, hYmin, _, hgY, hRY, hclean, _, hcover⟩ := hstep (k - 2) le_rfl
  have hR_empty : R = ∅ := by
    by_contra hRne
    obtain ⟨r₀, hr₀⟩ := Finset.nonempty_iff_ne_empty.mpr hRne
    let a : ↥(Y : Set V) := ⟨g ⟨0, by omega⟩, Finset.mem_coe.mpr (hgY ⟨0, by omega⟩)⟩
    let b : ↥(Y : Set V) := ⟨r₀, Finset.mem_coe.mpr (hRY hr₀)⟩
    obtain ⟨p⟩ := hYmin.1.2.1 a b
    let S : Set ↥(Y : Set V) := {u | u.val ∈ R}
    have ha_not : a ∈ Sᶜ := (hclean ⟨0, by omega⟩ (by show 0 < k - 2; omega)).1
    have hb_not : b ∉ Sᶜ := not_not.mpr hr₀
    obtain ⟨d, -, hd_out, hd_in⟩ := p.exists_boundary_dart Sᶜ ha_not hb_not
    have hd_notR : d.fst.val ∉ R := hd_out
    have hd_inR : d.snd.val ∈ R := not_not.mp hd_in
    rcases hcover d.fst.val (Finset.mem_coe.mp d.fst.property) with hR' | ⟨j, hj⟩
    · exact hd_notR hR'
    · exact (hclean j j.isLt).2 d.snd.val hd_inR (hj ▸ d.adj)
  have hsub : X ⊆ Finset.univ.image f := Finset.sdiff_eq_empty_iff_subset.mp hR_empty
  exact Finset.Subset.antisymm hsub (fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hfX i)

/-- Chung / Erdos-Saks-Sos Theorem: every finite nonempty connected graph of radius `r ≥ 1`
contains an induced path on `2 * r - 1` vertices. -/
private theorem chung_inducedPath_ge :
    ∀ (r : ℕ), 1 ≤ r →
      ∀ {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W] (G : SimpleGraph W),
        G.Connected → r ≤ G.radius.toNat →
        ∃ f : Fin (2 * r - 1) → W, IsInducedPath G (2 * r - 1) f := by
  intro r
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
      intro _ W _ _ _ G hG hrad
      rcases r with _ | _ | r
      · refine ⟨fun _ => Classical.arbitrary W, ?_, ?_⟩
        · intro a b _
          exact Fin.ext (by omega)
        · intro a b
          have ha : a.val = 0 := by omega
          have hb : b.val = 0 := by omega
          simp [ha, hb, G.irrefl]
      · obtain ⟨u, huv⟩ := exists_dist_ge_radius_toNat hG (Classical.arbitrary W)
        obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist (Classical.arbitrary W) u
        have hge2 : 2 ≤ G.dist (Classical.arbitrary W) u := le_trans hrad huv
        have hind := isInducedPath_of_length_eq_dist p hp
        exact ⟨_, hind.take (by omega)⟩
      · by_contra hno
        push Not at hno
        have hk4 : 4 ≤ 2 * (r + 3) - 1 := by omega
        obtain ⟨X, hXmin⟩ := exists_isMinimumCDS hG
        let H := G.induce (X : Set W)
        haveI : Nonempty ↥(X : Set W) := by
          obtain ⟨x, hx⟩ := hXmin.1.1
          exact ⟨⟨x, Finset.mem_coe.mpr hx⟩⟩
        have hHconn : H.Connected := hXmin.1.2.1
        have hHrad : H.radius.toNat ≤ r + 1 := by
          by_cases hex : ∃ f : Fin (2 * (r + 2) - 1) → ↥(X : Set W),
              IsInducedPath H (2 * (r + 2) - 1) f
          · obtain ⟨fH, hfH⟩ := hex
            have hEq : 2 * (r + 2) - 1 = 2 * (r + 3) - 1 - 2 := by omega
            let f : Fin (2 * (r + 3) - 1 - 2) → W := fun i => (fH (Fin.cast hEq.symm i)).val
            have hf : IsInducedPath G (2 * (r + 3) - 1 - 2) f := hfH.map_induce.cast hEq
            have hXeq := camby_schaudt hk4 hno hXmin (fun i => Finset.mem_coe.mp (fH _).property) hf
            apply radius_toNat_le_of_exists_forall_dist_le hHconn
            refine ⟨fH ⟨r + 1, by omega⟩, fun v => ?_⟩
            have hvX : v.val ∈ Finset.univ.image f := hXeq ▸ (Finset.mem_coe.mp v.property)
            obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvX
            have hvEq : v = fH (Fin.cast hEq.symm j) := Subtype.ext hj.symm
            rw [hvEq]
            have hd := hfH.dist_le_natAbs ⟨r + 1, by omega⟩ (Fin.cast hEq.symm j)
            have hjlt : (Fin.cast hEq.symm j).val < 2 * (r + 2) - 1 := (Fin.cast hEq.symm j).isLt
            simp only [Fin.val_cast] at hd hjlt
            omega
          · push Not at hex
            by_contra hgt
            push Not at hgt
            obtain ⟨fH, hfH⟩ := ih (by omega) H hHconn (by omega)
            exact hex fH hfH
        obtain ⟨c, hc⟩ := exists_center_forall_dist_le hHconn
        have hGrad_le : G.radius.toNat ≤ r + 2 := by
          apply radius_toNat_le_of_exists_forall_dist_le hG
          refine ⟨c.val, fun v => ?_⟩
          rcases hXmin.1.2.2 v with hvX | ⟨x, hxX, hxv⟩
          · have h1 : G.dist c.val v ≤ H.dist c ⟨v, Finset.mem_coe.mpr hvX⟩ :=
              induced_subgraph_dist_ge (hHconn c ⟨v, Finset.mem_coe.mpr hvX⟩)
            have h2 : H.dist c ⟨v, Finset.mem_coe.mpr hvX⟩ ≤ H.radius.toNat :=
              hc ⟨v, Finset.mem_coe.mpr hvX⟩
            omega
          · have h1 : G.dist c.val x ≤ H.dist c ⟨x, Finset.mem_coe.mpr hxX⟩ :=
              induced_subgraph_dist_ge (hHconn c ⟨x, Finset.mem_coe.mpr hxX⟩)
            have h2 : H.dist c ⟨x, Finset.mem_coe.mpr hxX⟩ ≤ H.radius.toNat :=
              hc ⟨x, Finset.mem_coe.mpr hxX⟩
            have htri := hG.dist_triangle (u := c.val) (v := x) (w := v)
            have h3 : G.dist x v = 1 := dist_eq_one_iff_adj.mpr hxv
            omega
        omega

end CambySchaudt

section Gebendorfer

private def IsCutVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ¬ (G.induce ({v}ᶜ : Set V)).Connected

private def HasCutVertex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ v : V, IsCutVertex G v

private def SameComp {V : Type*} (G : SimpleGraph V) (v x y : V) : Prop :=
  ∃ (hx : x ≠ v) (hy : y ≠ v), (G.induce ({v}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩

private noncomputable def compOf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v x : V) : Finset V :=
  open scoped Classical in
  Finset.univ.filter (fun y => SameComp G v x y)

private lemma mem_compOf_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x y : V} :
    y ∈ compOf G v x ↔ SameComp G v x y := by
  classical
  simp [compOf]

private lemma not_mem_compOf_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v x : V) : v ∉ compOf G v x := by
  rw [mem_compOf_iff]
  rintro ⟨_, hv, _⟩
  exact hv rfl

private lemma self_mem_compOf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x : V} (hx : x ≠ v) : x ∈ compOf G v x := by
  rw [mem_compOf_iff]
  exact ⟨hx, hx, Reachable.refl _⟩

private lemma compOf_eq_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x y : V} (hy : y ∈ compOf G v x) :
    compOf G v y = compOf G v x := by
  obtain ⟨hx, hy', hxy⟩ := mem_compOf_iff.mp hy
  ext z
  simp only [mem_compOf_iff, SameComp]
  exact ⟨fun ⟨_, hz, hyz⟩ => ⟨hx, hz, hxy.trans hyz⟩,
         fun ⟨_, hz, hxz⟩ => ⟨hy', hz, hxy.symm.trans hxz⟩⟩

private lemma compOf_adj_mem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x a b : V}
    (ha : a ∈ compOf G v x) (hb : b ≠ v) (hab : G.Adj a b) :
    b ∈ compOf G v x := by
  obtain ⟨hx, ha', hxa⟩ := mem_compOf_iff.mp ha
  rw [mem_compOf_iff]
  have hstep : (G.induce ({v}ᶜ : Set V)).Adj ⟨a, ha'⟩ ⟨b, hb⟩ := hab
  exact ⟨hx, hb, hxa.trans hstep.reachable⟩

private lemma walk_mem_support_of_compOf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x a b : V}
    (ha : a ∈ compOf G v x) (hb : b ∉ compOf G v x) (p : G.Walk a b) :
    v ∈ p.support := by
  by_contra hv
  have hmem : ∀ w ∈ p.support, w ∈ ({v}ᶜ : Set V) := fun w hw hEq => hv (hEq ▸ hw)
  have hr : (G.induce ({v}ᶜ : Set V)).Reachable ⟨a, hmem a p.start_mem_support⟩
      ⟨b, hmem b p.end_mem_support⟩ := ⟨p.induce ({v}ᶜ : Set V) hmem⟩
  obtain ⟨hx, ha', hxa⟩ := mem_compOf_iff.mp ha
  exact hb (mem_compOf_iff.mpr ⟨hx, hmem b p.end_mem_support, hxa.trans hr⟩)

private lemma dist_eq_add_of_compOf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {v x a b : V}
    (ha : a ∈ compOf G v x) (hb : b ∉ compOf G v x) :
    G.dist a b = G.dist a v + G.dist v b := by
  apply le_antisymm hG.dist_triangle
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a b
  have hv : v ∈ p.support := walk_mem_support_of_compOf ha hb p
  have hsplit := p.take_spec hv
  have hlen : p.length = (p.takeUntil v hv).length + (p.dropUntil v hv).length := by
    rw [← Walk.length_append, hsplit]
  have h1 := G.dist_le (p.takeUntil v hv)
  have h2 := G.dist_le (p.dropUntil v hv)
  omega

private lemma dist_eq_add_of_compOf_right {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {v x a b : V}
    (ha : a ∉ compOf G v x) (hb : b ∈ compOf G v x) :
    G.dist a b = G.dist a v + G.dist v b := by
  have h := dist_eq_add_of_compOf hG hb ha
  rw [G.dist_comm (u := b) (v := a), G.dist_comm (u := b) (v := v),
    G.dist_comm (u := v) (v := a), add_comm] at h
  exact h

private lemma connected_induce_compOf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x : V} (hx : x ≠ v) :
    (G.induce (compOf G v x : Set V)).Connected := by
  refine connected_mk ⟨x, Finset.mem_coe.mpr (self_mem_compOf G hx)⟩ (fun a b => ?_)
  obtain ⟨_, ha', hxa⟩ := mem_compOf_iff.mp (Finset.mem_coe.mp a.property)
  obtain ⟨_, hb', hxb⟩ := mem_compOf_iff.mp (Finset.mem_coe.mp b.property)
  obtain ⟨p⟩ := hxa.symm.trans hxb
  let q : G.Walk a.val b.val := p.map (SimpleGraph.Embedding.induce ({v}ᶜ : Set V)).toHom
  have hq_mem : ∀ w ∈ q.support, w ∈ (compOf G v x : Set V) := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_support_map_induce hw
    have hr : (G.induce ({v}ᶜ : Set V)).Reachable ⟨a.val, ha'⟩ w' := ⟨p.takeUntil w' hw'⟩
    exact Finset.mem_coe.mpr (mem_compOf_iff.mpr ⟨hx, w'.property, hxa.trans hr⟩)
  exact ⟨q.induce (compOf G v x : Set V) hq_mem⟩

private lemma connected_induce_insert_compOf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {v x : V} (hx : x ≠ v) :
    (G.induce ((insert v (compOf G v x) : Finset V) : Set V)).Connected := by
  have hcomp := connected_induce_compOf (G := G) hx
  obtain ⟨p⟩ := hG x v
  obtain ⟨d, -, hd_in, hd_out⟩ := p.exists_boundary_dart (compOf G v x : Set V)
    (Finset.mem_coe.mpr (self_mem_compOf G hx))
    (by simpa using not_mem_compOf_self G v x)
  have hd_eq : d.snd = v := by
    by_contra hne
    exact hd_out (Finset.mem_coe.mpr (compOf_adj_mem (Finset.mem_coe.mp hd_in) hne d.adj))
  rw [Finset.coe_insert]
  have h := connected_induce_union (v := v) (w := d.fst) (s := ({v} : Set V))
    (t := (compOf G v x : Set V)) (.of_subsingleton) hcomp.preconnected (by simp) hd_in
    (hd_eq ▸ d.adj.symm)
  simpa only [Set.singleton_union] using h

private lemma connected_induce_compl_compOf {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {v x : V} :
    (G.induce ((Finset.univ \ compOf G v x : Finset V) : Set V)).Connected := by
  have hv_in : v ∈ (Finset.univ \ compOf G v x : Finset V) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, not_mem_compOf_self G v x⟩
  let v' : ↥((Finset.univ \ compOf G v x : Finset V) : Set V) := ⟨v, Finset.mem_coe.mpr hv_in⟩
  have hreach : ∀ a : ↥((Finset.univ \ compOf G v x : Finset V) : Set V),
      (G.induce ((Finset.univ \ compOf G v x : Finset V) : Set V)).Reachable a v' := by
    intro a
    obtain ⟨p, hp_path, -⟩ := hG.exists_path_of_dist a.val v
    have hp_mem : ∀ w ∈ p.support, w ∈ ((Finset.univ \ compOf G v x : Finset V) : Set V) := by
      intro w hw
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, fun hwC => ?_⟩)
      have ha_notC : a.val ∉ compOf G v x := (Finset.mem_sdiff.mp (Finset.mem_coe.mp a.property)).2
      have hv_in1 : v ∈ (p.takeUntil w hw).support :=
        walk_mem_support_of_compOf (x := x) hwC ha_notC (p.takeUntil w hw).reverse |> fun h => by
          simpa [Walk.support_reverse] using h
      have hv_in2 : v ∈ (p.dropUntil w hw).support := Walk.end_mem_support _
      have hvw : v ≠ w := fun h => not_mem_compOf_self G v x (h ▸ hwC)
      exact not_mem_takeUntil_and_dropUntil_of_isPath hp_path hw hv_in1 hv_in2 hvw
    exact ⟨p.induce _ hp_mem⟩
  exact connected_mk v' (fun a b => (hreach a).trans (hreach b).symm)

private lemma isCutVertex_iff_exists_two_comps {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v : V} :
    IsCutVertex G v ↔ (∀ x : V, x = v) ∨ ∃ x : V, ∃ y : V, x ≠ v ∧ y ≠ v ∧ y ∉ compOf G v x := by
  constructor
  · intro hcut
    by_cases hall : ∀ x : V, x = v
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨x, hx⟩ := hall
      right
      by_contra hno
      push Not at hno
      apply hcut
      refine connected_mk ⟨x, hx⟩ (fun a b => ?_)
      have ha : a.val ∈ compOf G v x := hno x a.val hx a.property
      have hb : b.val ∈ compOf G v x := hno x b.val hx b.property
      obtain ⟨_, _, hxa⟩ := mem_compOf_iff.mp ha
      obtain ⟨_, _, hxb⟩ := mem_compOf_iff.mp hb
      exact hxa.symm.trans hxb
  · rintro (hall | ⟨x, y, hx, hy, hnot⟩)
    · intro hconn
      obtain ⟨⟨z, hz⟩⟩ := hconn.nonempty
      exact hz (hall z)
    · intro hconn
      exact hnot (mem_compOf_iff.mpr ⟨hx, hy, hconn.preconnected ⟨x, hx⟩ ⟨y, hy⟩⟩)

/-- Canonical decomposition of a minimal counterexample at a cut vertex `v`. -/
private structure CutDecomp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (v : V) where
  deep : Finset V
  shal : Finset V
  x₁ : V
  hx₁_mem : x₁ ∈ deep
  hdeep_eq : deep = compOf G v x₁
  hx₁_dist : r ≤ G.dist v x₁
  x₂ : V
  hx₂_mem : x₂ ∈ shal
  hshal_eq : shal = compOf G v x₂
  hshal_bd : ∀ y ∈ shal, G.dist v y ≤ r - 2
  hshal_card : shal.card = G.dist v x₂
  hshal_max : ∀ y ∈ shal, G.dist v y ≤ G.dist v x₂
  hdisj : Disjoint deep shal
  hv_deep : v ∉ deep
  hv_shal : v ∉ shal
  hpart : ∀ u : V, u = v ∨ u ∈ deep ∨ u ∈ shal

private lemma hasCutVertex_of_separated_in_sub {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {v x y : V}
    (hvS : v ∈ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hx_ne : x ≠ v) (hy_ne : y ≠ v)
    (hsep : ∀ p : G.Walk x y, v ∈ p.support) :
    HasCutVertex (G.induce (S : Set V)) := by
  refine ⟨⟨v, Finset.mem_coe.mpr hvS⟩, fun hconn => ?_⟩
  obtain ⟨p⟩ := hconn.preconnected
    ⟨⟨x, Finset.mem_coe.mpr hxS⟩, fun h => hx_ne (congrArg Subtype.val h)⟩
    ⟨⟨y, Finset.mem_coe.mpr hyS⟩, fun h => hy_ne (congrArg Subtype.val h)⟩
  let q1 := p.map (SimpleGraph.Embedding.induce ({⟨v, Finset.mem_coe.mpr hvS⟩}ᶜ : Set ↥(S : Set V))).toHom
  let q2 : G.Walk x y := q1.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
  have hv_q : v ∈ q2.support := hsep q2
  obtain ⟨a, ha_mem, hab⟩ := mem_support_map_induce hv_q
  obtain ⟨b, -, hb_eq⟩ := mem_support_map_induce ha_mem
  exact b.property (hb_eq.trans (Subtype.ext hab))

/-- Helper: build `CutDecomp G r v` for a minimal counterexample `G` at any cut vertex `v`. -/
private lemma exists_cutDecomp {n r : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hr_eq : G.radius.toNat = r) (hr3 : 3 ≤ r) (hn3 : 3 ≤ n)
    (hdist_lt : ∀ u w : Fin n, G.dist u w + 1 < 2 * r)
    (ih_sub : ∀ (S : Finset (Fin n)), S.card < n →
      (G.induce (S : Set (Fin n))).Connected →
      HasCutVertex (G.induce (S : Set (Fin n))) →
      (G.induce (S : Set (Fin n))).radius.toNat < r)
    (v : Fin n) (hvcut : IsCutVertex G v) : Nonempty (CutDecomp G r v) := by
  classical
  have hfar : ∀ u : Fin n, ∃ z : Fin n, r ≤ G.dist u z := fun u => by
    obtain ⟨z, hz⟩ := exists_dist_ge_radius_toNat hG u
    exact ⟨z, hr_eq ▸ hz⟩
  obtain ⟨x₁, hx₁_dist⟩ := hfar v
  have hx₁_ne : x₁ ≠ v := by
    rintro rfl; simp at hx₁_dist; omega
  set C_deep := compOf G v x₁ with hC_deep_def
  have hx₁_mem : x₁ ∈ C_deep := self_mem_compOf G hx₁_ne
  have hshal_bound : ∀ y : Fin n, y ≠ v → y ∉ C_deep → G.dist v y ≤ r - 2 := by
    intro y _ hy_not
    have hadd := dist_eq_add_of_compOf hG (v := v) (x := x₁) hx₁_mem hy_not
    have hlt2 := hdist_lt x₁ y
    rw [G.dist_comm (u := x₁) (v := v)] at hadd
    omega
  let rest := Finset.univ.filter (fun y => y ≠ v ∧ y ∉ C_deep)
  have hrest_ne : rest.Nonempty := by
    rcases isCutVertex_iff_exists_two_comps.mp hvcut with hall | ⟨a, b, ha, hb, hab⟩
    · exfalso
      have : Fintype.card (Fin n) ≤ 1 := by
        haveI : Subsingleton (Fin n) := ⟨fun u w => (hall u).trans (hall w).symm⟩
        exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
      simp at this; omega
    · by_cases ha_in : a ∈ C_deep
      · refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, ?_⟩⟩
        rw [hC_deep_def, ← compOf_eq_of_mem ha_in]; exact hab
      · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, ha_in⟩⟩
  obtain ⟨x₂, hx₂_rest, hx₂_max⟩ := Finset.exists_max_image rest (fun y => G.dist v y) hrest_ne
  have hx₂_ne : x₂ ≠ v := (Finset.mem_filter.mp hx₂_rest).2.1
  have hx₂_notD : x₂ ∉ C_deep := (Finset.mem_filter.mp hx₂_rest).2.2
  set C_shal := compOf G v x₂ with hC_shal_def
  have hx₂_mem : x₂ ∈ C_shal := self_mem_compOf G hx₂_ne
  have hdisj_DS : Disjoint C_deep C_shal := by
    rw [Finset.disjoint_left]
    intro u huD huS
    have hEq : compOf G v x₂ = compOf G v x₁ := (compOf_eq_of_mem huS).symm.trans (compOf_eq_of_mem huD)
    exact hx₂_notD (hC_deep_def ▸ hEq ▸ hx₂_mem)
  -- No third component
  have hno_third : ∀ u ∈ rest, u ∈ C_shal := by
    intro u hu_rest
    by_contra hu_notS
    have hu_ne : u ≠ v := (Finset.mem_filter.mp hu_rest).2.1
    have hu_notD : u ∉ C_deep := (Finset.mem_filter.mp hu_rest).2.2
    set C₃ := compOf G v u with hC₃_def
    have hu_C₃ : u ∈ C₃ := self_mem_compOf G hu_ne
    have hdisj_3D : Disjoint C₃ C_deep := by
      rw [Finset.disjoint_left]; intro z hz3 hzD
      have hEq : compOf G v u = compOf G v x₁ := (compOf_eq_of_mem hz3).symm.trans (compOf_eq_of_mem hzD)
      exact hu_notD (hC_deep_def ▸ hEq ▸ hu_C₃)
    have hdisj_3S : Disjoint C₃ C_shal := by
      rw [Finset.disjoint_left]; intro z hz3 hzS
      have hEq : compOf G v u = compOf G v x₂ := (compOf_eq_of_mem hz3).symm.trans (compOf_eq_of_mem hzS)
      exact hu_notS (hC_shal_def ▸ hEq ▸ hu_C₃)
    let S : Finset (Fin n) := Finset.univ \ C₃
    have hS_card : S.card < n := by
      have hu_notS' : u ∉ S := by simp [S, hu_C₃]
      have hss : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun hEq => by
        have : u ∈ S := by rw [hEq]; exact Finset.mem_univ u
        exact hu_notS' this)
      simpa using Finset.card_lt_card hss
    have hS_conn : (G.induce (S : Set (Fin n))).Connected := connected_induce_compl_compOf hG
    have hv_S : v ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_compOf_self G v u⟩
    have hx₁_S : x₁ ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_right.mp hdisj_3D hx₁_mem⟩
    have hx₂_S : x₂ ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_right.mp hdisj_3S hx₂_mem⟩
    have : Nonempty ↥(S : Set (Fin n)) := ⟨⟨v, Finset.mem_coe.mpr hv_S⟩⟩
    have hS_cut : HasCutVertex (G.induce (S : Set (Fin n))) :=
      hasCutVertex_of_separated_in_sub hv_S hx₁_S hx₂_S hx₁_ne hx₂_ne
        (fun q => walk_mem_support_of_compOf hx₁_mem hx₂_notD q)
    have hrad_lt := ih_sub S hS_card hS_conn hS_cut
    obtain ⟨c, hc⟩ := exists_center_forall_dist_le hS_conn
    have hc_lt : ∀ w : ↥(S : Set (Fin n)), (G.induce (S : Set (Fin n))).dist c w < r :=
      fun w => lt_of_le_of_lt (hc w) hrad_lt
    by_cases hcS : c.val ∈ C_shal
    · have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
        (hS_conn c ⟨x₁, Finset.mem_coe.mpr hx₁_S⟩)
      have h2 := dist_eq_add_of_compOf hG (v := v) (x := x₁) hx₁_mem
        (Finset.disjoint_right.mp hdisj_DS hcS)
      have h3 := hc_lt ⟨x₁, Finset.mem_coe.mpr hx₁_S⟩
      rw [G.dist_comm (u := c.val) (v := x₁)] at h1
      rw [G.dist_comm (u := x₁) (v := v)] at h2
      omega
    · obtain ⟨z, hz⟩ := hfar c.val
      by_cases hz3 : z ∈ C₃
      · have hc_not3 : c.val ∉ C₃ := (Finset.mem_sdiff.mp (Finset.mem_coe.mp c.property)).2
        have hcz : G.dist c.val z = G.dist c.val v + G.dist v z :=
          dist_eq_add_of_compOf_right hG hc_not3 hz3
        have hz_rest : z ∈ rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => not_mem_compOf_self G v u (hC₃_def ▸ h ▸ hz3),
          Finset.disjoint_left.mp hdisj_3D hz3⟩
        have hzx2 : G.dist v z ≤ G.dist v x₂ := hx₂_max z hz_rest
        have hcx2 : G.dist c.val x₂ = G.dist c.val v + G.dist v x₂ :=
          dist_eq_add_of_compOf_right hG hcS hx₂_mem
        have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
          (hS_conn c ⟨x₂, Finset.mem_coe.mpr hx₂_S⟩)
        dsimp only at h1
        have h3 := hc_lt ⟨x₂, Finset.mem_coe.mpr hx₂_S⟩
        omega
      · have hzS : z ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz3⟩
        have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
          (hS_conn c ⟨z, Finset.mem_coe.mpr hzS⟩)
        dsimp only at h1
        have h3 := hc_lt ⟨z, Finset.mem_coe.mpr hzS⟩
        omega
  -- Pendant path card = G.dist v x₂
  have hshal_card : C_shal.card = G.dist v x₂ := by
    obtain ⟨q, hq_path, hq_len⟩ := hG.exists_path_of_dist v x₂
    have hq_sub : q.support.toFinset.erase v ⊆ C_shal := by
      intro w hw
      have hw_ne : w ≠ v := Finset.ne_of_mem_erase hw
      have hw_supp : w ∈ q.support := List.mem_toFinset.mp (Finset.mem_of_mem_erase hw)
      by_contra hw_notS
      have hv_in2 : v ∈ (q.dropUntil w hw_supp).support :=
        walk_mem_support_of_compOf hx₂_mem hw_notS (q.dropUntil w hw_supp).reverse |> fun h => by
          simpa [Walk.support_reverse] using h
      have hv_in1 : v ∈ (q.takeUntil w hw_supp).support := Walk.start_mem_support _
      exact not_mem_takeUntil_and_dropUntil_of_isPath hq_path hw_supp hv_in1 hv_in2 hw_ne.symm
    have hq_er_card : (q.support.toFinset.erase v).card = G.dist v x₂ := by
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr q.start_mem_support),
        List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len]
      omega
    have hle : G.dist v x₂ ≤ C_shal.card := hq_er_card ▸ Finset.card_le_card hq_sub
    apply le_antisymm _ hle
    by_contra hgt
    push Not at hgt
    let Q := q.support.toFinset.erase v
    let S : Finset (Fin n) := (Finset.univ \ C_shal) ∪ Q
    have hdisj_Q : Disjoint (Finset.univ \ C_shal) Q :=
      Finset.disjoint_left.mpr (fun a ha1 ha2 => (Finset.mem_sdiff.mp ha1).2 (hq_sub ha2))
    have hS_card : S.card < n := by
      have hC_le : C_shal.card ≤ n := by simpa using Finset.card_le_univ C_shal
      have hsc : S.card = (Finset.univ \ C_shal).card + Q.card :=
        Finset.card_union_of_disjoint hdisj_Q
      have hsdiff : (Finset.univ \ C_shal).card = n - C_shal.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [hsc, hsdiff, hq_er_card]
      omega
    have hv_S : v ∈ S := Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_compOf_self G v x₂⟩)
    have hx₁_S : x₁ ∈ S := Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hdisj_DS hx₁_mem⟩)
    have hx₂_Q : x₂ ∈ Q := Finset.mem_erase.mpr ⟨hx₂_ne, List.mem_toFinset.mpr q.end_mem_support⟩
    have hx₂_S : x₂ ∈ S := Finset.mem_union_right _ hx₂_Q
    have : Nonempty ↥(S : Set (Fin n)) := ⟨⟨v, Finset.mem_coe.mpr hv_S⟩⟩
    have hS_conn : (G.induce (S : Set (Fin n))).Connected := by
      have h1 := connected_induce_compl_compOf (G := G) (v := v) (x := x₂) hG
      have h2 : (G.induce (q.support.toFinset : Set (Fin n))).Connected := by
        have hset : (q.support.toFinset : Set (Fin n)) = {y | y ∈ q.support} := by ext; simp
        rw [hset]
        exact q.connected_induce_support
      have hsub1 : ((Finset.univ \ C_shal : Finset (Fin n)) : Set (Fin n)) ⊆ (S : Set (Fin n)) :=
        Finset.coe_subset.mpr Finset.subset_union_left
      have hsub2 : (q.support.toFinset : Set (Fin n)) ⊆ (S : Set (Fin n)) := by
        intro z hz
        by_cases hzv : z = v
        · exact hzv ▸ Finset.mem_coe.mpr hv_S
        · exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzv, Finset.mem_coe.mp hz⟩))
      have hv1 : v ∈ ((Finset.univ \ C_shal : Finset (Fin n)) : Set (Fin n)) :=
        Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_compOf_self G v x₂⟩)
      have hv2 : v ∈ (q.support.toFinset : Set (Fin n)) :=
        Finset.mem_coe.mpr (List.mem_toFinset.mpr q.start_mem_support)
      have hto_v : ∀ c : ↥(S : Set (Fin n)),
          (G.induce (S : Set (Fin n))).Reachable c ⟨v, Finset.mem_coe.mpr hv_S⟩ := by
        intro c
        rcases Finset.mem_union.mp (Finset.mem_coe.mp c.property) with hc1 | hc2
        · obtain ⟨p'⟩ := h1.preconnected ⟨c.val, Finset.mem_coe.mpr hc1⟩ ⟨v, hv1⟩
          exact ⟨p'.map (induceMonoHom hsub1)⟩
        · obtain ⟨p'⟩ := h2.preconnected
            ⟨c.val, Finset.mem_coe.mpr (Finset.mem_of_mem_erase hc2)⟩ ⟨v, hv2⟩
          exact ⟨p'.map (induceMonoHom hsub2)⟩
      exact connected_mk ⟨v, Finset.mem_coe.mpr hv_S⟩ (fun a b => (hto_v a).trans (hto_v b).symm)
    have hS_cut : HasCutVertex (G.induce (S : Set (Fin n))) :=
      hasCutVertex_of_separated_in_sub hv_S hx₁_S hx₂_S hx₁_ne hx₂_ne
        (fun q' => walk_mem_support_of_compOf hx₁_mem hx₂_notD q')
    have hrad_lt := ih_sub S hS_card hS_conn hS_cut
    obtain ⟨c, hc⟩ := exists_center_forall_dist_le hS_conn
    have hc_lt : ∀ w : ↥(S : Set (Fin n)), (G.induce (S : Set (Fin n))).dist c w < r :=
      fun w => lt_of_le_of_lt (hc w) hrad_lt
    by_cases hcS : c.val ∈ C_shal
    · have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
        (hS_conn c ⟨x₁, Finset.mem_coe.mpr hx₁_S⟩)
      have h2 := dist_eq_add_of_compOf hG (v := v) (x := x₁) hx₁_mem
        (Finset.disjoint_right.mp hdisj_DS hcS)
      have h3 := hc_lt ⟨x₁, Finset.mem_coe.mpr hx₁_S⟩
      rw [G.dist_comm (u := c.val) (v := x₁)] at h1
      rw [G.dist_comm (u := x₁) (v := v)] at h2
      omega
    · obtain ⟨z, hz⟩ := hfar c.val
      by_cases hzS : z ∈ C_shal
      · have hcz : G.dist c.val z = G.dist c.val v + G.dist v z :=
          dist_eq_add_of_compOf_right hG hcS hzS
        have hz_rest : z ∈ rest := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => not_mem_compOf_self G v x₂ (hC_shal_def ▸ h ▸ hzS),
          Finset.disjoint_right.mp hdisj_DS hzS⟩
        have hzx2 : G.dist v z ≤ G.dist v x₂ := hx₂_max z hz_rest
        have hcx2 : G.dist c.val x₂ = G.dist c.val v + G.dist v x₂ :=
          dist_eq_add_of_compOf_right hG hcS hx₂_mem
        have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
          (hS_conn c ⟨x₂, Finset.mem_coe.mpr hx₂_S⟩)
        dsimp only at h1
        have h3 := hc_lt ⟨x₂, Finset.mem_coe.mpr hx₂_S⟩
        omega
      · have hz_inS : z ∈ S := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzS⟩)
        have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
          (hS_conn c ⟨z, Finset.mem_coe.mpr hz_inS⟩)
        dsimp only at h1
        have h3 := hc_lt ⟨z, Finset.mem_coe.mpr hz_inS⟩
        omega
  exact ⟨{
    deep := C_deep
    shal := C_shal
    x₁ := x₁
    hx₁_mem := hx₁_mem
    hdeep_eq := rfl
    hx₁_dist := hx₁_dist
    x₂ := x₂
    hx₂_mem := hx₂_mem
    hshal_eq := rfl
    hshal_bd := fun y hy => hshal_bound y
      (fun h => not_mem_compOf_self G v x₂ (hC_shal_def ▸ h ▸ hy))
      (Finset.disjoint_right.mp hdisj_DS hy)
    hshal_card := hshal_card
    hshal_max := fun y hy => hx₂_max y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun h => not_mem_compOf_self G v x₂ (hC_shal_def ▸ h ▸ hy),
      Finset.disjoint_right.mp hdisj_DS hy⟩)
    hdisj := hdisj_DS
    hv_deep := not_mem_compOf_self G v x₁
    hv_shal := not_mem_compOf_self G v x₂
    hpart := fun u => by
      by_cases huv : u = v
      · exact Or.inl huv
      · by_cases huD : u ∈ C_deep
        · exact Or.inr (Or.inl huD)
        · exact Or.inr (Or.inr (hno_third u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, huD⟩)))
  }⟩

/-- Helper: attach one pendant path `dv.shal` to an induced tree `T` containing `v`. -/
private lemma attach_one_pendant {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} {v : V} (dv : CutDecomp G r v)
    {T : Finset V} (hT : (G.induce (T : Set V)).IsTree) (hvT : v ∈ T)
    (hadj_only : ∀ u ∈ T, ∀ w ∈ dv.shal, G.Adj u w → u = v)
    (hdisjT : Disjoint T dv.shal) :
    (G.induce ((T ∪ dv.shal : Finset V) : Set V)).IsTree := by
  obtain ⟨q, hq_path, hq_len⟩ := hG.exists_path_of_dist v dv.x₂
  have hq_sub : q.support.toFinset.erase v ⊆ dv.shal := by
    intro w hw
    have hw_ne := Finset.ne_of_mem_erase hw
    have hw_supp := List.mem_toFinset.mp (Finset.mem_of_mem_erase hw)
    by_contra hw_notS
    have hv_in2 : v ∈ (q.dropUntil w hw_supp).support :=
      walk_mem_support_of_compOf (dv.hshal_eq ▸ dv.hx₂_mem) (dv.hshal_eq ▸ hw_notS)
        (q.dropUntil w hw_supp).reverse |> fun h => by simpa [Walk.support_reverse] using h
    have hv_in1 : v ∈ (q.takeUntil w hw_supp).support := Walk.start_mem_support _
    exact not_mem_takeUntil_and_dropUntil_of_isPath hq_path hw_supp hv_in1 hv_in2 hw_ne.symm
  have hq_eq : q.support.toFinset.erase v = dv.shal := by
    apply Finset.eq_of_subset_of_card_le hq_sub
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr q.start_mem_support),
      List.toFinset_card_of_nodup hq_path.support_nodup, q.length_support, hq_len, dv.hshal_card]
    omega
  have hq_ind := isInducedPath_of_length_eq_dist q hq_len
  have hind_ins : ∀ t : ℕ, t ≤ q.length →
      let P_t : Finset V := (Finset.range t).image (fun i => q.getVert (i + 1))
      (G.induce ((T ∪ P_t : Finset V) : Set V)).IsTree := by
    intro t
    induction t with
    | zero =>
        intro _
        dsimp
        rw [Finset.union_empty]
        exact hT
    | succ t ih =>
        intro ht
        have hTprev := ih (by omega)
        let P_t : Finset V := (Finset.range t).image (fun i => q.getVert (i + 1))
        let z := q.getVert (t + 1)
        let a := q.getVert t
        have hz_mem_q : z ∈ q.support.toFinset.erase v := by
          refine Finset.mem_erase.mpr ⟨?_, List.mem_toFinset.mpr (q.getVert_mem_support _)⟩
          intro heq
          have hidx := @hq_ind.1 ⟨t + 1, by omega⟩ ⟨0, by omega⟩ (by simpa [z] using heq)
          have hv := congrArg Fin.val hidx
          simp at hv
        have hz_Shal : z ∈ dv.shal := hq_eq ▸ hz_mem_q
        have hz_notT : z ∉ T := Finset.disjoint_right.mp hdisjT hz_Shal
        have hz_notPt : z ∉ P_t := by
          simp only [P_t, Finset.mem_image, Finset.mem_range, not_exists, not_and]
          intro i hi heq
          have hidx := @hq_ind.1 ⟨i + 1, by omega⟩ ⟨t + 1, by omega⟩ heq
          have hv := congrArg Fin.val hidx
          simp at hv
          omega
        have hz_not : z ∉ T ∪ P_t := by simp [hz_notT, hz_notPt]
        have ha_in : a ∈ T ∪ P_t := by
          cases t with
          | zero =>
              simp only [a, Walk.getVert_zero]
              exact Finset.mem_union_left _ hvT
          | succ t' =>
              exact Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨t', Finset.mem_range.mpr (by omega), rfl⟩)
        have hza : G.Adj z a := (q.adj_getVert_succ (by omega)).symm
        have huniq : ∀ ⦃b : V⦄, b ∈ T ∪ P_t → G.Adj z b → b = a := by
          intro b hb hzb
          rcases Finset.mem_union.mp hb with hbT | hbPt
          · have hbv : b = v := hadj_only b hbT z hz_Shal hzb.symm
            subst hbv
            have h := (hq_ind.2 ⟨t + 1, by omega⟩ ⟨0, by omega⟩).mp (by simpa [z] using hzb)
            simp only at h
            have ht0 : t = 0 := by omega
            subst ht0
            simp [a]
          · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hbPt
            rw [Finset.mem_range] at hi
            have h := (hq_ind.2 ⟨t + 1, by omega⟩ ⟨i + 1, by omega⟩).mp hzb
            simp only at h
            have hit : i + 1 = t := by omega
            simp [a, hit]
        have hTnew := hTprev.induce_insert_of_unique_adj hz_not ha_in hza huniq
        have hEq : insert z (T ∪ P_t) = T ∪ (Finset.range (t + 1)).image (fun i => q.getVert (i + 1)) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_union, P_t, Finset.mem_image, Finset.mem_range, z]
          constructor
          · rintro (rfl | hT' | ⟨i, hi, rfl⟩)
            · exact Or.inr ⟨t, by omega, rfl⟩
            · exact Or.inl hT'
            · exact Or.inr ⟨i, by omega, rfl⟩
          · rintro (hT' | ⟨i, hi, rfl⟩)
            · exact Or.inr (Or.inl hT')
            · by_cases hit : i = t
              · exact Or.inl (hit ▸ rfl)
              · exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
        rwa [hEq] at hTnew
  have hfinal := hind_ins q.length le_rfl
  have hP_eq : (Finset.range q.length).image (fun i => q.getVert (i + 1)) = dv.shal := by
    rw [← hq_eq]
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase, List.mem_toFinset]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, q.getVert_mem_support _⟩
      intro heq
      have hidx := @hq_ind.1 ⟨i + 1, by omega⟩ ⟨0, by omega⟩ (by simpa using heq)
      have hv := congrArg Fin.val hidx
      simp at hv
    · rintro ⟨hx_ne, hx_supp⟩
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx_supp
      rw [q.support_getElem_eq_getVert hi] at hget
      have hi_pos : 0 < i := by
        by_contra hi0
        have : i = 0 := by omega
        subst this
        simp at hget
        exact hx_ne hget.symm
      have hlen := q.length_support
      exact ⟨i - 1, by omega, by simpa [Nat.sub_add_cancel hi_pos] using hget⟩
  rwa [hP_eq] at hfinal

/-- Helper: nestedness of shallow components of `CutDecomp`. -/
private lemma cutDecomp_nested {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} {v w : V}
    (dv : CutDecomp G r v) (dw : CutDecomp G r w)
    (hwS : w ∈ dv.shal) : dw.shal ⊂ dv.shal := by
  have hvw : v ≠ w := fun h => dv.hv_shal (h ▸ hwS)
  have hconn_vD : (G.induce ((insert v dv.deep : Finset V) : Set V)).Connected := by
    rw [dv.hdeep_eq]
    exact connected_induce_insert_compOf hG (fun h => by have hm := dv.hx₁_mem; rw [h] at hm; exact dv.hv_deep hm)
  have hw_not_vD : w ∉ insert v dv.deep := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hvw.symm, Finset.disjoint_right.mp dv.hdisj hwS⟩
  have hv_in_Dw : v ∈ dw.deep := by
    rcases dw.hpart v with hEq | hD | hS
    · exact (hvw hEq).elim
    · exact hD
    · exfalso
      obtain ⟨p⟩ := hconn_vD.preconnected
        ⟨v, Finset.mem_coe.mpr (Finset.mem_insert_self _ _)⟩
        ⟨dv.x₁, Finset.mem_coe.mpr (Finset.mem_insert_of_mem dv.hx₁_mem)⟩
      let q : G.Walk v dv.x₁ := p.map (SimpleGraph.Embedding.induce _).toHom
      have hx₁_Sw : dv.x₁ ∈ dw.shal := by
        by_contra hx₁_not
        have hw_in : w ∈ q.support :=
          walk_mem_support_of_compOf (dw.hshal_eq ▸ hS) (dw.hshal_eq ▸ hx₁_not) q
        obtain ⟨z, -, hz⟩ := mem_support_map_induce hw_in
        exact hw_not_vD (hz ▸ Finset.mem_coe.mp z.property)
      have hwx1 : G.dist w dv.x₁ = G.dist w v + G.dist v dv.x₁ :=
        dist_eq_add_of_compOf hG (dv.hshal_eq ▸ hwS)
          (dv.hshal_eq ▸ Finset.disjoint_left.mp dv.hdisj dv.hx₁_mem)
      have hpos := hG.pos_dist_of_ne hvw.symm
      have hbd := dw.hshal_bd dv.x₁ hx₁_Sw
      have hdist1 := dv.hx₁_dist
      omega
  have hsub : dw.shal ⊆ dv.shal := by
    intro u hu
    by_contra hu_notSv
    have hu_vD : u ∈ insert v dv.deep := by
      rcases dv.hpart u with rfl | hD | hS
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem hD
      · exact (hu_notSv hS).elim
    obtain ⟨p⟩ := hconn_vD.preconnected
      ⟨v, Finset.mem_coe.mpr (Finset.mem_insert_self _ _)⟩
      ⟨u, Finset.mem_coe.mpr hu_vD⟩
    let q : G.Walk v u := p.map (SimpleGraph.Embedding.induce _).toHom
    have hw_in : w ∈ q.support :=
      walk_mem_support_of_compOf (dw.hdeep_eq ▸ hv_in_Dw)
        (dw.hdeep_eq ▸ Finset.disjoint_right.mp dw.hdisj hu) q
    obtain ⟨z, -, hz⟩ := mem_support_map_induce hw_in
    exact hw_not_vD (hz ▸ Finset.mem_coe.mp z.property)
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hEq => dw.hv_shal (hEq ▸ hwS)⟩

/-- Helper: disjointness of shallow components of two distinct vertices in the core `B`. -/
private lemma cutDecomp_disj {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} {v w : V}
    (dv : CutDecomp G r v) (dw : CutDecomp G r w)
    (hvw : v ≠ w) (hw_not_Sv : w ∉ dv.shal) (hv_not_Sw : v ∉ dw.shal) :
    Disjoint dv.shal dw.shal := by
  rw [Finset.disjoint_left]
  intro z hzv hzw
  have hconn_vS : (G.induce ((insert v dv.shal : Finset V) : Set V)).Connected := by
    rw [dv.hshal_eq]
    exact connected_induce_insert_compOf hG (fun h => by have hm := dv.hx₂_mem; rw [h] at hm; exact dv.hv_shal hm)
  obtain ⟨p⟩ := hconn_vS.preconnected
    ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hzv)⟩
    ⟨v, Finset.mem_coe.mpr (Finset.mem_insert_self _ _)⟩
  let q : G.Walk z v := p.map (SimpleGraph.Embedding.induce _).toHom
  have hw_in : w ∈ q.support :=
    walk_mem_support_of_compOf (dw.hshal_eq ▸ hzw) (dw.hshal_eq ▸ hv_not_Sw) q
  obtain ⟨u, -, hu⟩ := mem_support_map_induce hw_in
  rcases Finset.mem_insert.mp (Finset.mem_coe.mp u.property) with hEq | hS
  · exact hvw (hEq.symm.trans hu)
  · exact hw_not_Sv (hu ▸ hS)

/-- Helper: deleting the tip `du.x₂` of a pendant path keeps `G` connected. -/
private lemma connected_erase_tip {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} {u : V} (du : CutDecomp G r u) :
    (G.induce ((Finset.univ.erase du.x₂ : Finset V) : Set V)).Connected := by
  have hu_in : u ∈ Finset.univ.erase du.x₂ :=
    Finset.mem_erase.mpr ⟨fun h => by have hm := du.hx₂_mem; rw [← h] at hm; exact du.hv_shal hm, Finset.mem_univ _⟩
  have hreach : ∀ y : ↥((Finset.univ.erase du.x₂ : Finset V) : Set V),
      (G.induce ((Finset.univ.erase du.x₂ : Finset V) : Set V)).Reachable
        ⟨u, Finset.mem_coe.mpr hu_in⟩ y := by
    intro y
    have hy_ne : y.val ≠ du.x₂ := Finset.ne_of_mem_erase (Finset.mem_coe.mp y.property)
    obtain ⟨p, hp_path, hp_len⟩ := hG.exists_path_of_dist u y.val
    have hxu_not_p : du.x₂ ∉ p.support := by
      intro hmem
      have hlen1 := length_eq_dist_of_subwalk hp_len (Walk.isSubwalk_takeUntil p hmem)
      have hlen2 := length_eq_dist_of_subwalk hp_len (Walk.isSubwalk_dropUntil p hmem)
      have hsplit := congrArg Walk.length (p.take_spec hmem)
      rw [Walk.length_append, hp_len, hlen1, hlen2] at hsplit
      have hpos : 0 < G.dist du.x₂ y.val := hG.pos_dist_of_ne hy_ne.symm
      have hy_notSu : y.val ∉ du.shal := fun hyS => by
        have := du.hshal_max y.val hyS; omega
      have hu_in_drop : u ∈ (p.dropUntil du.x₂ hmem).support :=
        walk_mem_support_of_compOf (du.hshal_eq ▸ du.hx₂_mem) (du.hshal_eq ▸ hy_notSu)
          (p.dropUntil du.x₂ hmem)
      have hu_in_take : u ∈ (p.takeUntil du.x₂ hmem).support := Walk.start_mem_support _
      have hu_ne_xu : u ≠ du.x₂ := fun h => by have hm := du.hx₂_mem; rw [← h] at hm; exact du.hv_shal hm
      exact not_mem_takeUntil_and_dropUntil_of_isPath hp_path hmem hu_in_take hu_in_drop hu_ne_xu
    exact ⟨p.induce _ (fun z hz => Finset.mem_coe.mpr (Finset.mem_erase.mpr
      ⟨fun hEq => hxu_not_p (by rw [hEq] at hz; exact hz), Finset.mem_univ _⟩))⟩
  exact connected_mk ⟨u, Finset.mem_coe.mpr hu_in⟩ (fun a b => (hreach a).symm.trans (hreach b))

set_option maxHeartbeats 800000 in
/-- Gebendorfer's cut-vertex theorem: every finite connected graph with a cut vertex satisfies
`2 * G.radius.toNat ≤ largestInducedTreeSize G`. -/
private theorem cut_vertex_two_mul_radius_le_tree :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected → HasCutVertex G →
      2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G hG hhascut
      classical
      haveI : Nonempty (Fin n) := hG.nonempty
      set r := G.radius.toNat with hr_def
      by_cases hr0 : r = 0
      · omega
      by_cases hr1 : r = 1
      · obtain ⟨v, _⟩ := hhascut
        obtain ⟨x, hx⟩ := exists_dist_ge_radius_toNat hG v
        obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist v x
        have hT := (isInducedPath_of_length_eq_dist p hp).le_largestInducedTreeSize (by omega)
        omega
      by_contra hlt
      push Not at hlt
      have ih_sub : ∀ (S : Finset (Fin n)), S.card < n →
          (G.induce (S : Set (Fin n))).Connected →
          HasCutVertex (G.induce (S : Set (Fin n))) →
          (G.induce (S : Set (Fin n))).radius.toNat < r := by
        intro S hScard hSconn hScut
        let e : ↥(S : Set (Fin n)) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
        let K : SimpleGraph (Fin S.card) := (G.induce (S : Set (Fin n))).map e.toEmbedding
        let iso : G.induce (S : Set (Fin n)) ≃g K := SimpleGraph.Iso.map e _
        have hKconn : K.Connected := iso.connected_iff.mp hSconn
        have hKcut : HasCutVertex K := by
          obtain ⟨w, hwcut⟩ := hScut
          refine ⟨iso w, fun hconn => hwcut ?_⟩
          let e' : (G.induce (S : Set (Fin n))).induce ({w}ᶜ : Set ↥(S : Set (Fin n))) ≃g
              K.induce ({iso w}ᶜ : Set (Fin S.card)) :=
            { toFun := fun a => ⟨iso a.val, fun h => a.property (iso.injective h)⟩
              invFun := fun b => ⟨iso.symm b.val, fun h => b.property (by simpa using congrArg iso h)⟩
              left_inv := fun a => Subtype.ext (iso.symm_apply_apply a.val)
              right_inv := fun b => Subtype.ext (iso.apply_symm_apply b.val)
              map_rel_iff' := fun {a b} => by exact iso.map_rel_iff }
          exact e'.connected_iff.mpr hconn
        have hKbound := ih S.card hScard K hKconn hKcut
        have hKrad : K.radius = (G.induce (S : Set (Fin n))).radius := radius_iso iso
        have hKtree : largestInducedTreeSize K ≤ largestInducedTreeSize (G.induce (S : Set (Fin n))) :=
          tree_iso_le iso
        have hStree : largestInducedTreeSize (G.induce (S : Set (Fin n))) ≤ largestInducedTreeSize G :=
          tree_induce_le S
        rw [hKrad] at hKbound
        omega
      have hdist_lt : ∀ u w : Fin n, G.dist u w + 1 < 2 * r := by
        intro u w
        obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist u w
        have hle := (isInducedPath_of_length_eq_dist p hp).le_largestInducedTreeSize (by omega)
        omega
      have hn3 : 3 ≤ n := by
        by_contra hn2
        obtain ⟨v, _⟩ := hhascut
        obtain ⟨w, hw⟩ := exists_dist_ge_radius_toNat hG v
        obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist v w
        have hlt_len := hp.length_lt
        simp only [Fintype.card_fin] at hlt_len
        omega
      have hr3 : 3 ≤ r := by
        obtain ⟨v, hvcut⟩ := hhascut
        obtain ⟨x₁, hx₁⟩ := exists_dist_ge_radius_toNat hG v
        have hx₁_ne : x₁ ≠ v := by rintro rfl; rw [SimpleGraph.dist_self] at hx₁; omega
        have hshal : ∀ y : Fin n, y ≠ v → y ∉ compOf G v x₁ → G.dist v y ≤ r - 2 := by
          intro y _ hy_not
          have hadd := dist_eq_add_of_compOf hG (v := v) (x := x₁) (self_mem_compOf G hx₁_ne) hy_not
          have hlt2 := hdist_lt x₁ y
          rw [G.dist_comm (u := x₁) (v := v)] at hadd
          omega
        rcases isCutVertex_iff_exists_two_comps.mp hvcut with hall | ⟨a, b, ha, hb, hab⟩
        · have : Fintype.card (Fin n) ≤ 1 := by
            haveI : Subsingleton (Fin n) := ⟨fun u w => (hall u).trans (hall w).symm⟩
            exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
          simp at this; omega
        · by_cases ha_in : a ∈ compOf G v x₁
          · have hb_not : b ∉ compOf G v x₁ := by rw [← compOf_eq_of_mem ha_in]; exact hab
            have h1 := hshal b hb hb_not
            have hpos := hG.pos_dist_of_ne hb.symm
            omega
          · have h1 := hshal a ha ha_in
            have hpos := hG.pos_dist_of_ne ha.symm
            omega
      let D (v : Fin n) (hv : IsCutVertex G v) : CutDecomp G r v :=
        Classical.choice (exists_cutDecomp hG hr_def.symm hr3 hn3 hdist_lt ih_sub v hv)
      let B : Finset (Fin n) := Finset.univ.filter (fun u => ∀ v : Fin n, ∀ hv : IsCutVertex G v, u ∉ (D v hv).shal)
      have hshal_disj_B : ∀ (v w : Fin n) (hv : IsCutVertex G v) (hw : IsCutVertex G w),
          v ∈ B → w ∈ B → v ≠ w → Disjoint (D v hv).shal (D w hw).shal :=
        fun v w hv hw hvB hwB hvw =>
          cutDecomp_disj hG (D v hv) (D w hw) hvw
            ((Finset.mem_filter.mp hwB).2 v hv) ((Finset.mem_filter.mp hvB).2 w hw)
      have hnotB_owner : ∀ u : Fin n, u ∉ B → ∃ v ∈ B, ∃ hv : IsCutVertex G v, u ∈ (D v hv).shal := by
        intro u hu
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hu
        let cand : Finset (Fin n) := Finset.univ.filter (fun v => ∃ hv : IsCutVertex G v, u ∈ (D v hv).shal)
        have hcand_ne : cand.Nonempty := by
          obtain ⟨v, hv, huv⟩ := hu
          exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, huv⟩⟩
        obtain ⟨v, hv_cand, hv_max⟩ := Finset.exists_max_image cand
          (fun v => if hv : IsCutVertex G v then (D v hv).shal.card else 0) hcand_ne
        obtain ⟨hv, huv⟩ := (Finset.mem_filter.mp hv_cand).2
        have hvB : v ∈ B := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw hvSw => ?_⟩
          have hss := cutDecomp_nested hG (D w hw) (D v hv) hvSw
          have huSw : u ∈ (D w hw).shal := hss.subset huv
          have hw_cand : w ∈ cand := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, huSw⟩
          have hle := hv_max w hw_cand
          simp only [hv, hw, dite_true] at hle
          have hlt' := Finset.card_lt_card hss
          omega
        exact ⟨v, hvB, hv, huv⟩
      have hex_cut_B : ∃ v ∈ B, IsCutVertex G v := by
        obtain ⟨v₀, hv₀⟩ := hhascut
        by_cases hv₀B : v₀ ∈ B
        · exact ⟨v₀, hv₀B, hv₀⟩
        · obtain ⟨v, hvB, hv, _⟩ := hnotB_owner v₀ hv₀B
          exact ⟨v, hvB, hv⟩
      have hB_isom : ∀ a ∈ B, ∀ b ∈ B, ∃ p : G.Walk a b,
          p.length = G.dist a b ∧ ∀ w ∈ p.support, w ∈ B := by
        intro a ha b hb
        obtain ⟨p, hp_path, hp_len⟩ := hG.exists_path_of_dist a b
        refine ⟨p, hp_len, fun w hw => ?_⟩
        by_contra hw_notB
        obtain ⟨v, _, hv, hwS⟩ := hnotB_owner w hw_notB
        have ha_notS : a ∉ (D v hv).shal := (Finset.mem_filter.mp ha).2 v hv
        have hb_notS : b ∉ (D v hv).shal := (Finset.mem_filter.mp hb).2 v hv
        have hv1 : v ∈ (p.takeUntil w hw).support :=
          walk_mem_support_of_compOf ((D v hv).hshal_eq ▸ hwS) ((D v hv).hshal_eq ▸ ha_notS)
            (p.takeUntil w hw).reverse |> fun h => by simpa [Walk.support_reverse] using h
        have hv2 : v ∈ (p.dropUntil w hw).support :=
          walk_mem_support_of_compOf ((D v hv).hshal_eq ▸ hwS) ((D v hv).hshal_eq ▸ hb_notS)
            (p.dropUntil w hw)
        have hvw : v ≠ w := fun h => (D v hv).hv_shal (h ▸ hwS)
        exact not_mem_takeUntil_and_dropUntil_of_isPath hp_path hw hv1 hv2 hvw
      have hB_conn : (G.induce (B : Set (Fin n))).Connected := by
        obtain ⟨v₀, hv₀B, _⟩ := hex_cut_B
        refine connected_mk ⟨v₀, Finset.mem_coe.mpr hv₀B⟩ (fun a b => ?_)
        obtain ⟨p, _, hpB⟩ := hB_isom a.val (Finset.mem_coe.mp a.property) b.val (Finset.mem_coe.mp b.property)
        exact ⟨p.induce (B : Set (Fin n)) (fun w hw => Finset.mem_coe.mpr (hpB w hw))⟩
      have hB_dist : ∀ a b : ↥(B : Set (Fin n)), (G.induce (B : Set (Fin n))).dist a b = G.dist a.val b.val := by
        intro a b
        apply le_antisymm
        · obtain ⟨p, hplen, hpB⟩ := hB_isom a.val (Finset.mem_coe.mp a.property) b.val (Finset.mem_coe.mp b.property)
          have h := (G.induce (B : Set (Fin n))).dist_le
            (p.induce (B : Set (Fin n)) (fun w hw => Finset.mem_coe.mpr (hpB w hw)))
          rw [walk_length_induce, hplen] at h
          exact h
        · exact induced_subgraph_dist_ge (hB_conn a b)
      let ell (v : Fin n) : ℕ := if hv : IsCutVertex G v then (D v hv).shal.card else 0
      have hell_le : ∀ v ∈ B, ell v ≤ r - 2 := by
        intro v _
        simp only [ell]
        split_ifs with hv
        · rw [(D v hv).hshal_card]
          exact (D v hv).hshal_bd (D v hv).x₂ (D v hv).hx₂_mem
        · omega
      have hecc_B : ∀ a ∈ B, ∀ u : Fin n, ∃ b ∈ B, G.dist a u ≤ G.dist a b + ell b := by
        intro a ha u
        by_cases huB : u ∈ B
        · exact ⟨u, huB, Nat.le_add_right _ _⟩
        · obtain ⟨b, hbB, hbcut, huS⟩ := hnotB_owner u huB
          have ha_notS : a ∉ (D b hbcut).shal := (Finset.mem_filter.mp ha).2 b hbcut
          have hadd : G.dist a u = G.dist a b + G.dist b u :=
            dist_eq_add_of_compOf_right hG ((D b hbcut).hshal_eq ▸ ha_notS) ((D b hbcut).hshal_eq ▸ huS)
          refine ⟨b, hbB, ?_⟩
          simp only [ell, hbcut, dite_true, (D b hbcut).hshal_card]
          have := (D b hbcut).hshal_max u huS
          omega
      have hex_far_B : ∀ a ∈ B, ∃ b ∈ B, r ≤ G.dist a b + ell b := by
        intro a ha
        obtain ⟨u, hu⟩ := exists_dist_ge_radius_toNat hG a
        obtain ⟨b, hbB, hle⟩ := hecc_B a ha u
        exact ⟨b, hbB, le_trans (hr_def ▸ hu) hle⟩
      have hB_card3 : 3 ≤ B.card := by
        by_contra hB2
        obtain ⟨v₀, hv₀B, hv₀cut⟩ := hex_cut_B
        let dv := D v₀ hv₀cut
        have hex_b : ∃ b ∈ B, b ≠ v₀ ∧ r ≤ G.dist v₀ b + ell b := by
          by_cases hx₁B : dv.x₁ ∈ B
          · exact ⟨dv.x₁, hx₁B, fun h => by have hm := dv.hx₁_mem; rw [h] at hm; exact dv.hv_deep hm,
              by have := dv.hx₁_dist; omega⟩
          · obtain ⟨b, hbB, hbcut, hx₁Sb⟩ := hnotB_owner dv.x₁ hx₁B
            have hbv : b ≠ v₀ := fun h => by
              subst h
              exact Finset.disjoint_left.mp dv.hdisj dv.hx₁_mem hx₁Sb
            have hv₀_notSb : v₀ ∉ (D b hbcut).shal := (Finset.mem_filter.mp hv₀B).2 b hbcut
            have hadd : G.dist v₀ dv.x₁ = G.dist v₀ b + G.dist b dv.x₁ :=
              dist_eq_add_of_compOf_right hG ((D b hbcut).hshal_eq ▸ hv₀_notSb) ((D b hbcut).hshal_eq ▸ hx₁Sb)
            have hle : G.dist b dv.x₁ ≤ ell b := by
              simp only [ell, hbcut, dite_true, (D b hbcut).hshal_card]
              exact (D b hbcut).hshal_max dv.x₁ hx₁Sb
            have := dv.hx₁_dist
            exact ⟨b, hbB, hbv, by omega⟩
        obtain ⟨b, hbB, _, hdist_b⟩ := hex_b
        have hdist1 : G.dist v₀ b ≤ 1 := by
          rw [← hB_dist ⟨v₀, Finset.mem_coe.mpr hv₀B⟩ ⟨b, Finset.mem_coe.mpr hbB⟩]
          obtain ⟨p, hp_path, hp_len⟩ :=
            hB_conn.exists_path_of_dist ⟨v₀, Finset.mem_coe.mpr hv₀B⟩ ⟨b, Finset.mem_coe.mpr hbB⟩
          have hlt' := hp_path.length_lt
          have hcardB : Fintype.card ↥(B : Set (Fin n)) = B.card := Fintype.card_coe B
          omega
        have := hell_le b hbB
        omega
      -- Sub-step 2.3: Every u ∈ B is a cut vertex of G
      have hB_all_cut : ∀ u ∈ B, IsCutVertex G u := by
        by_contra hnot_all
        push Not at hnot_all
        obtain ⟨v₀, hv₀B, hv₀cut⟩ := hex_cut_B
        obtain ⟨u₀, hu₀B, hu₀_nc⟩ := hnot_all
        obtain ⟨p⟩ := hB_conn.preconnected ⟨u₀, Finset.mem_coe.mpr hu₀B⟩ ⟨v₀, Finset.mem_coe.mpr hv₀B⟩
        let S_nc : Set ↥(B : Set (Fin n)) := {x | ¬ IsCutVertex G x.val}
        obtain ⟨d, -, hd_in, hd_out⟩ := p.exists_boundary_dart S_nc hu₀_nc (by simpa [S_nc] using hv₀cut)
        let u := d.fst.val
        let w := d.snd.val
        have huB : u ∈ B := Finset.mem_coe.mp d.fst.property
        have hwB : w ∈ B := Finset.mem_coe.mp d.snd.property
        have hu_nc : ¬ IsCutVertex G u := hd_in
        have hw_cut : IsCutVertex G w := by simpa [S_nc] using hd_out
        have huw : G.Adj u w := d.adj
        let S : Finset (Fin n) := Finset.univ.erase u
        have hS_card : S.card < n := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
          omega
        have hS_conn : (G.induce (S : Set (Fin n))).Connected := by
          have hset : (S : Set (Fin n)) = ({u}ᶜ : Set (Fin n)) := by ext z; simp [S]
          rw [hset]
          exact not_not.mp hu_nc
        have hw_S : w ∈ S := Finset.mem_erase.mpr ⟨huw.ne', Finset.mem_univ _⟩
        have : Nonempty ↥(S : Set (Fin n)) := ⟨⟨w, Finset.mem_coe.mpr hw_S⟩⟩
        have hS_cut : HasCutVertex (G.induce (S : Set (Fin n))) := by
          let dw := D w hw_cut
          have hu_notSw : u ∉ dw.shal := (Finset.mem_filter.mp huB).2 w hw_cut
          have hx₂_ne_u : dw.x₂ ≠ u := fun h => hu_notSw (h ▸ dw.hx₂_mem)
          have hx₂_S : dw.x₂ ∈ S := Finset.mem_erase.mpr ⟨hx₂_ne_u, Finset.mem_univ _⟩
          have hex_z : ∃ z ∈ B, z ≠ u ∧ z ≠ w := by
            have hcard : 0 < ((B.erase u).erase w).card := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huw.ne', hwB⟩),
                Finset.card_erase_of_mem huB]
              omega
            obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
            exact ⟨z, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz),
              Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz), Finset.ne_of_mem_erase hz⟩
          obtain ⟨z, hzB, hzu, hzw⟩ := hex_z
          have hz_S : z ∈ S := Finset.mem_erase.mpr ⟨hzu, Finset.mem_univ _⟩
          have hz_notSw : z ∉ dw.shal := (Finset.mem_filter.mp hzB).2 w hw_cut
          exact hasCutVertex_of_separated_in_sub hw_S hx₂_S hz_S
            (fun h => by have hm := dw.hx₂_mem; rw [h] at hm; exact dw.hv_shal hm) hzw
            (fun qG => walk_mem_support_of_compOf (dw.hshal_eq ▸ dw.hx₂_mem) (dw.hshal_eq ▸ hz_notSw) qG)
        have hrad_lt := ih_sub S hS_card hS_conn hS_cut
        obtain ⟨c₀, hc₀⟩ := exists_center_forall_dist_le hS_conn
        have hc₀_lt : ∀ y : ↥(S : Set (Fin n)), (G.induce (S : Set (Fin n))).dist c₀ y < r :=
          fun y => lt_of_le_of_lt (hc₀ y) hrad_lt
        have hex_cB : ∃ c ∈ B, c ≠ u ∧ ∀ y ∈ S, G.dist c y < r := by
          by_cases hcB : c₀.val ∈ B
          · refine ⟨c₀.val, hcB, Finset.ne_of_mem_erase (Finset.mem_coe.mp c₀.property), fun y hy => ?_⟩
            have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
              (hS_conn c₀ ⟨y, Finset.mem_coe.mpr hy⟩)
            dsimp only at h1
            have h2 := hc₀_lt ⟨y, Finset.mem_coe.mpr hy⟩
            omega
          · obtain ⟨z, hzB, hzcut, hcSz⟩ := hnotB_owner c₀.val hcB
            have hzu : z ≠ u := fun h => hu_nc (h ▸ hzcut)
            refine ⟨z, hzB, hzu, fun y hy => ?_⟩
            by_cases hySz : y ∈ (D z hzcut).shal
            · have := (D z hzcut).hshal_bd y hySz; omega
            · have hadd : G.dist c₀.val y = G.dist c₀.val z + G.dist z y :=
                dist_eq_add_of_compOf hG ((D z hzcut).hshal_eq ▸ hcSz) ((D z hzcut).hshal_eq ▸ hySz)
              have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
                (hS_conn c₀ ⟨y, Finset.mem_coe.mpr hy⟩)
              dsimp only at h1
              have h2 := hc₀_lt ⟨y, Finset.mem_coe.mpr hy⟩
              omega
        obtain ⟨c, hcB, _, hc_lt⟩ := hex_cB
        have hcb_lt : ∀ b ∈ B, b ≠ u → G.dist c b + ell b < r := by
          intro b hbB hbu
          by_cases hbcut : IsCutVertex G b
          · let db := D b hbcut
            have hu_notSb : u ∉ db.shal := (Finset.mem_filter.mp huB).2 b hbcut
            have hy₂_S : db.x₂ ∈ S := Finset.mem_erase.mpr ⟨fun h => hu_notSb (h ▸ db.hx₂_mem), Finset.mem_univ _⟩
            have hc_notSb : c ∉ db.shal := (Finset.mem_filter.mp hcB).2 b hbcut
            have hadd : G.dist c db.x₂ = G.dist c b + G.dist b db.x₂ :=
              dist_eq_add_of_compOf_right hG (db.hshal_eq ▸ hc_notSb) (db.hshal_eq ▸ db.hx₂_mem)
            have hlt' := hc_lt db.x₂ hy₂_S
            have hcard_eq : ell b = G.dist b db.x₂ := by
              simp only [ell, hbcut, dite_true]; exact db.hshal_card
            omega
          · simp only [ell, hbcut, dite_false, add_zero]
            exact hc_lt b (Finset.mem_erase.mpr ⟨hbu, Finset.mem_univ _⟩)
        obtain ⟨b, hbB, hcb_ge⟩ := hex_far_B c hcB
        have hbu : b = u := by
          by_contra hne
          have := hcb_lt b hbB hne
          omega
        rw [hbu] at hcb_ge
        have hell_u : ell u = 0 := by simp [ell, hu_nc]
        have htri : G.dist c u ≤ G.dist c w + G.dist w u := hG.dist_triangle
        have hwu1 : G.dist w u = 1 := dist_eq_one_iff_adj.mpr huw.symm
        have hell_w : 1 ≤ ell w := by
          simp only [ell, hw_cut, dite_true]
          exact Finset.card_pos.mpr ⟨(D w hw_cut).x₂, (D w hw_cut).hx₂_mem⟩
        have hcw_lt := hcb_lt w hwB huw.ne'
        omega
      -- Sub-step 2.4: ell is constant on B
      have hell_const : ∀ u ∈ B, ∀ w ∈ B, ell u = ell w := by
        by_contra hnot_const
        push Not at hnot_const
        obtain ⟨u₀, hu₀B, w₀, hw₀B, hne⟩ := hnot_const
        have hex_edge : ∃ u ∈ B, ∃ w ∈ B, G.Adj u w ∧ ell u < ell w := by
          obtain ⟨u₁, w₁, hu₁B, hw₁B, hlt1⟩ : ∃ u₁ w₁, u₁ ∈ B ∧ w₁ ∈ B ∧ ell u₁ < ell w₁ := by
            rcases lt_or_gt_of_ne hne with h | h
            · exact ⟨u₀, w₀, hu₀B, hw₀B, h⟩
            · exact ⟨w₀, u₀, hw₀B, hu₀B, h⟩
          obtain ⟨p⟩ := hB_conn.preconnected ⟨u₁, Finset.mem_coe.mpr hu₁B⟩ ⟨w₁, Finset.mem_coe.mpr hw₁B⟩
          let S_le : Set ↥(B : Set (Fin n)) := {x | ell x.val ≤ ell u₁}
          have hu₁_in : (⟨u₁, Finset.mem_coe.mpr hu₁B⟩ : ↥(B : Set (Fin n))) ∈ S_le := le_refl (ell u₁)
          have hw₁_out : (⟨w₁, Finset.mem_coe.mpr hw₁B⟩ : ↥(B : Set (Fin n))) ∉ S_le := by
            simp only [S_le, Set.mem_setOf_eq, not_le]; exact hlt1
          obtain ⟨d, -, hd_in, hd_out⟩ := p.exists_boundary_dart S_le hu₁_in hw₁_out
          exact ⟨d.fst.val, Finset.mem_coe.mp d.fst.property, d.snd.val, Finset.mem_coe.mp d.snd.property,
            d.adj, by simp only [S_le, Set.mem_setOf_eq, not_le] at hd_in hd_out; omega⟩
        obtain ⟨u, huB, w, hwB, huw, hlt_ell⟩ := hex_edge
        have hu_cut := hB_all_cut u huB
        have hw_cut := hB_all_cut w hwB
        let du := D u hu_cut
        let dw := D w hw_cut
        let S : Finset (Fin n) := Finset.univ.erase du.x₂
        have hS_conn : (G.induce (S : Set (Fin n))).Connected := connected_erase_tip hG du
        have hS_card : S.card < n := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ du.x₂), Finset.card_univ, Fintype.card_fin]
          omega
        have hdisj_uw := hshal_disj_B u w hu_cut hw_cut huB hwB huw.ne
        have hxu_notSw : du.x₂ ∉ dw.shal := Finset.disjoint_left.mp hdisj_uw du.hx₂_mem
        have hxu_notB : du.x₂ ∉ B := fun h => (Finset.mem_filter.mp h).2 u hu_cut du.hx₂_mem
        have hw_S : w ∈ S := Finset.mem_erase.mpr ⟨fun h => hxu_notB (h ▸ hwB), Finset.mem_univ _⟩
        have hu_S : u ∈ S := Finset.mem_erase.mpr ⟨fun h => hxu_notB (h ▸ huB), Finset.mem_univ _⟩
        have hxw_inS : dw.x₂ ∈ S := Finset.mem_erase.mpr ⟨fun h => hxu_notSw (h ▸ dw.hx₂_mem), Finset.mem_univ _⟩
        have : Nonempty ↥(S : Set (Fin n)) := ⟨⟨w, Finset.mem_coe.mpr hw_S⟩⟩
        have hS_cut : HasCutVertex (G.induce (S : Set (Fin n))) :=
          hasCutVertex_of_separated_in_sub hw_S hxw_inS hu_S
            (fun h => by have hm := dw.hx₂_mem; rw [h] at hm; exact dw.hv_shal hm) huw.ne
            (fun qG => walk_mem_support_of_compOf (dw.hshal_eq ▸ dw.hx₂_mem)
              (dw.hshal_eq ▸ (Finset.mem_filter.mp huB).2 w hw_cut) qG)
        have hrad_lt := ih_sub S hS_card hS_conn hS_cut
        obtain ⟨c₀, hc₀⟩ := exists_center_forall_dist_le hS_conn
        have hc₀_lt : ∀ y : ↥(S : Set (Fin n)), (G.induce (S : Set (Fin n))).dist c₀ y < r :=
          fun y => lt_of_le_of_lt (hc₀ y) hrad_lt
        have hex_cB : ∃ c ∈ B, ∀ y ∈ S, G.dist c y < r := by
          by_cases hcB : c₀.val ∈ B
          · refine ⟨c₀.val, hcB, fun y hy => ?_⟩
            have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
              (hS_conn c₀ ⟨y, Finset.mem_coe.mpr hy⟩)
            dsimp only at h1
            have h2 := hc₀_lt ⟨y, Finset.mem_coe.mpr hy⟩
            omega
          · obtain ⟨z, hzB, hzcut, hcSz⟩ := hnotB_owner c₀.val hcB
            refine ⟨z, hzB, fun y hy => ?_⟩
            by_cases hySz : y ∈ (D z hzcut).shal
            · have := (D z hzcut).hshal_bd y hySz; omega
            · have hadd : G.dist c₀.val y = G.dist c₀.val z + G.dist z y :=
                dist_eq_add_of_compOf hG ((D z hzcut).hshal_eq ▸ hcSz) ((D z hzcut).hshal_eq ▸ hySz)
              have h1 := induced_subgraph_dist_ge (G := G) (S := (S : Set (Fin n)))
                (hS_conn c₀ ⟨y, Finset.mem_coe.mpr hy⟩)
              dsimp only at h1
              have h2 := hc₀_lt ⟨y, Finset.mem_coe.mpr hy⟩
              omega
        obtain ⟨c, hcB, hc_lt⟩ := hex_cB
        have hcb_lt : ∀ b ∈ B, b ≠ u → G.dist c b + ell b < r := by
          intro b hbB hbu
          have hb_cut := hB_all_cut b hbB
          let db := D b hb_cut
          have hdisj_ub := hshal_disj_B u b hu_cut hb_cut huB hbB hbu.symm
          have hy₂_S : db.x₂ ∈ S := Finset.mem_erase.mpr
            ⟨fun h => Finset.disjoint_left.mp hdisj_ub du.hx₂_mem (h.symm ▸ db.hx₂_mem), Finset.mem_univ _⟩
          have hc_notSb : c ∉ db.shal := (Finset.mem_filter.mp hcB).2 b hb_cut
          have hadd : G.dist c db.x₂ = G.dist c b + G.dist b db.x₂ :=
            dist_eq_add_of_compOf_right hG (db.hshal_eq ▸ hc_notSb) (db.hshal_eq ▸ db.hx₂_mem)
          have hlt' := hc_lt db.x₂ hy₂_S
          have hcard_eq : ell b = G.dist b db.x₂ := by
            simp only [ell, hb_cut, dite_true]; exact db.hshal_card
          omega
        obtain ⟨b, hbB, hcb_ge⟩ := hex_far_B c hcB
        have hbu : b = u := by
          by_contra hne'
          have := hcb_lt b hbB hne'
          omega
        rw [hbu] at hcb_ge
        have htri : G.dist c u ≤ G.dist c w + G.dist w u := hG.dist_triangle
        have hwu1 : G.dist w u = 1 := dist_eq_one_iff_adj.mpr huw.symm
        have hcw_lt := hcb_lt w hwB huw.ne'
        omega
      -- Sub-step 2.5: uniform pendant length L ≥ 1
      obtain ⟨v₀, hv₀B, hv₀cut⟩ := hex_cut_B
      let L := ell v₀
      have hL_pos : 1 ≤ L := by
        simp only [L, ell, hv₀cut, dite_true]
        exact Finset.card_pos.mpr ⟨(D v₀ hv₀cut).x₂, (D v₀ hv₀cut).hx₂_mem⟩
      have hell_eq : ∀ b ∈ B, ell b = L := fun b hbB => hell_const b hbB v₀ hv₀B
      let GB := G.induce (B : Set (Fin n))
      have : Nonempty ↥(B : Set (Fin n)) := ⟨⟨v₀, Finset.mem_coe.mpr hv₀B⟩⟩
      set rB := GB.radius.toNat with hrB_def
      have hr_le : r ≤ rB + L := by
        obtain ⟨cB, hcB⟩ := exists_center_forall_dist_le hB_conn
        apply radius_toNat_le_of_exists_forall_dist_le hG
        refine ⟨cB.val, fun u => ?_⟩
        obtain ⟨b, hbB, hle⟩ := hecc_B cB.val (Finset.mem_coe.mp cB.property) u
        have h1 : G.dist cB.val b = GB.dist cB ⟨b, Finset.mem_coe.mpr hbB⟩ :=
          (hB_dist cB ⟨b, Finset.mem_coe.mpr hbB⟩).symm
        have h2 : GB.dist cB ⟨b, Finset.mem_coe.mpr hbB⟩ ≤ rB :=
          hrB_def ▸ hcB ⟨b, Finset.mem_coe.mpr hbB⟩
        have h3 := hell_eq b hbB
        omega
      have hattach_tree : ∀ (TB : Finset (Fin n)), TB ⊆ B → (G.induce (TB : Set (Fin n))).IsTree →
          TB.card * (L + 1) ≤ largestInducedTreeSize G := by
        intro TB hTB_sub hTB_tree
        have hind_U : ∀ (U : Finset (Fin n)), U ⊆ TB →
            let T_U := TB ∪ U.biUnion (fun v => if hv : IsCutVertex G v then (D v hv).shal else ∅)
            (G.induce (T_U : Set (Fin n))).IsTree ∧ T_U.card = TB.card + U.card * L := by
          intro U
          induction U using Finset.induction_on with
          | empty =>
              intro _
              dsimp
              rw [Finset.union_empty]
              exact ⟨hTB_tree, by simp⟩
          | @insert v U hv_notU ihU =>
              intro hsubU
              have hvTB : v ∈ TB := hsubU (Finset.mem_insert_self v U)
              have hvB : v ∈ B := hTB_sub hvTB
              have hv_cut := hB_all_cut v hvB
              have hU_sub : U ⊆ TB := Finset.Subset.trans (Finset.subset_insert v U) hsubU
              obtain ⟨hTU_tree, hTU_card⟩ := ihU hU_sub
              let TU := TB ∪ U.biUnion (fun u => if hu : IsCutVertex G u then (D u hu).shal else ∅)
              have hdisj_v : Disjoint TU (D v hv_cut).shal := by
                rw [Finset.disjoint_left]
                intro x hxTU hxSv
                rcases Finset.mem_union.mp hxTU with hxTB | hxU
                · exact (Finset.mem_filter.mp (hTB_sub hxTB)).2 v hv_cut hxSv
                · obtain ⟨u, huU, hxu⟩ := Finset.mem_biUnion.mp hxU
                  have huB : u ∈ B := hTB_sub (hU_sub huU)
                  have hu_cut := hB_all_cut u huB
                  simp only [hu_cut, dite_true] at hxu
                  have huv : u ≠ v := fun h => hv_notU (h ▸ huU)
                  exact Finset.disjoint_left.mp (hshal_disj_B u v hu_cut hv_cut huB hvB huv) hxu hxSv
              have hadj_only : ∀ x ∈ TU, ∀ y ∈ (D v hv_cut).shal, G.Adj x y → x = v := by
                intro x hxTU y hySv hxy
                by_contra hxv
                have hx_notSv : x ∉ (D v hv_cut).shal := Finset.disjoint_left.mp hdisj_v hxTU
                exact hx_notSv ((D v hv_cut).hshal_eq ▸
                  compOf_adj_mem ((D v hv_cut).hshal_eq ▸ hySv) hxv hxy.symm)
              have hTnew := attach_one_pendant hG (D v hv_cut) hTU_tree
                (Finset.mem_union_left _ hvTB) hadj_only hdisj_v
              have hEq_set : TB ∪ (insert v U).biUnion (fun u => if hu : IsCutVertex G u then (D u hu).shal else ∅) =
                  TU ∪ (D v hv_cut).shal := by
                ext x
                simp only [TU, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert]
                constructor
                · rintro (h | ⟨u, rfl | huU, hxu⟩)
                  · exact Or.inl (Or.inl h)
                  · simp only [hv_cut, dite_true] at hxu; exact Or.inr hxu
                  · exact Or.inl (Or.inr ⟨u, huU, hxu⟩)
                · rintro ((h | ⟨u, huU, hxu⟩) | hxv)
                  · exact Or.inl h
                  · exact Or.inr ⟨u, Or.inr huU, hxu⟩
                  · exact Or.inr ⟨v, Or.inl rfl, by simp only [hv_cut, dite_true]; exact hxv⟩
              have hShal_card : (D v hv_cut).shal.card = L := by
                have := hell_eq v hvB
                simpa [ell, hv_cut] using this
              rw [hEq_set]
              refine ⟨hTnew, ?_⟩
              rw [Finset.card_union_of_disjoint hdisj_v, hTU_card, hShal_card,
                Finset.card_insert_of_notMem hv_notU]
              ring
        obtain ⟨hTfull, hTfull_card⟩ := hind_U TB Finset.Subset.rfl
        have hle := card_le_largestInducedTreeSize hTfull
        rw [hTfull_card] at hle
        have hring : TB.card + TB.card * L = TB.card * (L + 1) := by ring
        omega
      have hrB_pos : 1 ≤ rB := by
        haveI : Nontrivial ↥(B : Set (Fin n)) :=
          Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
        have hne0 : GB.radius ≠ 0 := GB.radius_ne_zero_of_nontrivial
        have hnetop : GB.radius ≠ ⊤ := connected_radius_ne_top hB_conn
        have hto : GB.radius.toNat ≠ 0 := by
          intro h0
          rw [ENat.toNat_eq_zero] at h0
          rcases h0 with h | h <;> contradiction
        omega
      by_cases hrB1 : rB = 1
      · obtain ⟨b, hbB, hbv⟩ : ∃ b ∈ B, b ≠ v₀ := by
          have hpos : 0 < (B.erase v₀).card := by rw [Finset.card_erase_of_mem hv₀B]; omega
          obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
          exact ⟨b, Finset.mem_of_mem_erase hb, Finset.ne_of_mem_erase hb⟩
        obtain ⟨p⟩ := hB_conn.preconnected ⟨v₀, Finset.mem_coe.mpr hv₀B⟩ ⟨b, Finset.mem_coe.mpr hbB⟩
        have hnp : ¬ p.Nil := fun h => hbv (congrArg Subtype.val (Walk.Nil.eq h)).symm
        let w := p.snd
        have hvw : G.Adj v₀ w.val := p.adj_snd hnp
        let TB : Finset (Fin n) := {v₀, w.val}
        have hTB_sub : TB ⊆ B := by
          intro z hz
          simp only [TB, Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hv₀B
          · exact Finset.mem_coe.mp w.property
        have hTB_tree : (G.induce (TB : Set (Fin n))).IsTree := by
          let f : Fin 2 → Fin n := fun i => if i = 0 then v₀ else w.val
          have hf : IsInducedPath G 2 f := by
            refine ⟨?_, ?_⟩
            · intro i j hij
              fin_cases i <;> fin_cases j
              · rfl
              · exact (hvw.ne (by simpa [f] using hij)).elim
              · exact (hvw.ne' (by simpa [f] using hij)).elim
              · rfl
            · intro i j
              fin_cases i <;> fin_cases j <;> simp [f, hvw, hvw.symm]
          have himg : Finset.univ.image f = TB := by
            ext z
            simp only [TB, f, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, Fin.exists_fin_two]
            simp [eq_comm]
          rw [← himg]
          exact hf.isTree_image (by omega)
        have hTB_card : TB.card = 2 := Finset.card_pair hvw.ne
        have hbound := hattach_tree TB hTB_sub hTB_tree
        rw [hTB_card] at hbound
        omega
      · have hrB2 : 2 ≤ rB := by omega
        obtain ⟨fB, hfB⟩ := chung_inducedPath_ge rB (by omega) GB hB_conn (le_of_eq hrB_def)
        let f : Fin (2 * rB - 1) → Fin n := fun i => (fB i).val
        have hf : IsInducedPath G (2 * rB - 1) f := hfB.map_induce
        let TB : Finset (Fin n) := Finset.univ.image f
        have hTB_sub : TB ⊆ B := by
          intro z hz
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_coe.mp (fB i).property
        have hTB_tree : (G.induce (TB : Set (Fin n))).IsTree := hf.isTree_image (by omega)
        have hTB_card : TB.card = 2 * rB - 1 := by
          rw [Finset.card_image_of_injective _ hf.1, Finset.card_fin]
        have hbound := hattach_tree TB hTB_sub hTB_tree
        rw [hTB_card] at hbound
        have halg : 2 * (rB + L) ≤ (2 * rB - 1) * (L + 1) := by
          obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hrB2
          obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hL_pos
          rw [ha, hb]
          have hsub : 2 * (2 + a) - 1 = 3 + 2 * a := by omega
          rw [hsub]
          nlinarith
        omega

end Gebendorfer

end GraphConj84Proof

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture84.conjecture84 := by
  intro α _ _ _ G _ hG hδ
  classical
  let e := Fintype.equivFin α
  let K : SimpleGraph (Fin (Fintype.card α)) := G.map e.toEmbedding
  let iso : G ≃g K := SimpleGraph.Iso.map e G
  have hcard : 2 ≤ Fintype.card α := Fintype.one_lt_card
  have : Nontrivial (Fin (Fintype.card α)) := Fin.nontrivial_iff_two_le.mpr hcard
  have hKconn : K.Connected := iso.connected_iff.mp hG
  have hmin : G.minDegree = K.minDegree := iso.minDegree_eq
  have hrad : K.radius = G.radius := GraphConj84Proof.radius_iso iso
  have htree : largestInducedTreeSize K ≤ largestInducedTreeSize G :=
    GraphConj84Proof.tree_iso_le iso
  have hδ' : 0 < K.minDegree := hmin ▸ hδ
  rw [hmin, ← hrad]
  have hkey : 2 * (K.radius.toNat : ℝ) / (K.minDegree : ℝ) ≤ (largestInducedTreeSize K : ℝ) := by
    rcases Nat.lt_or_ge K.minDegree 2 with hlt | hge
    · have hmin1 : K.minDegree = 1 := by omega
      rw [hmin1]
      simp only [Nat.cast_one, div_one]
      have hnat : 2 * K.radius.toNat ≤ largestInducedTreeSize K := by
        by_cases hn2 : Fintype.card α = 2
        · obtain ⟨v, w, hvw⟩ := exists_pair_ne (Fin (Fintype.card α))
          obtain ⟨p, -, hp⟩ := hKconn.exists_path_of_dist v w
          have hpos : 1 ≤ K.dist v w := hKconn.pos_dist_of_ne hvw
          have hle2 : 2 ≤ largestInducedTreeSize K := by
            have := (GraphConj84Proof.isInducedPath_of_length_eq_dist p hp).le_largestInducedTreeSize (by omega)
            omega
          have hrad1 : K.radius.toNat ≤ 1 := by
            apply GraphConj84Proof.radius_toNat_le_of_exists_forall_dist_le hKconn
            refine ⟨v, fun z => ?_⟩
            obtain ⟨q, hqp, hql⟩ := hKconn.exists_path_of_dist v z
            have := hqp.length_lt
            simp only [Fintype.card_fin] at this
            omega
          omega
        · have hn3 : 3 ≤ Fintype.card α := by omega
          obtain ⟨w, hwdeg⟩ := K.exists_minimal_degree_vertex
          rw [hmin1] at hwdeg
          obtain ⟨u, hwu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hwdeg.symm
          have hcut : GraphConj84Proof.HasCutVertex K := by
            refine ⟨u, fun hconn => ?_⟩
            have hex_z : ∃ z : Fin (Fintype.card α), z ≠ w ∧ z ≠ u := by
              have hcard_er : 0 < (((Finset.univ : Finset (Fin (Fintype.card α))).erase w).erase u).card := by
                rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwu.ne', Finset.mem_univ _⟩),
                  Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
                omega
              obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard_er
              exact ⟨z, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz), Finset.ne_of_mem_erase hz⟩
            obtain ⟨z, hzw, hzu⟩ := hex_z
            obtain ⟨p⟩ := hconn.preconnected ⟨w, hwu.ne⟩ ⟨z, hzu⟩
            have hnp : ¬ p.Nil := fun h => hzw (congrArg Subtype.val (Walk.Nil.eq h)).symm
            have hadj : K.Adj w p.snd.val := p.adj_snd hnp
            exact p.snd.property (huniq p.snd.val hadj)
          exact GraphConj84Proof.cut_vertex_two_mul_radius_le_tree _ K hKconn hcut
      exact_mod_cast hnat
    · obtain ⟨u, hu⟩ := GraphConj84Proof.exists_dist_ge_radius_toNat hKconn (Classical.arbitrary _)
      obtain ⟨p, -, hp⟩ := hKconn.exists_path_of_dist (Classical.arbitrary _) u
      have htree_ge : K.radius.toNat + 1 ≤ largestInducedTreeSize K := by
        have := (GraphConj84Proof.isInducedPath_of_length_eq_dist p hp).le_largestInducedTreeSize (by omega)
        omega
      have hδpos : (0 : ℝ) < (K.minDegree : ℝ) := by exact_mod_cast hδ'
      rw [div_le_iff₀ hδpos]
      have hmul : 2 * K.radius.toNat ≤ largestInducedTreeSize K * K.minDegree := by
        nlinarith
      exact_mod_cast hmul
  exact hkey.trans (by exact_mod_cast htree)
