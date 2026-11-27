import FormalConjectures.WrittenOnTheWallII.GraphConjecture372
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Theorem 2 — Two-Path Tree Bound

For any finite tree `T` on at least two vertices with `T.pathCoverNumber ≤ 2`,
its vertex cover number is at most its total domination number:
`T.vertexCoverNum.toNat ≤ T.totalDominationNumber`.
-/

section

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/- Section 1: Vertex Cover and Bipartite Bounds -/

omit [Fintype α] [DecidableEq α] in
private lemma oma_vertexCoverNum_toNat_le_of_isVertexCover
    (T : SimpleGraph α) (C : Finset α) (hC : T.IsVertexCover (C : Set α)) :
    T.vertexCoverNum.toNat ≤ C.card := by
  have hle : T.vertexCoverNum ≤ (C.card : ℕ∞) := by
    simpa using hC.vertexCoverNum_le
  exact ENat.toNat_le_of_le_natCast hle

omit [Fintype α] in
private lemma oma_exists_vc_subset_le_half
    (T : SimpleGraph α) (hT : T.IsTree) (S : Finset α) :
    ∃ C ⊆ S, 2 * C.card ≤ S.card ∧
      ∀ u ∈ S, ∀ v ∈ S, T.Adj u v → u ∈ C ∨ v ∈ C := by
  classical
  let col : T.Coloring (Fin 2) := hT.coloringTwo
  let C0 : Finset α := S.filter (fun v => col v = 0)
  let C1 : Finset α := S.filter (fun v => col v = 1)
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x <;> simp
  have hpart : C0 ∪ C1 = S := by
    ext v
    simp only [C0, C1, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      rcases hfin2 (col v) with h | h
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, h⟩
  have hdisj : Disjoint C0 C1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    simp only [C0, C1, Finset.mem_filter] at hv0 hv1
    exact zero_ne_one (hv0.2.symm.trans hv1.2)
  have hsum : C0.card + C1.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpart]
  by_cases hle : C0.card ≤ C1.card
  · refine ⟨C0, Finset.filter_subset _ S, by omega, ?_⟩
    intro u hu v hv hadj
    have hne : col u ≠ col v := col.valid hadj
    simp only [C0, Finset.mem_filter]
    rcases hfin2 (col u) with hcu | hcu <;> rcases hfin2 (col v) with hcv | hcv
    · exact False.elim (hne (hcu.trans hcv.symm))
    · exact Or.inl ⟨hu, hcu⟩
    · exact Or.inr ⟨hv, hcv⟩
    · exact False.elim (hne (hcu.trans hcv.symm))
  · refine ⟨C1, Finset.filter_subset _ S, by omega, ?_⟩
    intro u hu v hv hadj
    have hne : col u ≠ col v := col.valid hadj
    simp only [C1, Finset.mem_filter]
    rcases hfin2 (col u) with hcu | hcu <;> rcases hfin2 (col v) with hcv | hcv
    · exact False.elim (hne (hcu.trans hcv.symm))
    · exact Or.inr ⟨hv, hcv⟩
    · exact Or.inl ⟨hu, hcu⟩
    · exact False.elim (hne (hcu.trans hcv.symm))

private lemma oma_tree_vc_le_half
    (T : SimpleGraph α) (hT : T.IsTree) :
    2 * T.vertexCoverNum.toNat ≤ Fintype.card α := by
  obtain ⟨C, -, hcard, hcov⟩ := oma_exists_vc_subset_le_half T hT Finset.univ
  have hvc : T.IsVertexCover (C : Set α) := by
    intro u v hadj
    exact hcov u (Finset.mem_univ u) v (Finset.mem_univ v) hadj
  have hle : T.vertexCoverNum.toNat ≤ C.card :=
    oma_vertexCoverNum_toNat_le_of_isVertexCover T C hvc
  have huniv : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
  omega

/- Section 2: Minimum Path Covers and Total Dominating Sets -/

private lemma oma_exists_min_pathCover
    (T : SimpleGraph α) :
    ∃ P : Finset (Finset α), T.IsPathCover P ∧ P.card = T.pathCoverNumber := by
  let P0 : Finset (Finset α) := Finset.univ.image (fun v : α => ({v} : Finset α))
  have hP0 : T.IsPathCover P0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rcases Finset.mem_image.mp hs1 with ⟨v1, -, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨v2, -, rfl⟩
      have hv : v1 ≠ v2 := fun h => hne (by subst h; rfl)
      exact Finset.disjoint_singleton.mpr hv
    · intro v _
      exact Finset.mem_biUnion.mpr
        ⟨{v}, Finset.mem_image_of_mem _ (Finset.mem_univ v), Finset.mem_singleton_self v⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨v, -, rfl⟩
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  have hne : {k | ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P}.Nonempty :=
    ⟨P0.card, P0, rfl, hP0⟩
  obtain ⟨P, hcard, hP⟩ := Nat.sInf_mem hne
  exact ⟨P, hP, hcard⟩

omit [DecidableEq α] in
private lemma oma_exists_min_tds
    (T : SimpleGraph α) (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  have hnt : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have huniv : T.IsTotalDominating ((Finset.univ : Finset α) : Set α) := by
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hT.connected v w
    have hnil : ¬p.Nil := Walk.not_nil_of_ne hw.symm
    exact ⟨p.snd, Finset.mem_univ _, p.adj_snd hnil⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨(Finset.univ : Finset α).card, Finset.univ, ⟨huniv, rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

/- Section 3: Path Chordlessness, Neighbor Bounds, and Splitting -/

omit [Fintype α] [DecidableEq α] in
private lemma oma_mem_support_append_iff
    (T : SimpleGraph α) {u v w z : α} (p1 : T.Walk u v) (p2 : T.Walk v w) :
    z ∈ (p1.append p2).support ↔ z ∈ p1.support ∨ z ∈ p2.support := by
  rw [Walk.support_append, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)
  · rintro (h | h)
    · exact Or.inl h
    · cases p2 with
      | nil =>
        simp only [Walk.support_nil, List.mem_singleton] at h
        exact Or.inl (h ▸ p1.end_mem_support)
      | cons hadj tail =>
        simp only [Walk.support_cons, List.mem_cons, List.tail_cons] at h ⊢
        rcases h with rfl | h'
        · exact Or.inl p1.end_mem_support
        · exact Or.inr h'

omit [Fintype α] [DecidableEq α] in
private lemma oma_isPath_walk_in_support
    (T : SimpleGraph α) {a b x y : α} {p : T.Walk a b} (hp : p.IsPath)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ r : T.Walk x y, r.IsPath ∧ ∀ z ∈ r.support, z ∈ p.support := by
  obtain ⟨q1, q2, hq1, hq2, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hx
  have hy' : y ∈ q1.support ∨ y ∈ q2.support := by
    have : y ∈ (q1.append q2).support := hp_eq ▸ hy
    exact (oma_mem_support_append_iff T q1 q2).mp this
  rcases hy' with hy1 | hy2
  · obtain ⟨s1, s2, -, hs2, hq1_eq⟩ := hq1.mem_support_iff_exists_append.mp hy1
    refine ⟨s2.reverse, hs2.reverse, fun z hz => ?_⟩
    have hz_s2 : z ∈ s2.support := by simpa using hz
    have hz_q1 : z ∈ q1.support := by
      rw [hq1_eq]
      exact (oma_mem_support_append_iff T s1 s2).mpr (Or.inr hz_s2)
    rw [hp_eq]
    exact (oma_mem_support_append_iff T q1 q2).mpr (Or.inl hz_q1)
  · obtain ⟨s1, s2, hs1, -, hq2_eq⟩ := hq2.mem_support_iff_exists_append.mp hy2
    refine ⟨s1, hs1, fun z hz => ?_⟩
    have hz_q2 : z ∈ q2.support := by
      rw [hq2_eq]
      exact (oma_mem_support_append_iff T s1 s2).mpr (Or.inl hz)
    rw [hp_eq]
    exact (oma_mem_support_append_iff T q1 q2).mpr (Or.inr hz_q2)

private lemma oma_path_neighbor_split
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {a b x : α} {p : T.Walk a b} (hp : p.IsPath) (hx : x ∈ p.support) :
    (T.neighborFinset x ∩ p.support.toFinset).card ≤ 2 ∧
      ((T.neighborFinset x ∩ p.support.toFinset).card = 2 →
        ∃ A B : Finset α, ∃ aA ∈ A, ∃ aB ∈ B,
          Disjoint A B ∧ x ∉ A ∧ x ∉ B ∧ A ∪ B = p.support.toFinset.erase x ∧
          (∀ u ∈ A, ∀ v ∈ B, ¬ T.Adj u v) ∧
          (T.Adj x aA ∧ ∀ y ∈ A, T.Adj x y → y = aA) ∧
          (T.Adj x aB ∧ ∀ y ∈ B, T.Adj x y → y = aB)) := by
  obtain ⟨q, r, hq, hr, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hx
  have hmem_qr : ∀ {y : α}, y ∈ p.support → y ∈ q.support ∨ y ∈ r.support := by
    intro y hy
    have : y ∈ (q.append r).support := hp_eq ▸ hy
    exact (oma_mem_support_append_iff T q r).mp this
  have hsub_pair : T.neighborFinset x ∩ p.support.toFinset ⊆ {q.penultimate, r.snd} := by
    intro y hy
    rw [Finset.mem_inter, mem_neighborFinset, List.mem_toFinset] at hy
    rcases hmem_qr hy.2 with hyq | hyr
    · have hy_eq : y = q.penultimate :=
        hT.isAcyclic.eq_penultimate_of_adj_end hq hy.1 hyq
      simp [hy_eq]
    · have hy_eq : y = r.snd :=
        hT.isAcyclic.eq_snd_of_adj_start hr hy.1 hyr
      simp [hy_eq]
  have hcard_le : (T.neighborFinset x ∩ p.support.toFinset).card ≤ 2 :=
    (Finset.card_le_card hsub_pair).trans Finset.card_le_two
  refine ⟨hcard_le, fun hcard_eq => ?_⟩
  have hq_not_nil : ¬q.Nil := by
    intro hqnil
    have hqsupp : q.support = [a] := Walk.nil_iff_support_eq.mp hqnil
    have hax : a = x := by cases hqnil; rfl
    have hsub1 : T.neighborFinset x ∩ p.support.toFinset ⊆ {r.snd} := by
      intro y hy
      rw [Finset.mem_inter, mem_neighborFinset, List.mem_toFinset] at hy
      rcases hmem_qr hy.2 with hyq | hyr
      · rw [hqsupp, hax, List.mem_singleton] at hyq
        exact False.elim (hy.1.ne hyq.symm)
      · exact Finset.mem_singleton.mpr (hT.isAcyclic.eq_snd_of_adj_start hr hy.1 hyr)
    have hle1 : (T.neighborFinset x ∩ p.support.toFinset).card ≤ 1 :=
      (Finset.card_le_card hsub1).trans (by simp)
    omega
  have hr_not_nil : ¬r.Nil := by
    intro hrnil
    have hrsupp : r.support = [x] := Walk.nil_iff_support_eq.mp hrnil
    have hsub1 : T.neighborFinset x ∩ p.support.toFinset ⊆ {q.penultimate} := by
      intro y hy
      rw [Finset.mem_inter, mem_neighborFinset, List.mem_toFinset] at hy
      rcases hmem_qr hy.2 with hyq | hyr
      · exact Finset.mem_singleton.mpr (hT.isAcyclic.eq_penultimate_of_adj_end hq hy.1 hyq)
      · rw [hrsupp, List.mem_singleton] at hyr
        exact False.elim (hy.1.ne hyr.symm)
    have hle1 : (T.neighborFinset x ∩ p.support.toFinset).card ≤ 1 :=
      (Finset.card_le_card hsub1).trans (by simp)
    omega
  let A : Finset α := q.support.toFinset.erase x
  let B : Finset α := r.support.toFinset.erase x
  have haA_adj : T.Adj x q.penultimate := (q.adj_penultimate hq_not_nil).symm
  have haA_mem : q.penultimate ∈ A := by
    rw [Finset.mem_erase, List.mem_toFinset]
    exact ⟨haA_adj.ne.symm, List.mem_of_mem_dropLast (q.penultimate_mem_dropLast_support hq_not_nil)⟩
  have haB_adj : T.Adj x r.snd := r.adj_snd hr_not_nil
  have haB_mem : r.snd ∈ B := by
    rw [Finset.mem_erase, List.mem_toFinset]
    exact ⟨haB_adj.ne.symm, List.mem_of_mem_tail (r.snd_mem_tail_support hr_not_nil)⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rw [Finset.mem_erase, List.mem_toFinset] at hzA hzB
    have hqr_path : (q.append r).IsPath := hp_eq ▸ hp
    exact hqr_path.ne_of_mem_support_of_append hzB.1 hzA.2 hzB.2 rfl
  have hpart : A ∪ B = p.support.toFinset.erase x := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_erase, List.mem_toFinset, hp_eq,
      oma_mem_support_append_iff]
    tauto
  have hno_edge : ∀ u ∈ A, ∀ v ∈ B, ¬ T.Adj u v := by
    intro u hu v hv hadj
    rw [Finset.mem_erase, List.mem_toFinset] at hu hv
    obtain ⟨q1, q2, -, -, hq_eq⟩ := hq.mem_support_iff_exists_append.mp hu.2
    obtain ⟨r1, r2, -, -, hr_eq⟩ := hr.mem_support_iff_exists_append.mp hv.2
    have hfull_path : (q1.append ((q2.append r1).append r2)).IsPath := by
      have hp' : ((q1.append q2).append (r1.append r2)).IsPath := by
        rw [← hq_eq, ← hr_eq, ← hp_eq]
        exact hp
      simpa [Walk.append_assoc] using hp'
    have hmid_path : (q2.append r1).IsPath :=
      hfull_path.of_append_right.of_append_left
    have hpath_eq : q2.append r1 = hadj.toWalk :=
      Subtype.ext_iff.mp ((hT.isAcyclic.subsingleton_path u v).elim
        ⟨q2.append r1, hmid_path⟩ ⟨hadj.toWalk, hadj.isPath_toWalk⟩)
    have hx_mid : x ∈ (q2.append r1).support :=
      (oma_mem_support_append_iff T q2 r1).mpr (Or.inl q2.end_mem_support)
    rw [hpath_eq] at hx_mid
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx_mid
    rcases hx_mid with hxu | hxv
    · exact hu.1 hxu.symm
    · exact hv.1 hxv.symm
  refine ⟨A, B, q.penultimate, haA_mem, r.snd, haB_mem, hdisj,
    Finset.notMem_erase x _, Finset.notMem_erase x _, hpart, hno_edge, ?_, ?_⟩
  · refine ⟨haA_adj, fun y hy hadj => ?_⟩
    rw [Finset.mem_erase, List.mem_toFinset] at hy
    exact hT.isAcyclic.eq_penultimate_of_adj_end hq hadj hy.2
  · refine ⟨haB_adj, fun y hy hadj => ?_⟩
    rw [Finset.mem_erase, List.mem_toFinset] at hy
    exact hT.isAcyclic.eq_snd_of_adj_start hr hadj hy.2

/- Section 4: Unique Bridge Between Disjoint Paths -/

private lemma oma_exists_bridge_walk
    (T : SimpleGraph α) {S1 S2 : Finset α}
    (hdisj : Disjoint S1 S2) (huniv : S1 ∪ S2 = Finset.univ)
    {a b : α} (w : T.Walk a b) (ha : a ∈ S1) (hb : b ∈ S2) :
    ∃ x ∈ S1, ∃ y ∈ S2, T.Adj x y := by
  induction w with
  | nil =>
    exact False.elim ((Finset.disjoint_left.mp hdisj ha) hb)
  | @cons u v _ hadj tail ih =>
    have hv_univ : v ∈ S1 ∪ S2 := huniv.symm ▸ Finset.mem_univ v
    rcases Finset.mem_union.mp hv_univ with hv1 | hv2
    · exact ih hv1 hb
    · exact ⟨u, ha, v, hv2, hadj⟩

private lemma oma_two_paths_unique_bridge
    (T : SimpleGraph α) (hT : T.IsTree) {S1 S2 : Finset α}
    (hdisj : Disjoint S1 S2) (huniv : S1 ∪ S2 = Finset.univ)
    {a1 b1 a2 b2 : α} {p1 : T.Walk a1 b1} {p2 : T.Walk a2 b2}
    (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hS1 : S1 = p1.support.toFinset) (hS2 : S2 = p2.support.toFinset) :
    ∃ u1 ∈ S1, ∃ u2 ∈ S2, T.Adj u1 u2 ∧
      ∀ x ∈ S1, ∀ y ∈ S2, T.Adj x y → x = u1 ∧ y = u2 := by
  have ha1 : a1 ∈ S1 := hS1 ▸ List.mem_toFinset.mpr p1.start_mem_support
  have ha2 : a2 ∈ S2 := hS2 ▸ List.mem_toFinset.mpr p2.start_mem_support
  obtain ⟨w0⟩ := hT.connected a1 a2
  obtain ⟨u1, hu1, u2, hu2, hadj0⟩ := oma_exists_bridge_walk T hdisj huniv w0 ha1 ha2
  refine ⟨u1, hu1, u2, hu2, hadj0, fun v1 hv1 v2 hv2 hadj1 => ?_⟩
  have hu1_p : u1 ∈ p1.support := List.mem_toFinset.mp (hS1 ▸ hu1)
  have hv1_p : v1 ∈ p1.support := List.mem_toFinset.mp (hS1 ▸ hv1)
  have hu2_p : u2 ∈ p2.support := List.mem_toFinset.mp (hS2 ▸ hu2)
  have hv2_p : v2 ∈ p2.support := List.mem_toFinset.mp (hS2 ▸ hv2)
  obtain ⟨r1, hr1, hr1_sub⟩ := oma_isPath_walk_in_support T hp1 hu1_p hv1_p
  obtain ⟨r2, hr2, hr2_sub⟩ := oma_isPath_walk_in_support T hp2 hv2_p hu2_p
  have hr1_S1 : ∀ z ∈ r1.support, z ∈ S1 := fun z hz =>
    hS1 ▸ List.mem_toFinset.mpr (hr1_sub z hz)
  have hr2_S2 : ∀ z ∈ r2.support, z ∈ S2 := fun z hz =>
    hS2 ▸ List.mem_toFinset.mpr (hr2_sub z hz)
  have hr2_rev_S2 : ∀ z ∈ r2.reverse.support, z ∈ S2 := fun z hz =>
    hr2_S2 z (by simpa using hz)
  by_cases huv1 : u1 = v1
  · subst huv1
    have hu1_not_r2 : u1 ∉ r2.reverse.support := fun h =>
      Finset.disjoint_left.mp hdisj hu1 (hr2_rev_S2 u1 h)
    have hpath_w : (Walk.cons hadj0 r2.reverse).IsPath :=
      hr2.reverse.cons hu1_not_r2
    have hwalk_eq : Walk.cons hadj0 r2.reverse = hadj1.toWalk :=
      Subtype.ext_iff.mp ((hT.isAcyclic.subsingleton_path u1 v2).elim
        ⟨Walk.cons hadj0 r2.reverse, hpath_w⟩ ⟨hadj1.toWalk, hadj1.isPath_toWalk⟩)
    have hlen : (Walk.cons hadj0 r2.reverse).length = hadj1.toWalk.length :=
      congrArg Walk.length hwalk_eq
    have hr2_len : r2.length = 0 := by
      simp only [Adj.toWalk, Walk.length_cons, Walk.length_reverse, Walk.length_nil] at hlen
      omega
    have hnil : r2.Nil := Walk.length_eq_zero_iff.mp hr2_len
    exact ⟨rfl, hr2.nil_iff_eq.mp hnil⟩
  · have hv1_not_r2 : v1 ∉ r2.reverse.support := fun h =>
      Finset.disjoint_left.mp hdisj hv1 (hr2_rev_S2 v1 h)
    have hc_path : (r2.reverse.concat hadj1.symm).IsPath :=
      hr2.reverse.concat hv1_not_r2 hadj1.symm
    have hu1_not_c : u1 ∉ (r2.reverse.concat hadj1.symm).support := by
      intro h
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Finset.disjoint_left.mp hdisj hu1 (hr2_rev_S2 u1 h)
      · exact huv1 h
    have hw_path : (Walk.cons hadj0 (r2.reverse.concat hadj1.symm)).IsPath :=
      hc_path.cons hu1_not_c
    have hwalk_eq : r1 = Walk.cons hadj0 (r2.reverse.concat hadj1.symm) :=
      Subtype.ext_iff.mp ((hT.isAcyclic.subsingleton_path u1 v1).elim
        ⟨r1, hr1⟩ ⟨Walk.cons hadj0 (r2.reverse.concat hadj1.symm), hw_path⟩)
    have hu2_in_r1 : u2 ∈ r1.support := by
      rw [hwalk_eq, Walk.support_cons]
      exact List.mem_cons_of_mem _ (r2.reverse.concat hadj1.symm).start_mem_support
    exact False.elim (Finset.disjoint_left.mp hdisj (hr1_S1 u2 hu2_in_r1) hu2)

/- Section 5: Double Counting and Component Matching -/

private lemma oma_double_count_bipartite
    (T : SimpleGraph α) [DecidableRel T.Adj] (A B : Finset α) :
    ∑ x ∈ A, (T.neighborFinset x ∩ B).card =
      ∑ y ∈ B, (T.neighborFinset y ∩ A).card := by
  have hL : ∀ x : α, (T.neighborFinset x ∩ B).card =
      ∑ y ∈ B, if T.Adj x y then 1 else 0 := by
    intro x
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp [mem_neighborFinset, and_comm]
  have hR : ∀ y : α, (T.neighborFinset y ∩ A).card =
      ∑ x ∈ A, if T.Adj x y then 1 else 0 := by
    intro y
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp [mem_neighborFinset, T.adj_comm, and_comm]
  simp_rw [hL, hR]
  exact Finset.sum_comm

private lemma oma_card_inter_add_card_sdiff_neighbor
    (T : SimpleGraph α) [DecidableRel T.Adj] (D : Finset α) (x : α) :
    (T.neighborFinset x ∩ D).card + (T.neighborFinset x \ D).card = T.degree x := by
  have h := Finset.card_inter_add_card_sdiff (T.neighborFinset x) D
  simp [SimpleGraph.card_neighborFinset_eq_degree]

private lemma oma_component_vc_bound
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (D K : Finset α) (u aK : α)
    (huD : u ∈ D) (haK_mem : aK ∈ K) (hu_not_K : u ∉ K) (haK_not_D : aK ∉ D)
    (hadj_u : T.Adj u aK)
    (hclosed : ∀ v ∈ K, v ≠ aK → T.neighborFinset v ⊆ K)
    (hD_deg : ∀ x ∈ K ∩ D, (T.neighborFinset x \ D).card = 1)
    (hDc_deg : ∀ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card = 1) :
    ∃ C_K ⊆ K, C_K.card ≤ (K ∩ D).card ∧
      ∀ x ∈ K, ∀ y ∈ K, T.Adj x y → x ∈ C_K ∨ y ∈ C_K := by
  let D_K : Finset α := K ∩ D
  let R_K : Finset α := (K \ D).erase aK
  have haK_Dc : aK ∈ Finset.univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ aK, haK_not_D⟩
  have haK_D_eq : T.neighborFinset aK ∩ D = {u} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨(mem_neighborFinset T aK u).mpr hadj_u.symm, huD⟩, ?_⟩
    intro z hz
    have hcard1 : (T.neighborFinset aK ∩ D).card = 1 := hDc_deg aK haK_Dc
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
    have hzw : z = w := by simpa [hw] using hz
    have huw : u = w := by
      have hu_mem : u ∈ T.neighborFinset aK ∩ D :=
        Finset.mem_inter.mpr ⟨(mem_neighborFinset T aK u).mpr hadj_u.symm, huD⟩
      simpa [hw] using hu_mem
    exact hzw.trans huw.symm
  have hDK_match : ∀ x ∈ D_K, (T.neighborFinset x ∩ R_K).card = 1 := by
    intro x hx
    rw [Finset.mem_inter] at hx
    have hxa : x ≠ aK := fun h => haK_not_D (h ▸ hx.2)
    have hsubK : T.neighborFinset x ⊆ K := hclosed x hx.1 hxa
    have hnot_adj_aK : ¬ T.Adj x aK := by
      intro hadj
      have hx_mem : x ∈ T.neighborFinset aK ∩ D :=
        Finset.mem_inter.mpr ⟨(mem_neighborFinset T aK x).mpr hadj.symm, hx.2⟩
      rw [haK_D_eq, Finset.mem_singleton] at hx_mem
      exact hu_not_K (hx_mem ▸ hx.1)
    have heq_set : T.neighborFinset x ∩ R_K = T.neighborFinset x \ D := by
      ext z
      simp only [R_K, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase, mem_neighborFinset]
      constructor
      · rintro ⟨hz1, ⟨_, _, hzD⟩⟩
        exact ⟨hz1, hzD⟩
      · rintro ⟨hz1, hzD⟩
        have hzK : z ∈ K := hsubK ((mem_neighborFinset T x z).mpr hz1)
        have hza : z ≠ aK := fun h => hnot_adj_aK (h ▸ hz1)
        exact ⟨hz1, ⟨hza, hzK, hzD⟩⟩
    rw [heq_set]
    exact hD_deg x (Finset.mem_inter.mpr hx)
  have hRK_match : ∀ y ∈ R_K, (T.neighborFinset y ∩ D_K).card = 1 := by
    intro y hy
    simp only [R_K, Finset.mem_erase, Finset.mem_sdiff] at hy
    have hsubK : T.neighborFinset y ⊆ K := hclosed y hy.2.1 hy.1
    have heq_set : T.neighborFinset y ∩ D_K = T.neighborFinset y ∩ D := by
      ext z
      simp only [D_K, Finset.mem_inter, mem_neighborFinset]
      constructor
      · rintro ⟨hz1, _, hzD⟩
        exact ⟨hz1, hzD⟩
      · rintro ⟨hz1, hzD⟩
        exact ⟨hz1, hsubK ((mem_neighborFinset T y z).mpr hz1), hzD⟩
    rw [heq_set]
    exact hDc_deg y (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy.2.2⟩)
  have hsum_L : ∑ x ∈ D_K, (T.neighborFinset x ∩ R_K).card = D_K.card := by
    calc ∑ x ∈ D_K, (T.neighborFinset x ∩ R_K).card
        = ∑ _x ∈ D_K, 1 := Finset.sum_congr rfl hDK_match
      _ = D_K.card := by simp
  have hsum_R : ∑ y ∈ R_K, (T.neighborFinset y ∩ D_K).card = R_K.card := by
    calc ∑ y ∈ R_K, (T.neighborFinset y ∩ D_K).card
        = ∑ _y ∈ R_K, 1 := Finset.sum_congr rfl hRK_match
      _ = R_K.card := by simp
  have hcard_eq : D_K.card = R_K.card := by
    rw [← hsum_L, ← hsum_R]
    exact oma_double_count_bipartite T D_K R_K
  have haK_mem_sdiff : aK ∈ K \ D := Finset.mem_sdiff.mpr ⟨haK_mem, haK_not_D⟩
  have hRK_card : R_K.card + 1 = (K \ D).card := by
    dsimp [R_K]
    exact Finset.card_erase_add_one haK_mem_sdiff
  have hK_split : (K ∩ D).card + (K \ D).card = K.card :=
    Finset.card_inter_add_card_sdiff K D
  have hK_card : K.card = 1 + 2 * (K ∩ D).card := by
    change (K ∩ D).card = R_K.card at hcard_eq
    omega
  obtain ⟨C_K, hCK_sub, hCK_half, hCK_cov⟩ := oma_exists_vc_subset_le_half T hT K
  refine ⟨C_K, hCK_sub, ?_, hCK_cov⟩
  omega

/- Section 6: Main Theorem (`oma_two_paths_bound`) -/

private theorem oma_two_paths_bound
    {α : Type*} [Fintype α] [DecidableEq α] (T : SimpleGraph α)
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  classical
  obtain ⟨P, hP, hP_card⟩ := oma_exists_min_pathCover T
  obtain ⟨D, hD, hD_card⟩ := oma_exists_min_tds T hT hn
  have hDc_lb : ∀ y ∈ Finset.univ \ D, 1 ≤ (T.neighborFinset y ∩ D).card := by
    intro y _
    obtain ⟨w, hwD, hadj⟩ := hD y
    exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨(mem_neighborFinset T y w).mpr hadj, hwD⟩⟩
  have hD_lb : ∀ x ∈ D, 1 ≤ (T.neighborFinset x ∩ D).card := by
    intro x _
    obtain ⟨w, hwD, hadj⟩ := hD x
    exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨(mem_neighborFinset T x w).mpr hadj, hwD⟩⟩
  have hP_pos : 1 ≤ P.card := by
    by_contra h0
    have hP_empty : P = ∅ := Finset.card_eq_zero.mp (by omega)
    have hpos : 0 < Fintype.card α := by omega
    have hne : Nonempty α := Fintype.card_pos_iff.mp hpos
    obtain ⟨v⟩ := hne
    have hv := hP.2.1 (Finset.mem_univ v)
    simp [hP_empty] at hv
  have hP_cases : P.card = 1 ∨ P.card = 2 := by omega
  rcases hP_cases with hP1 | hP2
  · obtain ⟨S1, rfl⟩ := Finset.card_eq_one.mp hP1
    have hS1_univ : S1 = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      have hv := hP.2.1 (Finset.mem_univ v)
      simpa using hv
    obtain ⟨a1, b1, p1, hp1, hS1_supp⟩ := hP.2.2 S1 (Finset.mem_singleton_self S1)
    have hdeg_le : ∀ x : α, T.degree x ≤ 2 := by
      intro x
      have hx_supp : x ∈ p1.support := List.mem_toFinset.mp (by rw [← hS1_supp, hS1_univ]; simp)
      have hsplit := (oma_path_neighbor_split T hT hp1 hx_supp).1
      have h_eq : T.neighborFinset x ∩ p1.support.toFinset = T.neighborFinset x := by
        ext y
        simp only [Finset.mem_inter, List.mem_toFinset]
        refine ⟨fun h => h.1, fun h => ⟨h, List.mem_toFinset.mp (by rw [← hS1_supp, hS1_univ]; simp)⟩⟩
      simpa [h_eq, SimpleGraph.card_neighborFinset_eq_degree] using hsplit
    have hsum_dc : (Finset.univ \ D).card ≤ ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := by
      calc (Finset.univ \ D).card
          = ∑ _y ∈ Finset.univ \ D, 1 := by simp
        _ ≤ ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := Finset.sum_le_sum hDc_lb
    have hsum_d : ∑ x ∈ D, (T.neighborFinset x \ D).card ≤ D.card := by
      calc ∑ x ∈ D, (T.neighborFinset x \ D).card
          ≤ ∑ _x ∈ D, 1 := by
            apply Finset.sum_le_sum
            intro x hx
            have h1 := hD_lb x hx
            have h2 := oma_card_inter_add_card_sdiff_neighbor T D x
            have h3 := hdeg_le x
            omega
        _ = D.card := by simp
    have hcross : ∑ x ∈ D, (T.neighborFinset x \ D).card =
        ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := by
      have heq : ∀ x, T.neighborFinset x \ D = T.neighborFinset x ∩ (Finset.univ \ D) := by
        intro x
        ext y
        simp
      simp_rw [heq]
      exact oma_double_count_bipartite T D (Finset.univ \ D)
    have hcard_part : D.card + (Finset.univ \ D).card = Fintype.card α := by
      simpa using Finset.card_inter_add_card_sdiff (Finset.univ : Finset α) D
    have hn_bound : Fintype.card α ≤ 2 * D.card := by omega
    have hvc_half : 2 * T.vertexCoverNum.toNat ≤ Fintype.card α := oma_tree_vc_le_half T hT
    omega
  · obtain ⟨S1, S2, hne12, rfl⟩ := Finset.card_eq_two.mp hP2
    have hdisj : Disjoint S1 S2 := hP.1 S1 (by simp) S2 (by simp) hne12
    have huniv : S1 ∪ S2 = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      have hv := hP.2.1 (Finset.mem_univ v)
      simpa using hv
    obtain ⟨a1, b1, p1, hp1, hS1_supp⟩ := hP.2.2 S1 (by simp)
    obtain ⟨a2, b2, p2, hp2, hS2_supp⟩ := hP.2.2 S2 (by simp)
    obtain ⟨u1, hu1, u2, hu2, hadj_bridge, huniq_bridge⟩ :=
      oma_two_paths_unique_bridge T hT hdisj huniv hp1 hp2 hS1_supp hS2_supp
    have hu_ne : u1 ≠ u2 := fun h => Finset.disjoint_left.mp hdisj hu1 (h ▸ hu2)
    have hN_u1_S2 : T.neighborFinset u1 ∩ S2 = {u2} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_inter.mpr ⟨(mem_neighborFinset T u1 u2).mpr hadj_bridge, hu2⟩, ?_⟩
      intro y hy
      rw [Finset.mem_inter, mem_neighborFinset] at hy
      exact (huniq_bridge u1 hu1 y hy.2 hy.1).2
    have hN_u2_S1 : T.neighborFinset u2 ∩ S1 = {u1} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_inter.mpr ⟨(mem_neighborFinset T u2 u1).mpr hadj_bridge.symm, hu1⟩, ?_⟩
      intro x hx
      rw [Finset.mem_inter, mem_neighborFinset] at hx
      exact (huniq_bridge x hx.2 u2 hu2 hx.1.symm).1
    have hN_split : ∀ x : α, (T.neighborFinset x ∩ S1).card + (T.neighborFinset x ∩ S2).card = T.degree x := by
      intro x
      have hdisj_N : Disjoint (T.neighborFinset x ∩ S1) (T.neighborFinset x ∩ S2) :=
        hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
      have hunion_N : (T.neighborFinset x ∩ S1) ∪ (T.neighborFinset x ∩ S2) = T.neighborFinset x := by
        rw [← Finset.inter_union_distrib_left, huniv, Finset.inter_univ]
      rw [← Finset.card_union_of_disjoint hdisj_N, hunion_N, SimpleGraph.card_neighborFinset_eq_degree]
    have hdeg_S1_other : ∀ x ∈ S1, x ≠ u1 → T.neighborFinset x ∩ S2 = ∅ := by
      intro x hx hne
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter, mem_neighborFinset] at hy
      exact hne (huniq_bridge x hx y hy.2 hy.1).1
    have hdeg_S2_other : ∀ x ∈ S2, x ≠ u2 → T.neighborFinset x ∩ S1 = ∅ := by
      intro x hx hne
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter, mem_neighborFinset] at hy
      exact hne (huniq_bridge y hy.2 x hx hy.1.symm).2
    have hdeg_other : ∀ x : α, x ∉ ({u1, u2} : Finset α) → T.degree x ≤ 2 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hx_univ : x ∈ S1 ∪ S2 := huniv ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hx_univ with hx1 | hx2
      · have hx_p : x ∈ p1.support := List.mem_toFinset.mp (hS1_supp ▸ hx1)
        have h1 := (oma_path_neighbor_split T hT hp1 hx_p).1
        have h2 : T.neighborFinset x ∩ S2 = ∅ := hdeg_S1_other x hx1 hx.1
        have h3 := hN_split x
        rw [← hS1_supp] at h1
        rw [h2, Finset.card_empty] at h3
        omega
      · have hx_p : x ∈ p2.support := List.mem_toFinset.mp (hS2_supp ▸ hx2)
        have h1 := (oma_path_neighbor_split T hT hp2 hx_p).1
        have h2 : T.neighborFinset x ∩ S1 = ∅ := hdeg_S2_other x hx2 hx.2
        have h3 := hN_split x
        rw [← hS2_supp] at h1
        rw [h2, Finset.card_empty] at h3
        omega
    have hu1_p : u1 ∈ p1.support := List.mem_toFinset.mp (hS1_supp ▸ hu1)
    have hu2_p : u2 ∈ p2.support := List.mem_toFinset.mp (hS2_supp ▸ hu2)
    have hdeg_u1_le : T.degree u1 ≤ 3 := by
      have h1 := (oma_path_neighbor_split T hT hp1 hu1_p).1
      have h3 := hN_split u1
      rw [← hS1_supp] at h1
      rw [hN_u1_S2, Finset.card_singleton] at h3
      omega
    have hdeg_u2_le : T.degree u2 ≤ 3 := by
      have h1 := (oma_path_neighbor_split T hT hp2 hu2_p).1
      have h3 := hN_split u2
      rw [← hS2_supp] at h1
      rw [hN_u2_S1, Finset.card_singleton] at h3
      omega
    let Bset : Finset α := {u1, u2}
    have hBset_card : Bset.card = 2 := Finset.card_pair hu_ne
    have hD_term_le : ∀ x ∈ D, (T.neighborFinset x \ D).card ≤ 1 + (if x ∈ Bset then 1 else 0) := by
      intro x hx
      have h1 := hD_lb x hx
      have h2 := oma_card_inter_add_card_sdiff_neighbor T D x
      by_cases hxB : x ∈ Bset
      · rw [if_pos hxB]
        have hxB' : x = u1 ∨ x = u2 := by simpa [Bset] using hxB
        have hdeg : T.degree x ≤ 3 := by
          rcases hxB' with rfl | rfl <;> assumption
        omega
      · rw [if_neg hxB]
        have hdeg : T.degree x ≤ 2 := hdeg_other x hxB
        omega
    have hsum_dc : (Finset.univ \ D).card ≤ ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := by
      calc (Finset.univ \ D).card
          = ∑ _y ∈ Finset.univ \ D, 1 := by simp
        _ ≤ ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := Finset.sum_le_sum hDc_lb
    have hcross : ∑ x ∈ D, (T.neighborFinset x \ D).card =
        ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := by
      have heq : ∀ x, T.neighborFinset x \ D = T.neighborFinset x ∩ (Finset.univ \ D) := by
        intro x
        ext y
        simp
      simp_rw [heq]
      exact oma_double_count_bipartite T D (Finset.univ \ D)
    have hsum_d_le : ∑ x ∈ D, (T.neighborFinset x \ D).card ≤ D.card + (D ∩ Bset).card := by
      calc ∑ x ∈ D, (T.neighborFinset x \ D).card
          ≤ ∑ x ∈ D, (1 + if x ∈ Bset then 1 else 0) := Finset.sum_le_sum hD_term_le
        _ = (∑ _x ∈ D, 1) + ∑ x ∈ D, (if x ∈ Bset then 1 else 0) := Finset.sum_add_distrib
        _ = D.card + (D ∩ Bset).card := by
            simp [Finset.sum_ite_mem]
    have hDB_le : (D ∩ Bset).card ≤ 2 := by
      calc (D ∩ Bset).card ≤ Bset.card := Finset.card_le_card Finset.inter_subset_right
        _ = 2 := hBset_card
    have hcard_part : D.card + (Finset.univ \ D).card = Fintype.card α := by
      simpa using Finset.card_inter_add_card_sdiff (Finset.univ : Finset α) D
    have hn_le : Fintype.card α ≤ 2 * D.card + 2 := by omega
    rcases Nat.lt_or_eq_of_le hn_le with hlt | htight
    · have hvc_half : 2 * T.vertexCoverNum.toNat ≤ Fintype.card α := oma_tree_vc_le_half T hT
      omega
    · have hDc_eq : (Finset.univ \ D).card = D.card + 2 := by omega
      have hDB_eq : (D ∩ Bset).card = 2 := by omega
      have hDB_sub : D ∩ Bset = Bset :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      have hu1_D : u1 ∈ D := by
        have : u1 ∈ D ∩ Bset := hDB_sub.symm ▸ (by simp [Bset])
        exact (Finset.mem_inter.mp this).1
      have hu2_D : u2 ∈ D := by
        have : u2 ∈ D ∩ Bset := hDB_sub.symm ▸ (by simp [Bset])
        exact (Finset.mem_inter.mp this).1
      have hsum_d_eq : ∑ x ∈ D, (T.neighborFinset x \ D).card =
          ∑ x ∈ D, (1 + if x ∈ Bset then 1 else 0) := by
        have h_ite : ∑ x ∈ D, (1 + if x ∈ Bset then 1 else 0) = D.card + (D ∩ Bset).card := by
          rw [Finset.sum_add_distrib]
          simp [Finset.sum_ite_mem]
        omega
      have hD_term_eq : ∀ x ∈ D, (T.neighborFinset x \ D).card = 1 + (if x ∈ Bset then 1 else 0) :=
        fun x hx => (Finset.sum_eq_sum_iff_of_le hD_term_le).mp hsum_d_eq x hx
      have hsum_dc_eq : ∑ _y ∈ Finset.univ \ D, 1 =
          ∑ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card := by
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        omega
      have hDc_term_eq : ∀ y ∈ Finset.univ \ D, (T.neighborFinset y ∩ D).card = 1 :=
        fun y hy => ((Finset.sum_eq_sum_iff_of_le hDc_lb).mp hsum_dc_eq y hy).symm
      have hD_other_deg : ∀ x ∈ D, x ∉ Bset → (T.neighborFinset x \ D).card = 1 := by
        intro x hxD hxB
        have h := hD_term_eq x hxD
        simpa [hxB] using h
      have hu1_deg3 : T.degree u1 = 3 := by
        have h := hD_term_eq u1 hu1_D
        have hu1B : u1 ∈ Bset := by simp [Bset]
        simp only [hu1B, ite_true] at h
        have h1 := hD_lb u1 hu1_D
        have h2 := oma_card_inter_add_card_sdiff_neighbor T D u1
        omega
      have hu2_deg3 : T.degree u2 = 3 := by
        have h := hD_term_eq u2 hu2_D
        have hu2B : u2 ∈ Bset := by simp [Bset]
        simp only [hu2B, ite_true] at h
        have h1 := hD_lb u2 hu2_D
        have h2 := oma_card_inter_add_card_sdiff_neighbor T D u2
        omega
      have hu1_p_card2 : (T.neighborFinset u1 ∩ p1.support.toFinset).card = 2 := by
        have h3 := hN_split u1
        rw [hS1_supp, hN_u1_S2, Finset.card_singleton, hu1_deg3] at h3
        omega
      have hu2_p_card2 : (T.neighborFinset u2 ∩ p2.support.toFinset).card = 2 := by
        have h3 := hN_split u2
        rw [hS2_supp, hN_u2_S1, Finset.card_singleton, hu2_deg3] at h3
        omega
      obtain ⟨A1, B1, aA1, haA1, aB1, haB1, hdisj1, hu1_nA1, hu1_nB1, hpart1, hno1, huniqA1, huniqB1⟩ :=
        (oma_path_neighbor_split T hT hp1 hu1_p).2 hu1_p_card2
      obtain ⟨A2, B2, aA2, haA2, aB2, haB2, hdisj2, hu2_nA2, hu2_nB2, hpart2, hno2, huniqA2, huniqB2⟩ :=
        (oma_path_neighbor_split T hT hp2 hu2_p).2 hu2_p_card2
      rw [← hS1_supp] at hpart1
      rw [← hS2_supp] at hpart2
      have hA1_sub_S1 : A1 ⊆ S1.erase u1 := fun z hz => hpart1 ▸ Finset.mem_union_left B1 hz
      have hB1_sub_S1 : B1 ⊆ S1.erase u1 := fun z hz => hpart1 ▸ Finset.mem_union_right A1 hz
      have hA2_sub_S2 : A2 ⊆ S2.erase u2 := fun z hz => hpart2 ▸ Finset.mem_union_left B2 hz
      have hB2_sub_S2 : B2 ⊆ S2.erase u2 := fun z hz => hpart2 ▸ Finset.mem_union_right A2 hz
      have hu1_D_eq : T.neighborFinset u1 ∩ D = {u2} := by
        have hcard1 : (T.neighborFinset u1 ∩ D).card = 1 := by
          have h := hD_term_eq u1 hu1_D
          have hu1B : u1 ∈ Bset := by simp [Bset]
          simp only [hu1B, ite_true] at h
          have h2 := oma_card_inter_add_card_sdiff_neighbor T D u1
          omega
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_inter.mpr ⟨(mem_neighborFinset T u1 u2).mpr hadj_bridge, hu2_D⟩, ?_⟩
        intro z hz
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
        have hzw : z = w := by simpa [hw] using hz
        have hu2w : u2 = w := by
          have : u2 ∈ T.neighborFinset u1 ∩ D :=
            Finset.mem_inter.mpr ⟨(mem_neighborFinset T u1 u2).mpr hadj_bridge, hu2_D⟩
          simpa [hw] using this
        exact hzw.trans hu2w.symm
      have hu2_D_eq : T.neighborFinset u2 ∩ D = {u1} := by
        have hcard1 : (T.neighborFinset u2 ∩ D).card = 1 := by
          have h := hD_term_eq u2 hu2_D
          have hu2B : u2 ∈ Bset := by simp [Bset]
          simp only [hu2B, ite_true] at h
          have h2 := oma_card_inter_add_card_sdiff_neighbor T D u2
          omega
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_inter.mpr ⟨(mem_neighborFinset T u2 u1).mpr hadj_bridge.symm, hu1_D⟩, ?_⟩
        intro z hz
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
        have hzw : z = w := by simpa [hw] using hz
        have hu1w : u1 = w := by
          have : u1 ∈ T.neighborFinset u2 ∩ D :=
            Finset.mem_inter.mpr ⟨(mem_neighborFinset T u2 u1).mpr hadj_bridge.symm, hu1_D⟩
          simpa [hw] using this
        exact hzw.trans hu1w.symm
      have hnotD_of_S1 : ∀ a ∈ S1, T.Adj u1 a → a ∉ D := by
        intro a ha hadj haD
        have ha_mem : a ∈ T.neighborFinset u1 ∩ D :=
          Finset.mem_inter.mpr ⟨(mem_neighborFinset T u1 a).mpr hadj, haD⟩
        rw [hu1_D_eq, Finset.mem_singleton] at ha_mem
        exact Finset.disjoint_left.mp hdisj ha (ha_mem ▸ hu2)
      have hnotD_of_S2 : ∀ a ∈ S2, T.Adj u2 a → a ∉ D := by
        intro a ha hadj haD
        have ha_mem : a ∈ T.neighborFinset u2 ∩ D :=
          Finset.mem_inter.mpr ⟨(mem_neighborFinset T u2 a).mpr hadj, haD⟩
        rw [hu2_D_eq, Finset.mem_singleton] at ha_mem
        exact Finset.disjoint_left.mp hdisj (ha_mem ▸ hu1) ha
      have hclosedA1 : ∀ v ∈ A1, v ≠ aA1 → T.neighborFinset v ⊆ A1 := by
        intro v hv hne z hz
        rw [mem_neighborFinset] at hz
        have hv_S1 : v ∈ S1 := Finset.mem_of_mem_erase (hA1_sub_S1 hv)
        have hv_ne_u1 : v ≠ u1 := Finset.ne_of_mem_erase (hA1_sub_S1 hv)
        have hz_nS2 : z ∉ S2 := fun hz2 =>
          hv_ne_u1 (huniq_bridge v hv_S1 z hz2 hz).1
        have hz_S1 : z ∈ S1 := (Finset.mem_union.mp (huniv ▸ Finset.mem_univ z)).resolve_right hz_nS2
        have hz_ne_u1 : z ≠ u1 := fun h => hne (huniqA1.2 v hv (h ▸ hz.symm))
        have hz_erase : z ∈ A1 ∪ B1 := hpart1 ▸ Finset.mem_erase.mpr ⟨hz_ne_u1, hz_S1⟩
        exact (Finset.mem_union.mp hz_erase).resolve_right (fun hzB => hno1 v hv z hzB hz)
      have hclosedB1 : ∀ v ∈ B1, v ≠ aB1 → T.neighborFinset v ⊆ B1 := by
        intro v hv hne z hz
        rw [mem_neighborFinset] at hz
        have hv_S1 : v ∈ S1 := Finset.mem_of_mem_erase (hB1_sub_S1 hv)
        have hv_ne_u1 : v ≠ u1 := Finset.ne_of_mem_erase (hB1_sub_S1 hv)
        have hz_nS2 : z ∉ S2 := fun hz2 =>
          hv_ne_u1 (huniq_bridge v hv_S1 z hz2 hz).1
        have hz_S1 : z ∈ S1 := (Finset.mem_union.mp (huniv ▸ Finset.mem_univ z)).resolve_right hz_nS2
        have hz_ne_u1 : z ≠ u1 := fun h => hne (huniqB1.2 v hv (h ▸ hz.symm))
        have hz_erase : z ∈ A1 ∪ B1 := hpart1 ▸ Finset.mem_erase.mpr ⟨hz_ne_u1, hz_S1⟩
        exact (Finset.mem_union.mp hz_erase).resolve_left (fun hzA => hno1 z hzA v hv hz.symm)
      have hclosedA2 : ∀ v ∈ A2, v ≠ aA2 → T.neighborFinset v ⊆ A2 := by
        intro v hv hne z hz
        rw [mem_neighborFinset] at hz
        have hv_S2 : v ∈ S2 := Finset.mem_of_mem_erase (hA2_sub_S2 hv)
        have hv_ne_u2 : v ≠ u2 := Finset.ne_of_mem_erase (hA2_sub_S2 hv)
        have hz_nS1 : z ∉ S1 := fun hz1 =>
          hv_ne_u2 (huniq_bridge z hz1 v hv_S2 hz.symm).2
        have hz_S2 : z ∈ S2 := (Finset.mem_union.mp (huniv ▸ Finset.mem_univ z)).resolve_left hz_nS1
        have hz_ne_u2 : z ≠ u2 := fun h => hne (huniqA2.2 v hv (h ▸ hz.symm))
        have hz_erase : z ∈ A2 ∪ B2 := hpart2 ▸ Finset.mem_erase.mpr ⟨hz_ne_u2, hz_S2⟩
        exact (Finset.mem_union.mp hz_erase).resolve_right (fun hzB => hno2 v hv z hzB hz)
      have hclosedB2 : ∀ v ∈ B2, v ≠ aB2 → T.neighborFinset v ⊆ B2 := by
        intro v hv hne z hz
        rw [mem_neighborFinset] at hz
        have hv_S2 : v ∈ S2 := Finset.mem_of_mem_erase (hB2_sub_S2 hv)
        have hv_ne_u2 : v ≠ u2 := Finset.ne_of_mem_erase (hB2_sub_S2 hv)
        have hz_nS1 : z ∉ S1 := fun hz1 =>
          hv_ne_u2 (huniq_bridge z hz1 v hv_S2 hz.symm).2
        have hz_S2 : z ∈ S2 := (Finset.mem_union.mp (huniv ▸ Finset.mem_univ z)).resolve_left hz_nS1
        have hz_ne_u2 : z ≠ u2 := fun h => hne (huniqB2.2 v hv (h ▸ hz.symm))
        have hz_erase : z ∈ A2 ∪ B2 := hpart2 ▸ Finset.mem_erase.mpr ⟨hz_ne_u2, hz_S2⟩
        exact (Finset.mem_union.mp hz_erase).resolve_left (fun hzA => hno2 z hzA v hv hz.symm)
      have hD_deg_sub : ∀ K : Finset α, (∀ z ∈ K, z ∉ Bset) →
          ∀ x ∈ K ∩ D, (T.neighborFinset x \ D).card = 1 := by
        intro K hK x hx
        rw [Finset.mem_inter] at hx
        exact hD_other_deg x hx.2 (hK x hx.1)
      have hA1_nB : ∀ z ∈ A1, z ∉ Bset := by
        intro z hz
        simp only [Bset, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hu1_nA1 (h ▸ hz), fun h => ?_⟩
        exact Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase (hA1_sub_S1 hz)) (h ▸ hu2)
      have hB1_nB : ∀ z ∈ B1, z ∉ Bset := by
        intro z hz
        simp only [Bset, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hu1_nB1 (h ▸ hz), fun h => ?_⟩
        exact Finset.disjoint_left.mp hdisj (Finset.mem_of_mem_erase (hB1_sub_S1 hz)) (h ▸ hu2)
      have hA2_nB : ∀ z ∈ A2, z ∉ Bset := by
        intro z hz
        simp only [Bset, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => ?_, fun h => hu2_nA2 (h ▸ hz)⟩
        exact Finset.disjoint_left.mp hdisj (h ▸ hu1) (Finset.mem_of_mem_erase (hA2_sub_S2 hz))
      have hB2_nB : ∀ z ∈ B2, z ∉ Bset := by
        intro z hz
        simp only [Bset, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => ?_, fun h => hu2_nB2 (h ▸ hz)⟩
        exact Finset.disjoint_left.mp hdisj (h ▸ hu1) (Finset.mem_of_mem_erase (hB2_sub_S2 hz))
      obtain ⟨CA1, hCA1_sub, hCA1_card, hCA1_cov⟩ :=
        oma_component_vc_bound T hT D A1 u1 aA1 hu1_D haA1 hu1_nA1
          (hnotD_of_S1 aA1 (Finset.mem_of_mem_erase (hA1_sub_S1 haA1)) huniqA1.1)
          huniqA1.1 hclosedA1 (hD_deg_sub A1 hA1_nB) hDc_term_eq
      obtain ⟨CB1, hCB1_sub, hCB1_card, hCB1_cov⟩ :=
        oma_component_vc_bound T hT D B1 u1 aB1 hu1_D haB1 hu1_nB1
          (hnotD_of_S1 aB1 (Finset.mem_of_mem_erase (hB1_sub_S1 haB1)) huniqB1.1)
          huniqB1.1 hclosedB1 (hD_deg_sub B1 hB1_nB) hDc_term_eq
      obtain ⟨CA2, hCA2_sub, hCA2_card, hCA2_cov⟩ :=
        oma_component_vc_bound T hT D A2 u2 aA2 hu2_D haA2 hu2_nA2
          (hnotD_of_S2 aA2 (Finset.mem_of_mem_erase (hA2_sub_S2 haA2)) huniqA2.1)
          huniqA2.1 hclosedA2 (hD_deg_sub A2 hA2_nB) hDc_term_eq
      obtain ⟨CB2, hCB2_sub, hCB2_card, hCB2_cov⟩ :=
        oma_component_vc_bound T hT D B2 u2 aB2 hu2_D haB2 hu2_nB2
          (hnotD_of_S2 aB2 (Finset.mem_of_mem_erase (hB2_sub_S2 haB2)) huniqB2.1)
          huniqB2.1 hclosedB2 (hD_deg_sub B2 hB2_nB) hDc_term_eq
      let C : Finset α := Bset ∪ CA1 ∪ CB1 ∪ CA2 ∪ CB2
      have hC_vc : T.IsVertexCover (C : Set α) := by
        intro x y hadj
        by_cases hxB : x ∈ Bset
        · exact Or.inl (Finset.mem_coe.mpr (by simp [C, hxB]))
        by_cases hyB : y ∈ Bset
        · exact Or.inr (Finset.mem_coe.mpr (by simp [C, hyB]))
        have hxB' : x ≠ u1 ∧ x ≠ u2 := by
          simpa [Bset, Finset.mem_insert, Finset.mem_singleton, not_or] using hxB
        have hyB' : y ≠ u1 ∧ y ≠ u2 := by
          simpa [Bset, Finset.mem_insert, Finset.mem_singleton, not_or] using hyB
        have hx_univ : x ∈ S1 ∪ S2 := huniv ▸ Finset.mem_univ x
        have hy_univ : y ∈ S1 ∪ S2 := huniv ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp hx_univ with hx1 | hx2
        · have hy1 : y ∈ S1 := by
            rcases Finset.mem_union.mp hy_univ with hy1 | hy2
            · exact hy1
            · exact False.elim (hxB'.1 (huniq_bridge x hx1 y hy2 hadj).1)
          have hx_AB : x ∈ A1 ∪ B1 := hpart1 ▸ Finset.mem_erase.mpr ⟨hxB'.1, hx1⟩
          have hy_AB : y ∈ A1 ∪ B1 := hpart1 ▸ Finset.mem_erase.mpr ⟨hyB'.1, hy1⟩
          rcases Finset.mem_union.mp hx_AB with hxA | hxB1
          · have hyA : y ∈ A1 :=
              (Finset.mem_union.mp hy_AB).resolve_right (fun hyB1 => hno1 x hxA y hyB1 hadj)
            rcases hCA1_cov x hxA y hyA hadj with hxc | hyc
            · exact Or.inl (Finset.mem_coe.mpr (by simp [C, hxc]))
            · exact Or.inr (Finset.mem_coe.mpr (by simp [C, hyc]))
          · have hyB1 : y ∈ B1 :=
              (Finset.mem_union.mp hy_AB).resolve_left (fun hyA => hno1 y hyA x hxB1 hadj.symm)
            rcases hCB1_cov x hxB1 y hyB1 hadj with hxc | hyc
            · exact Or.inl (Finset.mem_coe.mpr (by simp [C, hxc]))
            · exact Or.inr (Finset.mem_coe.mpr (by simp [C, hyc]))
        · have hy2 : y ∈ S2 := by
            rcases Finset.mem_union.mp hy_univ with hy1 | hy2
            · exact False.elim (hxB'.2 (huniq_bridge y hy1 x hx2 hadj.symm).2)
            · exact hy2
          have hx_AB : x ∈ A2 ∪ B2 := hpart2 ▸ Finset.mem_erase.mpr ⟨hxB'.2, hx2⟩
          have hy_AB : y ∈ A2 ∪ B2 := hpart2 ▸ Finset.mem_erase.mpr ⟨hyB'.2, hy2⟩
          rcases Finset.mem_union.mp hx_AB with hxA | hxB2
          · have hyA : y ∈ A2 :=
              (Finset.mem_union.mp hy_AB).resolve_right (fun hyB2 => hno2 x hxA y hyB2 hadj)
            rcases hCA2_cov x hxA y hyA hadj with hxc | hyc
            · exact Or.inl (Finset.mem_coe.mpr (by simp [C, hxc]))
            · exact Or.inr (Finset.mem_coe.mpr (by simp [C, hyc]))
          · have hyB2 : y ∈ B2 :=
              (Finset.mem_union.mp hy_AB).resolve_left (fun hyA => hno2 y hyA x hxB2 hadj.symm)
            rcases hCB2_cov x hxB2 y hyB2 hadj with hxc | hyc
            · exact Or.inl (Finset.mem_coe.mpr (by simp [C, hxc]))
            · exact Or.inr (Finset.mem_coe.mpr (by simp [C, hyc]))
      have hD_part_eq :
          (A1 ∩ D).card + (B1 ∩ D).card + (A2 ∩ D).card + (B2 ∩ D).card + 2 = D.card := by
        have hS1_eq : (A1 ∩ D).card + (B1 ∩ D).card + 1 = (S1 ∩ D).card := by
          have hdisj_1D : Disjoint (A1 ∩ D) (B1 ∩ D) :=
            hdisj1.mono Finset.inter_subset_left Finset.inter_subset_left
          have hAB_1D : (A1 ∩ D) ∪ (B1 ∩ D) = (S1 ∩ D).erase u1 := by
            ext z
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase]
            have hz_part : z ∈ A1 ∨ z ∈ B1 ↔ z ≠ u1 ∧ z ∈ S1 := by
              simpa [Finset.mem_union, Finset.mem_erase] using Finset.ext_iff.mp hpart1 z
            tauto
          have hu1_S1D : u1 ∈ S1 ∩ D := Finset.mem_inter.mpr ⟨hu1, hu1_D⟩
          rw [← Finset.card_union_of_disjoint hdisj_1D, hAB_1D, Finset.card_erase_add_one hu1_S1D]
        have hS2_eq : (A2 ∩ D).card + (B2 ∩ D).card + 1 = (S2 ∩ D).card := by
          have hdisj_2D : Disjoint (A2 ∩ D) (B2 ∩ D) :=
            hdisj2.mono Finset.inter_subset_left Finset.inter_subset_left
          have hAB_2D : (A2 ∩ D) ∪ (B2 ∩ D) = (S2 ∩ D).erase u2 := by
            ext z
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_erase]
            have hz_part : z ∈ A2 ∨ z ∈ B2 ↔ z ≠ u2 ∧ z ∈ S2 := by
              simpa [Finset.mem_union, Finset.mem_erase] using Finset.ext_iff.mp hpart2 z
            tauto
          have hu2_S2D : u2 ∈ S2 ∩ D := Finset.mem_inter.mpr ⟨hu2, hu2_D⟩
          rw [← Finset.card_union_of_disjoint hdisj_2D, hAB_2D, Finset.card_erase_add_one hu2_S2D]
        have hS12_eq : (S1 ∩ D).card + (S2 ∩ D).card = D.card := by
          have hdisj_D : Disjoint (S1 ∩ D) (S2 ∩ D) :=
            hdisj.mono Finset.inter_subset_left Finset.inter_subset_left
          have hunion_D : (S1 ∩ D) ∪ (S2 ∩ D) = D := by
            rw [← Finset.union_inter_distrib_right, huniv, Finset.univ_inter]
          rw [← Finset.card_union_of_disjoint hdisj_D, hunion_D]
        omega
      have hC_card_le : C.card ≤ D.card := by
        have h1 := Finset.card_union_le (Bset ∪ CA1 ∪ CB1 ∪ CA2) CB2
        have h2 := Finset.card_union_le (Bset ∪ CA1 ∪ CB1) CA2
        have h3 := Finset.card_union_le (Bset ∪ CA1) CB1
        have h4 := Finset.card_union_le Bset CA1
        change (Bset ∪ CA1 ∪ CB1 ∪ CA2 ∪ CB2).card ≤ D.card
        omega
      have hvc : T.vertexCoverNum.toNat ≤ C.card :=
        oma_vertexCoverNum_toNat_le_of_isVertexCover T C hC_vc
      omega

end

theorem OMA.solution :
    type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.two_paths := by
  intro α _ _ T hT hn hp
  exact oma_two_paths_bound T hT hn hp
