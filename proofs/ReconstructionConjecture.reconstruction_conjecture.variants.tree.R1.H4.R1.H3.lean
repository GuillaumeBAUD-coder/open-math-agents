import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

section Tree3485H3

open SimpleGraph Classical

private structure BicenterData {V : Type} [Fintype V] (T : SimpleGraph V) (r : ℕ) where
  c₁ : V
  c₂ : V
  hr : 1 ≤ r
  hT : T.IsTree
  hdiam : T.diam = 2 * r + 1
  hadj : T.Adj c₁ c₂
  hne : ∀ x : V, T.dist x c₁ ≠ T.dist x c₂
  hle₁ : ∀ x : V, T.dist x c₁ < T.dist x c₂ → T.dist x c₁ ≤ r
  hle₂ : ∀ x : V, T.dist x c₂ < T.dist x c₁ → T.dist x c₂ ≤ r
  ht₁ : (T.induce {x : V | T.dist x c₁ < T.dist x c₂}).IsTree
  ht₂ : (T.induce {x : V | T.dist x c₂ < T.dist x c₁}).IsTree
  hdist : ∀ x y : V, T.dist x c₁ < T.dist x c₂ → T.dist y c₂ < T.dist y c₁ →
    T.dist x y = T.dist x c₁ + 1 + T.dist c₂ y
  hbig₁ : r + 2 ≤ {x : V | T.dist x c₁ < T.dist x c₂}.ncard
  hbig₂ : r + 2 ≤ {x : V | T.dist x c₂ < T.dist x c₁}.ncard

private def BicenterData.swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : BicenterData T r where
  c₁ := D.c₂
  c₂ := D.c₁
  hr := D.hr
  hT := D.hT
  hdiam := D.hdiam
  hadj := D.hadj.symm
  hne := fun x => (D.hne x).symm
  hle₁ := D.hle₂
  hle₂ := D.hle₁
  ht₁ := D.ht₂
  ht₂ := D.ht₁
  hdist := fun x y hx hy => by
    rw [SimpleGraph.dist_comm (u := x) (v := y), D.hdist y x hy hx,
      SimpleGraph.dist_comm (u := D.c₂) (v := x), SimpleGraph.dist_comm (u := y) (v := D.c₁)]
    ring
  hbig₁ := D.hbig₂
  hbig₂ := D.hbig₁

private def BicenterData.side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Set V :=
  {x : V | T.dist x D.c₁ < T.dist x D.c₂}

private noncomputable def BicenterData.A₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Finset V :=
  Finset.univ.filter (fun x => T.dist x D.c₁ < T.dist x D.c₂)

private lemma mem_A₁_iff {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} : x ∈ D.A₁ ↔ x ∈ D.side₁ := by
  simp [BicenterData.A₁, BicenterData.side₁]

private lemma A₁_card_eq_ncard {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁.card = D.side₁.ncard := by
  have h : D.side₁ = (D.A₁ : Set V) := by
    ext x
    exact (mem_A₁_iff D).symm
  rw [h, Set.ncard_coe_finset]

private lemma card_side₁_eq_A₁_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Fintype.card D.side₁ = D.A₁.card :=
  Fintype.card_of_finset' D.A₁ (fun _ => mem_A₁_iff D)

private lemma mem_side₁_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₁ ∈ D.side₁ := by
  simp only [BicenterData.side₁, Set.mem_setOf_eq, dist_self, dist_eq_one_iff_adj.mpr D.hadj]
  omega

private lemma mem_A₁_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.c₁ ∈ D.A₁ :=
  (mem_A₁_iff D).mpr (mem_side₁_self D)

private lemma disjoint_A₁_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : Disjoint D.A₁ D.swap.A₁ := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  rw [mem_A₁_iff] at hx₁ hx₂
  change T.dist x D.c₁ < T.dist x D.c₂ at hx₁
  change T.dist x D.c₂ < T.dist x D.c₁ at hx₂
  omega

private lemma union_A₁_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁ ∪ D.swap.A₁ = Finset.univ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rw [mem_A₁_iff, mem_A₁_iff]
  exact lt_or_gt_of_ne (D.hne x)

private lemma card_A₁_add_swap {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁.card + D.swap.A₁.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint (disjoint_A₁_swap D), union_A₁_swap, Finset.card_univ]

private noncomputable def BicenterData.T₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : SimpleGraph D.side₁ :=
  T.induce D.side₁

private noncomputable def BicenterData.root₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.side₁ :=
  ⟨D.c₁, mem_side₁_self D⟩

private lemma BicenterData.ht_side₁ {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.T₁.IsTree :=
  D.ht₁

private lemma mem_swap_side₁_of_not_mem {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (hx : x ∉ D.side₁) : x ∈ D.swap.side₁ :=
  (lt_or_gt_of_ne (D.hne x)).resolve_left (by simpa [BicenterData.side₁] using hx)

private lemma induce_dist_eq {V : Type} {T : SimpleGraph V} (hT : T.IsTree) {S : Set V}
    (hS : (T.induce S).IsTree) (x y : S) : (T.induce S).dist x y = T.dist x.1 y.1 := by
  obtain ⟨p, hp_path, hp_len⟩ := hS.connected.exists_path_of_dist x y
  let f : T.induce S →g T := (SimpleGraph.Embedding.induce S).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hp'_path : (p.map f).IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp_path.support_nodup.map hf)
  obtain ⟨q, hq_path, hq_len⟩ := hT.connected.exists_path_of_dist x.1 y.1
  have huniq := (hT.existsUnique_path x.1 y.1).unique hp'_path hq_path
  rw [← hp_len, ← hq_len]
  exact (Walk.length_map f p).symm.trans (congrArg Walk.length huniq)

private lemma exists_far_vertex {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : ∃ a : D.side₁, D.T₁.dist a D.root₁ = r := by
  have hneV : Nonempty V := D.hT.connected.nonempty
  obtain ⟨x, y, hxy⟩ := T.exists_dist_eq_diam
  have hxy_r : T.dist x y = 2 * r + 1 := hxy.trans D.hdiam
  have htri : ∀ u v : V, u ∈ D.side₁ → v ∈ D.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₁ u hu
    have h2 := D.hle₁ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₁ + T.dist D.c₁ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₁) (v := v)] at h3
    omega
  have htri₂ : ∀ u v : V, u ∈ D.swap.side₁ → v ∈ D.swap.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₂ u hu
    have h2 := D.hle₂ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₂ + T.dist D.c₂ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := v)] at h3
    omega
  rcases lt_or_gt_of_ne (D.hne x) with hx | hx <;> rcases lt_or_gt_of_ne (D.hne y) with hy | hy
  · exfalso; have := htri x y hx hy; omega
  · have hdeq := D.hdist x y hx hy
    have h1 := D.hle₁ x hx
    have h2 := D.hle₂ y hy
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := y)] at hdeq
    refine ⟨⟨x, (show x ∈ D.side₁ from hx)⟩, ?_⟩
    dsimp [BicenterData.T₁]
    rw [induce_dist_eq D.hT D.ht_side₁]
    dsimp only [BicenterData.root₁]
    omega
  · have hdeq := D.hdist y x hy hx
    have h1 := D.hle₁ y hy
    have h2 := D.hle₂ x hx
    rw [SimpleGraph.dist_comm (u := x) (v := y)] at hxy_r
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := x)] at hdeq
    refine ⟨⟨y, (show y ∈ D.side₁ from hy)⟩, ?_⟩
    dsimp [BicenterData.T₁]
    rw [induce_dist_eq D.hT D.ht_side₁]
    dsimp only [BicenterData.root₁]
    omega
  · exfalso; have := htri₂ x y hx hy; omega

private lemma eq_center_of_adj_across {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x y : V} (hx : x ∈ D.side₁) (hy : y ∈ D.swap.side₁)
    (hadj : T.Adj x y) : x = D.c₁ ∧ y = D.c₂ := by
  have h1 : T.dist x y = 1 := dist_eq_one_iff_adj.mpr hadj
  have h2 := D.hdist x y hx hy
  have hx0 : T.dist x D.c₁ = 0 := by omega
  have hy0 : T.dist D.c₂ y = 0 := by omega
  exact ⟨(D.hT.connected.dist_eq_zero_iff).mp hx0,
    ((D.hT.connected.dist_eq_zero_iff).mp hy0).symm⟩

private def RootedIso {A B : Type} (R₁ : SimpleGraph A) (a : A) (R₂ : SimpleGraph B) (b : B) : Prop :=
  ∃ φ : R₁ ≃g R₂, φ a = b

private lemma RootedIso.refl {A : Type} (R : SimpleGraph A) (a : A) : RootedIso R a R a :=
  ⟨{ toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
     map_rel_iff' := fun {_ _} => Iff.rfl }, rfl⟩

private lemma RootedIso.symm {A B : Type} {R₁ : SimpleGraph A} {a : A} {R₂ : SimpleGraph B} {b : B}
    (h : RootedIso R₁ a R₂ b) : RootedIso R₂ b R₁ a := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.symm, by rw [← hφ, φ.symm_apply_apply]⟩

private lemma RootedIso.trans {A B C : Type} {R₁ : SimpleGraph A} {a : A}
    {R₂ : SimpleGraph B} {b : B} {R₃ : SimpleGraph C} {c : C}
    (h1 : RootedIso R₁ a R₂ b) (h2 : RootedIso R₂ b R₃ c) : RootedIso R₁ a R₃ c := by
  obtain ⟨φ₁, hφ₁⟩ := h1
  obtain ⟨φ₂, hφ₂⟩ := h2
  exact ⟨φ₁.trans φ₂, by simp [hφ₁, hφ₂]⟩

private lemma RootedIso.card_eq {A B : Type} [Fintype A] [Fintype B]
    {R₁ : SimpleGraph A} {a : A} {R₂ : SimpleGraph B} {b : B}
    (h : RootedIso R₁ a R₂ b) : Fintype.card A = Fintype.card B := by
  obtain ⟨φ, _⟩ := h
  exact Fintype.card_congr φ.toEquiv

private def attachPath {A : Type} (R : SimpleGraph A) (root : A) (r : ℕ) :
    SimpleGraph (A ⊕ Fin (r + 1)) where
  Adj u v := match u, v with
    | .inl a, .inl b => R.Adj a b
    | .inr i, .inr j => (pathGraph (r + 1)).Adj i j
    | .inl a, .inr i => a = root ∧ i.1 = 0
    | .inr i, .inl a => a = root ∧ i.1 = 0
  symm := ⟨fun u v h => by
    rcases u with a | i <;> rcases v with b | j
    · exact (R.adj_comm a b).mp h
    · exact h
    · exact h
    · exact ((pathGraph (r + 1)).adj_comm i j).mp h⟩
  loopless := ⟨fun u h => by
    rcases u with a | i
    · exact R.ne_of_adj h rfl
    · exact (pathGraph (r + 1)).ne_of_adj h rfl⟩

private lemma exists_path_pathGraph_h3 (d : ℕ) :
    ∀ k (hk : k ≤ d), ∃ q : (pathGraph (d + 1)).Walk 0 ⟨k, Nat.lt_succ_of_le hk⟩,
      q.IsPath ∧ q.length = k ∧ ∀ x ∈ q.support, x.1 ≤ k
  | 0, _ => ⟨Walk.nil, Walk.IsPath.nil, rfl, fun x hx => by
      change x ∈ [(0 : Fin (d + 1))] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact Nat.zero_le 0⟩
  | k + 1, hk => by
    obtain ⟨q, hq_path, hq_len, hq_le⟩ := exists_path_pathGraph_h3 d k (by omega)
    have hadj : (pathGraph (d + 1)).Adj ⟨k, by omega⟩ ⟨k + 1, Nat.lt_succ_of_le hk⟩ := by
      simp [pathGraph_adj]
    have hnot : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (d + 1)) ∉ q.support := by
      intro hmem
      have h := hq_le _ hmem
      dsimp at h
      omega
    refine ⟨q.concat hadj, hq_path.concat hnot hadj, by rw [Walk.length_concat, hq_len], fun x hx => ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := hq_le x hx; omega
    · simp

private lemma attachPath_diam_walk {A : Type} (R : SimpleGraph A) (root a₀ : A) (r : ℕ)
    (hR : R.IsTree) (ha₀ : R.dist a₀ root = r) :
    ∃ q : (attachPath R root r).Walk (Sum.inl a₀) (Sum.inr ⟨r, Nat.lt_succ_self r⟩),
      q.IsPath ∧ q.length = 2 * r + 1 ∧
      q.getVert r = Sum.inl root ∧ q.getVert (r + 1) = Sum.inr 0 := by
  obtain ⟨p₁, hp₁_path, hp₁_len⟩ := hR.connected.exists_path_of_dist a₀ root
  obtain ⟨p₂, hp₂_path, hp₂_len, _⟩ := exists_path_pathGraph_h3 r r le_rfl
  let f₁ : R →g attachPath R root r := ⟨Sum.inl, fun h => by dsimp only [attachPath]; exact h⟩
  let f₂ : pathGraph (r + 1) →g attachPath R root r :=
    ⟨Sum.inr, fun h => by dsimp only [attachPath]; exact h⟩
  have hf₁ : Function.Injective f₁ := Sum.inl_injective
  have hf₂ : Function.Injective f₂ := Sum.inr_injective
  let q₁ := p₁.map f₁
  let q₂ := p₂.map f₂
  have hq₁_path : q₁.IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp₁_path.support_nodup.map hf₁)
  have hq₂_path : q₂.IsPath :=
    (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hp₂_path.support_nodup.map hf₂)
  have hadj : (attachPath R root r).Adj (Sum.inl root) (Sum.inr (0 : Fin (r + 1))) := by
    simp [attachPath]
  have hdisj : ∀ x ∈ q₁.support, ∀ y ∈ q₂.support, x ≠ y := by
    intro x hx y hy
    rw [Walk.support_map, List.mem_map] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    exact Sum.inl_ne_inr
  let q := q₁.append (Walk.cons hadj q₂)
  have hq_supp : q.support = q₁.support ++ q₂.support := by
    dsimp [q]
    rw [Walk.support_append, Walk.support_cons, List.tail_cons]
  have hq_path : q.IsPath := by
    rw [Walk.isPath_def, hq_supp]
    exact List.nodup_append.mpr ⟨hq₁_path.support_nodup, hq₂_path.support_nodup, hdisj⟩
  have hq₁_len : q₁.length = r := by dsimp [q₁]; rw [Walk.length_map, hp₁_len, ha₀]
  have hq₂_len : q₂.length = r := by dsimp [q₂]; rw [Walk.length_map, hp₂_len]
  have hq_len : q.length = 2 * r + 1 := by
    dsimp [q]
    rw [Walk.length_append, Walk.length_cons, hq₁_len, hq₂_len]
    omega
  have hgv₁ : q.getVert r = Sum.inl root := by
    dsimp [q]
    rw [Walk.getVert_append]
    split_ifs with h
    · exfalso; omega
    · have h0 : r - q₁.length = 0 := by omega
      rw [h0, Walk.getVert_zero]
      rfl
  have hgv₂ : q.getVert (r + 1) = Sum.inr 0 := by
    dsimp [q]
    rw [Walk.getVert_append]
    split_ifs with h
    · exfalso; omega
    · have hsub : r + 1 - q₁.length = 1 := by omega
      rw [hsub, Walk.getVert_cons_succ, Walk.getVert_zero]
  exact ⟨q, hq_path, hq_len, hgv₁, hgv₂⟩

private lemma bicenter_path_mid_of_len {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x₀ y₀ : V} {q : T.Walk x₀ y₀} (hq_path : q.IsPath)
    (hq_len : q.length = 2 * r + 1) :
    (x₀ ∈ D.side₁ ∧ y₀ ∈ D.swap.side₁ ∧ q.getVert r = D.c₁ ∧ q.getVert (r + 1) = D.c₂) ∨
    (x₀ ∈ D.swap.side₁ ∧ y₀ ∈ D.side₁ ∧ q.getVert r = D.c₂ ∧ q.getVert (r + 1) = D.c₁) := by
  obtain ⟨r₀, hr₀_path, hr₀_len⟩ := D.hT.connected.exists_path_of_dist x₀ y₀
  have huniq_q := (D.hT.existsUnique_path x₀ y₀).unique hq_path hr₀_path
  have hdist_xy : T.dist x₀ y₀ = 2 * r + 1 := by rw [← hr₀_len, ← huniq_q, hq_len]
  have htri₁ : ∀ u v : V, u ∈ D.side₁ → v ∈ D.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₁ u hu
    have h2 := D.hle₁ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₁ + T.dist D.c₁ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₁) (v := v)] at h3
    omega
  have htri₂ : ∀ u v : V, u ∈ D.swap.side₁ → v ∈ D.swap.side₁ → T.dist u v ≤ 2 * r := by
    intro u v hu hv
    have h1 := D.hle₂ u hu
    have h2 := D.hle₂ v hv
    have h3 : T.dist u v ≤ T.dist u D.c₂ + T.dist D.c₂ v := D.hT.connected.dist_triangle
    rw [SimpleGraph.dist_comm (u := D.c₂) (v := v)] at h3
    omega
  have side_path : ∀ (Dc : BicenterData T r),
      ∀ u ∈ Dc.side₁, ∀ v ∈ Dc.swap.side₁, T.dist u v = 2 * r + 1 →
      ∀ w : T.Walk u v, w.IsPath → w.length = 2 * r + 1 →
      w.getVert r = Dc.c₁ ∧ w.getVert (r + 1) = Dc.c₂ := by
    intro Dc u hu v hv huv_d w hw_path hw_len
    obtain ⟨w₁, hw₁_path, hw₁_len⟩ := Dc.hT.connected.exists_path_of_dist u Dc.c₁
    obtain ⟨w₂, hw₂_path, hw₂_len⟩ := Dc.hT.connected.exists_path_of_dist Dc.c₂ v
    have hc₁_side : Dc.c₁ ∈ Dc.side₁ := mem_side₁_self Dc
    have hc₂_side : Dc.c₂ ∈ Dc.swap.side₁ := mem_side₁_self Dc.swap
    have h_no_c₂ : ∀ z ∈ w₁.support, z ∈ Dc.side₁ := by
      intro z hz
      obtain ⟨p_uz, p_zc, hp_uz, hp_zc, hw₁_app⟩ := hw₁_path.mem_support_iff_exists_append.mp hz
      by_contra hnot
      have hz₂ : z ∈ Dc.swap.side₁ := (lt_or_gt_of_ne (Dc.hne z)).resolve_left hnot
      have hdz : T.dist z Dc.c₁ = T.dist z Dc.c₂ + 1 := by
        have h_eq := Dc.hT.dist_eq_dist_add_one_of_adj z Dc.hadj
        change T.dist z Dc.c₂ < T.dist z Dc.c₁ at hz₂
        omega
      obtain ⟨p_zu, _⟩ := Dc.hT.connected.exists_path_of_dist z Dc.c₂
      have hlen_zc : T.dist z Dc.c₁ ≤ p_zc.length := dist_le p_zc
      have hlen_uz : T.dist u z ≤ p_uz.length := dist_le p_uz
      have hlen_sum : p_uz.length + p_zc.length = w₁.length := by rw [hw₁_app, Walk.length_append]
      have huc₂ : T.dist u Dc.c₂ = T.dist u Dc.c₁ + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj u Dc.hadj
        change T.dist u Dc.c₁ < T.dist u Dc.c₂ at hu
        omega
      have htri_u : T.dist u Dc.c₂ ≤ T.dist u z + T.dist z Dc.c₂ := Dc.hT.connected.dist_triangle
      omega
    have h_no_c₁ : ∀ z ∈ w₂.support, z ∈ Dc.swap.side₁ := by
      intro z hz
      obtain ⟨p_cz, p_zv, hp_cz, hp_zv, hw₂_app⟩ := hw₂_path.mem_support_iff_exists_append.mp hz
      by_contra hnot
      have hz₁ : z ∈ Dc.side₁ := (lt_or_gt_of_ne (Dc.hne z)).resolve_right hnot
      have hdz : T.dist z Dc.c₂ = T.dist z Dc.c₁ + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj z Dc.hadj
        change T.dist z Dc.c₁ < T.dist z Dc.c₂ at hz₁
        omega
      have hlen_cz : T.dist Dc.c₂ z ≤ p_cz.length := dist_le p_cz
      have hlen_zv : T.dist z v ≤ p_zv.length := dist_le p_zv
      have hlen_sum : p_cz.length + p_zv.length = w₂.length := by rw [hw₂_app, Walk.length_append]
      have hvc₁ : T.dist Dc.c₁ v = T.dist Dc.c₂ v + 1 := by
        have := Dc.hT.dist_eq_dist_add_one_of_adj v Dc.hadj
        change T.dist v Dc.c₂ < T.dist v Dc.c₁ at hv
        rw [SimpleGraph.dist_comm (u := Dc.c₁) (v := v), SimpleGraph.dist_comm (u := Dc.c₂) (v := v)]
        omega
      have htri_v : T.dist Dc.c₁ v ≤ T.dist Dc.c₁ z + T.dist z v := Dc.hT.connected.dist_triangle
      rw [SimpleGraph.dist_comm (u := Dc.c₁) (v := z)] at htri_v
      rw [SimpleGraph.dist_comm (u := Dc.c₂) (v := z)] at hlen_cz
      omega
    have hdisj : ∀ a ∈ w₁.support, ∀ b ∈ w₂.support, a ≠ b := by
      intro a ha b hb hab
      subst hab
      have h1 := h_no_c₂ a ha
      have h2 := h_no_c₁ a hb
      change T.dist a Dc.c₁ < T.dist a Dc.c₂ at h1
      change T.dist a Dc.c₂ < T.dist a Dc.c₁ at h2
      omega
    let w' : T.Walk u v := w₁.append (Walk.cons Dc.hadj w₂)
    have hw'_supp : w'.support = w₁.support ++ w₂.support := by
      dsimp [w']
      rw [Walk.support_append, Walk.support_cons, List.tail_cons]
    have hw'_path : w'.IsPath := by
      rw [Walk.isPath_def, hw'_supp]
      exact List.nodup_append.mpr ⟨hw₁_path.support_nodup, hw₂_path.support_nodup, hdisj⟩
    have hw_eq : w = w' := (Dc.hT.existsUnique_path u v).unique hw_path hw'_path
    have h1_le := Dc.hle₁ u hu
    have h2_le := Dc.hle₂ v hv
    have hdeq := Dc.hdist u v hu hv
    rw [SimpleGraph.dist_comm (u := Dc.c₂) (v := v)] at hdeq
    have hw₁_r : w₁.length = r := by omega
    rw [hw_eq]
    dsimp [w']
    constructor
    · rw [Walk.getVert_append]
      split_ifs with h
      · exfalso; omega
      · have h0 : r - w₁.length = 0 := by omega
        rw [h0, Walk.getVert_zero]
    · rw [Walk.getVert_append]
      split_ifs with h
      · exfalso; omega
      · have hsub : r + 1 - w₁.length = 1 := by omega
        rw [hsub, Walk.getVert_cons_succ, Walk.getVert_zero]
  rcases lt_or_gt_of_ne (D.hne x₀) with hx | hx <;> rcases lt_or_gt_of_ne (D.hne y₀) with hy | hy
  · exfalso; have := htri₁ x₀ y₀ hx hy; omega
  · have h := side_path D x₀ hx y₀ hy hdist_xy q hq_path hq_len
    exact Or.inl ⟨hx, hy, h.1, h.2⟩
  · have h := side_path D.swap x₀ hx y₀ hy hdist_xy q hq_path hq_len
    exact Or.inr ⟨hx, hy, h.1, h.2⟩
  · exfalso; have := htri₂ x₀ y₀ hx hy; omega

private lemma walk_mem_side_of_not_mem_other {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {x : V} (w : T.Walk x D.c₁) (hc₂ : D.c₂ ∉ w.support) :
    x ∈ D.side₁ := by
  by_contra hnot
  have hx₂ : x ∈ D.swap.side₁ := (lt_or_gt_of_ne (D.hne x)).resolve_left hnot
  obtain ⟨p, hp_path, hp_len⟩ := D.hT.connected.exists_path_of_dist x D.c₂
  have hc₁_not : D.c₁ ∉ p.support := by
    intro hc₁
    obtain ⟨q, hq_path, hq_len⟩ := D.hT.connected.exists_path_of_dist x D.c₁
    have heq := D.hT.isAcyclic.path_concat hq_path hp_path D.hadj hc₁
    have hlen_eq : p.length = q.length + 1 := by rw [heq, Walk.length_concat]
    change T.dist x D.c₂ < T.dist x D.c₁ at hx₂
    omega
  have hp_cat : (p.concat D.hadj.symm).IsPath := hp_path.concat hc₁_not D.hadj.symm
  have hw_path : w.toPath.val.IsPath := w.toPath.isPath
  have huniq := (D.hT.existsUnique_path x D.c₁).unique hw_path hp_cat
  apply hc₂
  apply Walk.support_toPath_subset_support
  rw [huniq, Walk.support_concat, List.mem_append, List.mem_singleton]
  left
  exact p.end_mem_support

private noncomputable def rootedCopies {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    Finset (Finset V) :=
  Finset.univ.filter fun S₁ : Finset V =>
    S₁ ⊆ D.A₁ ∧ D.c₁ ∈ S₁ ∧ ∃ φ : R ≃g T.induce (S₁ : Set V), (φ root).1 = D.c₁

private lemma mem_rootedCopies_iff {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) (S₁ : Finset V) :
    S₁ ∈ rootedCopies D R root ↔
      S₁ ⊆ D.A₁ ∧ D.c₁ ∈ S₁ ∧ ∃ φ : R ≃g T.induce (S₁ : Set V), (φ root).1 = D.c₁ := by
  simp [rootedCopies]

private lemma attachPath_decomp {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hR : R.IsTree) (hR_far : ∃ a₀ : A, R.dist a₀ root = r)
    (_hR_card : r + 2 ≤ Fintype.card A) (S : Finset V) :
    Nonempty (T.induce (S : Set V) ≃g attachPath R root r) ↔
      (S ∩ D.A₁ ∈ rootedCopies D R root ∧ S ∩ D.swap.A₁ ∈ rootedCopies D.swap (pathGraph (r + 1)) 0) ∨
      (S ∩ D.swap.A₁ ∈ rootedCopies D.swap R root ∧ S ∩ D.A₁ ∈ rootedCopies D (pathGraph (r + 1)) 0) := by
  constructor
  · rintro ⟨ψ⟩
    let φ : attachPath R root r ≃g T.induce (S : Set V) := ψ.symm
    obtain ⟨a₀, ha₀⟩ := hR_far
    obtain ⟨q_att, hq_att_path, hq_att_len, hgv₁, hgv₂⟩ := attachPath_diam_walk R root a₀ r hR ha₀
    let hom : attachPath R root r →g T := (SimpleGraph.Embedding.induce (S : Set V)).toHom.comp φ.toHom
    have hinj : Function.Injective hom := Subtype.val_injective.comp φ.injective
    let q := q_att.map hom
    have hq_path : q.IsPath :=
      (Walk.isPath_def _).mpr (by rw [Walk.support_map]; exact hq_att_path.support_nodup.map hinj)
    have hq_len : q.length = 2 * r + 1 := (Walk.length_map hom q_att).trans hq_att_len
    have hq_gv₁ : q.getVert r = (φ (Sum.inl root)).1 := by
      dsimp [q]
      rw [Walk.getVert_map, hgv₁]
      rfl
    have hq_gv₂ : q.getVert (r + 1) = (φ (Sum.inr 0)).1 := by
      dsimp [q]
      rw [Walk.getVert_map, hgv₂]
      rfl
    have hmid := bicenter_path_mid_of_len D hq_path hq_len
    have extract_pair : ∀ (Dc : BicenterData T r)
        (hc₁ : (φ (Sum.inl root)).1 = Dc.c₁) (hc₂ : (φ (Sum.inr 0)).1 = Dc.c₂),
        S ∩ Dc.A₁ ∈ rootedCopies Dc R root ∧
        S ∩ Dc.swap.A₁ ∈ rootedCopies Dc.swap (pathGraph (r + 1)) 0 := by
      intro Dc hc₁ hc₂
      have hin_side₁ : ∀ a : A, (φ (Sum.inl a)).1 ∈ Dc.side₁ := by
        intro a
        obtain ⟨pa, _⟩ := hR.connected.exists_path_of_dist a root
        let fR : R →g attachPath R root r := ⟨Sum.inl, fun h => by dsimp only [attachPath]; exact h⟩
        let w0 := (pa.map fR).map hom
        have hc₁' : hom (fR root) = Dc.c₁ := hc₁
        let w : T.Walk (hom (fR a)) Dc.c₁ := w0.copy rfl hc₁'
        change hom (fR a) ∈ Dc.side₁
        refine walk_mem_side_of_not_mem_other Dc w ?_
        intro hmem
        dsimp only [w, w0] at hmem
        rw [Walk.support_copy, Walk.support_map, Walk.support_map] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨_, ⟨u, _, rfl⟩, hu⟩ := hmem
        have h_eq : φ (Sum.inl u) = φ (Sum.inr 0) := Subtype.ext (hu.trans hc₂.symm)
        exact Sum.inl_ne_inr (φ.injective h_eq)
      have hin_side₂ : ∀ i : Fin (r + 1), (φ (Sum.inr i)).1 ∈ Dc.swap.side₁ := by
        intro i
        obtain ⟨pi⟩ := pathGraph_preconnected (r + 1) i 0
        let fP : pathGraph (r + 1) →g attachPath R root r :=
          ⟨Sum.inr, fun h => by dsimp only [attachPath]; exact h⟩
        let w0 := (pi.map fP).map hom
        have hc₂' : hom (fP 0) = Dc.swap.c₁ := hc₂
        let w : T.Walk (hom (fP i)) Dc.swap.c₁ := w0.copy rfl hc₂'
        change hom (fP i) ∈ Dc.swap.side₁
        refine walk_mem_side_of_not_mem_other Dc.swap w ?_
        intro hmem
        dsimp only [w, w0] at hmem
        rw [Walk.support_copy, Walk.support_map, Walk.support_map] at hmem
        simp only [List.mem_map] at hmem
        obtain ⟨_, ⟨j, _, rfl⟩, hj⟩ := hmem
        change (φ (Sum.inr j)).1 = Dc.c₁ at hj
        have h_eq : φ (Sum.inr j) = φ (Sum.inl root) := Subtype.ext (hj.trans hc₁.symm)
        exact Sum.inr_ne_inl (φ.injective h_eq)
      have hSA₁ : S ∩ Dc.A₁ = (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hxS, hxA⟩
          obtain ⟨u, hu⟩ := φ.surjective ⟨x, hxS⟩
          rcases u with a | i
          · exact ⟨a, congrArg Subtype.val hu⟩
          · exfalso
            have hx_eq : (φ (Sum.inr i)).1 = x := congrArg Subtype.val hu
            have hx2 : x ∈ Dc.swap.side₁ := hx_eq ▸ hin_side₂ i
            have hx1 : x ∈ Dc.side₁ := (mem_A₁_iff Dc).mp hxA
            change T.dist x Dc.c₁ < T.dist x Dc.c₂ at hx1
            change T.dist x Dc.c₂ < T.dist x Dc.c₁ at hx2
            omega
        · rintro ⟨a, rfl⟩
          exact ⟨(φ (Sum.inl a)).2, (mem_A₁_iff Dc).mpr (hin_side₁ a)⟩
      have hSA₂ : S ∩ Dc.swap.A₁ =
          (Finset.univ : Finset (Fin (r + 1))).image (fun i => (φ (Sum.inr i)).1) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hxS, hxA⟩
          obtain ⟨u, hu⟩ := φ.surjective ⟨x, hxS⟩
          rcases u with a | i
          · exfalso
            have hx_eq : (φ (Sum.inl a)).1 = x := congrArg Subtype.val hu
            have hx1 : x ∈ Dc.side₁ := hx_eq ▸ hin_side₁ a
            have hx2 : x ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp hxA
            change T.dist x Dc.c₁ < T.dist x Dc.c₂ at hx1
            change T.dist x Dc.c₂ < T.dist x Dc.c₁ at hx2
            omega
          · exact ⟨i, congrArg Subtype.val hu⟩
        · rintro ⟨i, rfl⟩
          exact ⟨(φ (Sum.inr i)).2, (mem_A₁_iff Dc.swap).mpr (hin_side₂ i)⟩
      constructor
      · rw [mem_rootedCopies_iff]
        refine ⟨Finset.inter_subset_right, ?_, ?_⟩
        · rw [hSA₁]
          exact Finset.mem_image.mpr ⟨root, Finset.mem_univ _, hc₁⟩
        · let φ₁ : R ≃g T.induce ((S ∩ Dc.A₁ : Finset V) : Set V) :=
            { toFun := fun a => ⟨(φ (Sum.inl a)).1, by
                rw [Finset.mem_coe, hSA₁]
                exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
              invFun := fun x => by
                have hx : x.1 ∈ (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
                  rw [← hSA₁]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose
              left_inv := fun a => by
                dsimp only
                have hx : (φ (Sum.inl a)).1 ∈
                    (Finset.univ : Finset A).image (fun a' => (φ (Sum.inl a')).1) :=
                  Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
                have hspec := (Finset.mem_image.mp hx).choose_spec.2
                exact Sum.inl_injective (φ.injective (Subtype.ext hspec))
              right_inv := fun x => by
                ext
                dsimp only
                have hx : x.1 ∈ (Finset.univ : Finset A).image (fun a => (φ (Sum.inl a)).1) := by
                  rw [← hSA₁]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose_spec.2
              map_rel_iff' := fun {a b} => by
                change T.Adj (φ (Sum.inl a)).1 (φ (Sum.inl b)).1 ↔ R.Adj a b
                simpa [attachPath, SimpleGraph.induce_adj] using
                  (φ.map_rel_iff (a := Sum.inl a) (b := Sum.inl b)) }
          exact ⟨φ₁, hc₁⟩
      · rw [mem_rootedCopies_iff]
        refine ⟨Finset.inter_subset_right, ?_, ?_⟩
        · rw [hSA₂]
          exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hc₂⟩
        · let φ₂ : pathGraph (r + 1) ≃g T.induce ((S ∩ Dc.swap.A₁ : Finset V) : Set V) :=
            { toFun := fun i => ⟨(φ (Sum.inr i)).1, by
                rw [Finset.mem_coe, hSA₂]
                exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
              invFun := fun x => by
                have hx : x.1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i => (φ (Sum.inr i)).1) := by
                  rw [← hSA₂]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose
              left_inv := fun i => by
                dsimp only
                have hx : (φ (Sum.inr i)).1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i' => (φ (Sum.inr i')).1) :=
                  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
                have hspec := (Finset.mem_image.mp hx).choose_spec.2
                exact Sum.inr_injective (φ.injective (Subtype.ext hspec))
              right_inv := fun x => by
                ext
                dsimp only
                have hx : x.1 ∈ (Finset.univ : Finset (Fin (r + 1))).image
                    (fun i => (φ (Sum.inr i)).1) := by
                  rw [← hSA₂]; exact Finset.mem_coe.mp x.2
                exact (Finset.mem_image.mp hx).choose_spec.2
              map_rel_iff' := fun {i j} => by
                change T.Adj (φ (Sum.inr i)).1 (φ (Sum.inr j)).1 ↔ (pathGraph (r + 1)).Adj i j
                simpa [attachPath, SimpleGraph.induce_adj] using
                  (φ.map_rel_iff (a := Sum.inr i) (b := Sum.inr j)) }
          exact ⟨φ₂, hc₂⟩
    rcases hmid with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩
    · exact Or.inl (extract_pair D (hq_gv₁ ▸ h1) (hq_gv₂ ▸ h2))
    · exact Or.inr (extract_pair D.swap (hq_gv₁ ▸ h1) (hq_gv₂ ▸ h2))
  · have build_iso : ∀ (Dc : BicenterData T r),
        S ∩ Dc.A₁ ∈ rootedCopies Dc R root →
        S ∩ Dc.swap.A₁ ∈ rootedCopies Dc.swap (pathGraph (r + 1)) 0 →
        Nonempty (T.induce (S : Set V) ≃g attachPath R root r) := by
      intro Dc h1 h2
      rw [mem_rootedCopies_iff] at h1 h2
      obtain ⟨hsub₁, hc₁_in, ⟨φ₁, hφ₁⟩⟩ := h1
      obtain ⟨hsub₂, hc₂_in, ⟨φ₂, hφ₂⟩⟩ := h2
      have hS_eq : (S ∩ Dc.A₁) ∪ (S ∩ Dc.swap.A₁) = S := by
        rw [← Finset.inter_union_distrib_left, union_A₁_swap Dc, Finset.inter_univ]
      have hdisj_SA : Disjoint (S ∩ Dc.A₁) (S ∩ Dc.swap.A₁) :=
        Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (disjoint_A₁_swap Dc)
      let φ : attachPath R root r ≃g T.induce (S : Set V) :=
        { toFun := Sum.elim
            (fun a => ⟨(φ₁ a).1, Finset.mem_coe.mpr (Finset.inter_subset_left (Finset.mem_coe.mp (φ₁ a).2))⟩)
            (fun i => ⟨(φ₂ i).1, Finset.mem_coe.mpr (Finset.inter_subset_left (Finset.mem_coe.mp (φ₂ i).2))⟩)
          invFun := fun x =>
            if hx : x.1 ∈ S ∩ Dc.A₁ then
              Sum.inl (φ₁.symm ⟨x.1, Finset.mem_coe.mpr hx⟩)
            else
              Sum.inr (φ₂.symm ⟨x.1, Finset.mem_coe.mpr
                ((Finset.mem_union.mp ((Finset.ext_iff.mp hS_eq x.1).mpr (Finset.mem_coe.mp x.2))).resolve_left hx)⟩)
          left_inv := fun u => by
            rcases u with a | i
            · dsimp only [Sum.elim_inl]
              have ha : (φ₁ a).1 ∈ S ∩ Dc.A₁ := Finset.mem_coe.mp (φ₁ a).2
              rw [dif_pos ha]
              simp
            · dsimp only [Sum.elim_inr]
              have hi : (φ₂ i).1 ∈ S ∩ Dc.swap.A₁ := Finset.mem_coe.mp (φ₂ i).2
              have hnot : (φ₂ i).1 ∉ S ∩ Dc.A₁ := Finset.disjoint_right.mp hdisj_SA hi
              rw [dif_neg hnot]
              simp
          right_inv := fun x => by
            ext
            dsimp only
            by_cases hx : x.1 ∈ S ∩ Dc.A₁
            · rw [dif_pos hx]
              dsimp only [Sum.elim_inl]
              exact congrArg Subtype.val (φ₁.apply_symm_apply ⟨x.1, Finset.mem_coe.mpr hx⟩)
            · rw [dif_neg hx]
              dsimp only [Sum.elim_inr]
              exact congrArg Subtype.val (φ₂.apply_symm_apply _)
          map_rel_iff' := fun {u v} => by
            rcases u with a | i <;> rcases v with b | j <;> dsimp only [attachPath]
            · change T.Adj (φ₁ a).1 (φ₁ b).1 ↔ R.Adj a b
              simpa [SimpleGraph.induce_adj] using (φ₁.map_rel_iff (a := a) (b := b))
            · change T.Adj (φ₁ a).1 (φ₂ j).1 ↔ a = root ∧ j.1 = 0
              have ha_side : (φ₁ a).1 ∈ Dc.side₁ := (mem_A₁_iff Dc).mp (hsub₁ (Finset.mem_coe.mp (φ₁ a).2))
              have hj_side : (φ₂ j).1 ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp (hsub₂ (Finset.mem_coe.mp (φ₂ j).2))
              constructor
              · intro hadj
                obtain ⟨hxa, hyj⟩ := eq_center_of_adj_across Dc ha_side hj_side hadj
                have ha_eq : a = root := φ₁.injective (Subtype.ext (hxa.trans hφ₁.symm))
                have hj_eq : j = 0 := φ₂.injective (Subtype.ext (hyj.trans hφ₂.symm))
                exact ⟨ha_eq, by simp [hj_eq]⟩
              · rintro ⟨rfl, hj0⟩
                have hj_eq : j = 0 := Fin.ext hj0
                subst hj_eq
                rw [hφ₁, hφ₂]
                exact Dc.hadj
            · change T.Adj (φ₂ i).1 (φ₁ b).1 ↔ b = root ∧ i.1 = 0
              have hb_side : (φ₁ b).1 ∈ Dc.side₁ := (mem_A₁_iff Dc).mp (hsub₁ (Finset.mem_coe.mp (φ₁ b).2))
              have hi_side : (φ₂ i).1 ∈ Dc.swap.side₁ := (mem_A₁_iff Dc.swap).mp (hsub₂ (Finset.mem_coe.mp (φ₂ i).2))
              rw [adj_comm]
              constructor
              · intro hadj
                obtain ⟨hxb, hyi⟩ := eq_center_of_adj_across Dc hb_side hi_side hadj
                have hb_eq : b = root := φ₁.injective (Subtype.ext (hxb.trans hφ₁.symm))
                have hi_eq : i = 0 := φ₂.injective (Subtype.ext (hyi.trans hφ₂.symm))
                exact ⟨hb_eq, by simp [hi_eq]⟩
              · rintro ⟨rfl, hi0⟩
                have hi_eq : i = 0 := Fin.ext hi0
                subst hi_eq
                rw [hφ₁, hφ₂]
                exact Dc.hadj
            · change T.Adj (φ₂ i).1 (φ₂ j).1 ↔ (pathGraph (r + 1)).Adj i j
              simpa [SimpleGraph.induce_adj] using (φ₂.map_rel_iff (a := i) (b := j)) }
      exact ⟨φ.symm⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact build_iso D h1 h2
    · exact build_iso D.swap h1 h2

private lemma ncard_attachPath_eq {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hR : R.IsTree) (hR_far : ∃ a₀ : A, R.dist a₀ root = r)
    (hR_card : r + 2 ≤ Fintype.card A) :
    {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)}.ncard =
      (rootedCopies D R root).card * (rootedCopies D.swap (pathGraph (r + 1)) 0).card +
      (rootedCopies D.swap R root).card * (rootedCopies D (pathGraph (r + 1)) 0).card := by
  let F_all : Finset (Finset V) :=
    Finset.univ.filter fun S => Nonempty (T.induce (S : Set V) ≃g attachPath R root r)
  have hncard : {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)}.ncard =
      F_all.card := by
    have hset : {S : Finset V | Nonempty (T.induce (S : Set V) ≃g attachPath R root r)} =
        (F_all : Set (Finset V)) := by
      ext S; simp [F_all]
    rw [hset, Set.ncard_coe_finset]
  rw [hncard]
  let F₁ : Finset (Finset V) :=
    (rootedCopies D R root ×ˢ rootedCopies D.swap (pathGraph (r + 1)) 0).image (fun p => p.1 ∪ p.2)
  let F₂ : Finset (Finset V) :=
    (rootedCopies D.swap R root ×ˢ rootedCopies D (pathGraph (r + 1)) 0).image (fun p => p.1 ∪ p.2)
  have hF_eq : F_all = F₁ ∪ F₂ := by
    ext S
    simp only [F_all, F₁, F₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image, Finset.mem_product, Prod.exists]
    rw [attachPath_decomp D hR hR_far hR_card]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        refine ⟨S ∩ D.A₁, S ∩ D.swap.A₁, ⟨h1, h2⟩, ?_⟩
        rw [← Finset.inter_union_distrib_left, union_A₁_swap D, Finset.inter_univ]
      · right
        refine ⟨S ∩ D.swap.A₁, S ∩ D.A₁, ⟨h1, h2⟩, ?_⟩
        rw [← Finset.inter_union_distrib_left, Finset.union_comm D.swap.A₁ D.A₁,
          union_A₁_swap D, Finset.inter_univ]
    · rintro (⟨S₁, S₂, ⟨h1, h2⟩, rfl⟩ | ⟨S₁, S₂, ⟨h1, h2⟩, rfl⟩)
      · left
        have hs₁ : S₁ ⊆ D.A₁ := ((mem_rootedCopies_iff D R root S₁).mp h1).1
        have hs₂ : S₂ ⊆ D.swap.A₁ := ((mem_rootedCopies_iff D.swap (pathGraph (r + 1)) 0 S₂).mp h2).1
        have hdisj₁ : Disjoint S₂ D.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D).symm
        have hdisj₂ : Disjoint S₁ D.swap.A₁ := Disjoint.mono_left hs₁ (disjoint_A₁_swap D)
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
          Finset.disjoint_iff_inter_eq_empty.mp hdisj₁, Finset.union_empty]
        rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj₂,
          Finset.empty_union, Finset.inter_eq_left.mpr hs₂]
        exact ⟨h1, h2⟩
      · right
        have hs₁ : S₁ ⊆ D.swap.A₁ := ((mem_rootedCopies_iff D.swap R root S₁).mp h1).1
        have hs₂ : S₂ ⊆ D.A₁ := ((mem_rootedCopies_iff D (pathGraph (r + 1)) 0 S₂).mp h2).1
        have hdisj₁ : Disjoint S₂ D.swap.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D)
        have hdisj₂ : Disjoint S₁ D.A₁ := Disjoint.mono_left hs₁ (disjoint_A₁_swap D).symm
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
          Finset.disjoint_iff_inter_eq_empty.mp hdisj₁, Finset.union_empty]
        rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj₂,
          Finset.empty_union, Finset.inter_eq_left.mpr hs₂]
        exact ⟨h1, h2⟩
  have hF_disj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    rw [Finset.mem_image] at hS₁ hS₂
    obtain ⟨⟨S₁, S₂⟩, hmem₁, rfl⟩ := hS₁
    obtain ⟨⟨T₁, T₂⟩, hmem₂, heq⟩ := hS₂
    rw [Finset.mem_product, mem_rootedCopies_iff, mem_rootedCopies_iff] at hmem₁ hmem₂
    have hs₁ : S₁ ⊆ D.A₁ := hmem₁.1.1
    have hs₂ : S₂ ⊆ D.swap.A₁ := hmem₁.2.1
    have ht₁ : T₁ ⊆ D.swap.A₁ := hmem₂.1.1
    have ht₂ : T₂ ⊆ D.A₁ := hmem₂.2.1
    have hdisj_s₂ : Disjoint S₂ D.A₁ := Disjoint.mono_left hs₂ (disjoint_A₁_swap D).symm
    have hdisj_t₁ : Disjoint T₁ D.A₁ := Disjoint.mono_left ht₁ (disjoint_A₁_swap D).symm
    have h_inter : S₁ = T₂ := by
      have h := congrArg (· ∩ D.A₁) heq
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hs₁,
        Finset.inter_eq_left.mpr ht₂, Finset.disjoint_iff_inter_eq_empty.mp hdisj_s₂,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj_t₁] using h.symm
    obtain ⟨φ₁, _⟩ := hmem₁.1.2.2
    obtain ⟨φ₂, _⟩ := hmem₂.2.2.2
    have hc₁ : S₁.card = Fintype.card A := by
      simpa using (Fintype.card_congr φ₁.toEquiv).symm
    have hc₂ : T₂.card = r + 1 := by
      simpa using (Fintype.card_congr φ₂.toEquiv).symm
    have h_card_inter : S₁.card = T₂.card := congrArg Finset.card h_inter
    omega
  have hinj_pair : ∀ (Dc₁ Dc₂ : BicenterData T r), Disjoint Dc₁.A₁ Dc₂.A₁ →
      ∀ {B : Type} [Fintype B] (RB : SimpleGraph B) (rB : B),
      Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2)
        ((rootedCopies Dc₁ R root ×ˢ rootedCopies Dc₂ RB rB : Finset (Finset V × Finset V)) :
          Set (Finset V × Finset V)) := by
    intro Dc₁ Dc₂ hdisj B _ RB rB ⟨S₁, S₂⟩ h1 ⟨T₁, T₂⟩ h2 heq
    rw [Finset.mem_coe, Finset.mem_product, mem_rootedCopies_iff, mem_rootedCopies_iff] at h1 h2
    have h_1 : S₁ = T₁ := by
      have h := congrArg (· ∩ Dc₁.A₁) heq
      have hd1 : Disjoint S₂ Dc₁.A₁ := Disjoint.mono_left h1.2.1 hdisj.symm
      have hd2 : Disjoint T₂ Dc₁.A₁ := Disjoint.mono_left h2.2.1 hdisj.symm
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1.1.1,
        Finset.inter_eq_left.mpr h2.1.1, Finset.disjoint_iff_inter_eq_empty.mp hd1,
        Finset.disjoint_iff_inter_eq_empty.mp hd2] using h
    have h_2 : S₂ = T₂ := by
      have h := congrArg (· ∩ Dc₂.A₁) heq
      have hd1 : Disjoint S₁ Dc₂.A₁ := Disjoint.mono_left h1.1.1 hdisj
      have hd2 : Disjoint T₁ Dc₂.A₁ := Disjoint.mono_left h2.1.1 hdisj
      simpa [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr h1.2.1,
        Finset.inter_eq_left.mpr h2.2.1, Finset.disjoint_iff_inter_eq_empty.mp hd1,
        Finset.disjoint_iff_inter_eq_empty.mp hd2] using h
    exact Prod.ext h_1 h_2
  rw [hF_eq, Finset.card_union_of_disjoint hF_disj]
  dsimp only [F₁, F₂]
  rw [Finset.card_image_of_injOn (hinj_pair D D.swap (disjoint_A₁_swap D) (pathGraph (r + 1)) 0),
    Finset.card_product,
    Finset.card_image_of_injOn (hinj_pair D.swap D (disjoint_A₁_swap D).symm (pathGraph (r + 1)) 0),
    Finset.card_product]

private lemma mem_rootedCopies_self {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : D.A₁ ∈ rootedCopies D D.T₁ D.root₁ := by
  rw [mem_rootedCopies_iff]
  refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
  let φ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
    { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
      invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := fun {_ _} => Iff.rfl }
  exact ⟨φ, rfl⟩

private lemma rootedCopies_rays_pos {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) : 0 < (rootedCopies D (pathGraph (r + 1)) 0).card := by
  obtain ⟨a₀, ha₀⟩ := exists_far_vertex D
  obtain ⟨p, hp_path, hp_len⟩ := D.ht_side₁.connected.exists_path_of_dist a₀ D.root₁
  let p' := p.reverse
  have hp'_path : p'.IsPath := hp_path.reverse
  have hp'_len : p'.length = r := by dsimp [p']; rw [Walk.length_reverse, hp_len, ha₀]
  let P : Finset V := (p'.support.map Subtype.val).toFinset
  have hP_sub : P ⊆ D.A₁ := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact (mem_A₁_iff D).mpr y.2
  have hc₁_P : D.c₁ ∈ P := by
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨D.root₁, p'.start_mem_support, rfl⟩
  let φ : pathGraph (r + 1) ≃g T.induce (P : Set V) :=
    { toFun := fun i => ⟨(p'.getVert i.1).1, by
        rw [Finset.mem_coe, List.mem_toFinset, List.mem_map]
        exact ⟨p'.getVert i.1, p'.getVert_mem_support i.1, rfl⟩⟩
      invFun := fun x => ⟨(p'.support.map Subtype.val).idxOf x.1, by
        have hmem := List.mem_toFinset.mp (Finset.mem_coe.mp x.2)
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [List.length_map, p'.length_support, hp'_len] at hlt
        exact hlt⟩
      left_inv := fun i => by
        ext
        dsimp
        have hi_lt : i.1 < (p'.support.map Subtype.val).length := by
          rw [List.length_map, p'.length_support, hp'_len]; exact i.isLt
        have hnodup : (p'.support.map Subtype.val).Nodup :=
          hp'_path.support_nodup.map Subtype.val_injective
        rw [p'.getVert_eq_support_getElem (by omega : i.1 ≤ p'.length)]
        have hget : (p'.support[i.1]' (by rw [p'.length_support, hp'_len]; exact i.isLt)).1 =
            (p'.support.map Subtype.val)[i.1]' hi_lt := by simp
        rw [hget]
        exact hnodup.idxOf_getElem i.1 hi_lt
      right_inv := fun x => by
        ext
        dsimp
        have hmem : x.1 ∈ p'.support.map Subtype.val := List.mem_toFinset.mp (Finset.mem_coe.mp x.2)
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [p'.getVert_eq_support_getElem (by rw [List.length_map, p'.length_support] at hlt; omega)]
        have hget : (p'.support[(p'.support.map Subtype.val).idxOf x.1]'
            (by rw [List.length_map] at hlt; exact hlt)).1 =
            (p'.support.map Subtype.val)[(p'.support.map Subtype.val).idxOf x.1]' hlt :=
          (List.getElem_map (f := Subtype.val)).symm
        rw [hget]
        exact List.getElem_idxOf hlt
      map_rel_iff' := fun {i j} => by
        change T.Adj (p'.getVert i.1).1 (p'.getVert j.1).1 ↔ (pathGraph (r + 1)).Adj i j
        have hadj_iff : ∀ a b : Fin (r + 1), a.1 ≤ b.1 →
            (T.Adj (p'.getVert a.1).1 (p'.getVert b.1).1 ↔ a.1 + 1 = b.1) := by
          intro a b hab
          constructor
          · intro hadj
            have hadj_sub : D.T₁.Adj (p'.getVert a.1) (p'.getVert b.1) := hadj
            let q := (p'.drop a.1).take (b.1 - a.1)
            have hsub : q.IsSubwalk p' := (Walk.isSubwalk_take _ _).trans (Walk.isSubwalk_drop _ _)
            have hp'_dist : p'.length = D.T₁.dist D.root₁ a₀ :=
              hp'_len.trans (SimpleGraph.dist_comm.trans ha₀).symm
            have hdist_eq : q.length = D.T₁.dist (p'.getVert a.1) ((p'.drop a.1).getVert (b.1 - a.1)) :=
              length_eq_dist_of_subwalk hp'_dist hsub
            have hql : q.length = b.1 - a.1 := by
              dsimp [q]
              rw [Walk.take_length, Walk.drop_length]
              have := b.isLt
              omega
            have hdv : D.T₁.dist (p'.getVert a.1) ((p'.drop a.1).getVert (b.1 - a.1)) = 1 := by
              rw [Walk.drop_getVert, Nat.add_sub_of_le hab, dist_eq_one_iff_adj.mpr hadj_sub]
            omega
          · intro hsucc
            rw [← hsucc]
            exact p'.adj_getVert_succ (by omega)
        rw [pathGraph_adj]
        rcases le_total i.1 j.1 with hij | hji
        · rw [hadj_iff i j hij]
          constructor
          · exact Or.inl
          · rintro (h | h) <;> omega
        · rw [adj_comm, hadj_iff j i hji]
          constructor
          · exact Or.inr
          · rintro (h | h) <;> omega }
  refine Finset.card_pos.mpr ⟨P, ?_⟩
  rw [mem_rootedCopies_iff]
  exact ⟨hP_sub, hc₁_P, φ, by
    dsimp [φ]
    rw [Walk.getVert_zero]
    rfl⟩

private lemma rootedCopies_nonempty_implies_le_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hpos : 0 < (rootedCopies D R root).card) : Fintype.card A ≤ D.A₁.card := by
  obtain ⟨S₁, hS₁⟩ := Finset.card_pos.mp hpos
  rw [mem_rootedCopies_iff] at hS₁
  obtain ⟨hsub, _, ⟨φ, _⟩⟩ := hS₁
  have hc : Fintype.card A = S₁.card := by
    simpa using Fintype.card_congr φ.toEquiv
  exact hc ▸ Finset.card_le_card hsub

private lemma rootedCopies_eq_one_of_eq_card {V : Type} [Fintype V] {T : SimpleGraph V} {r : ℕ}
    (D : BicenterData T r) {A : Type} [Fintype A] {R : SimpleGraph A} {root : A}
    (hcard : Fintype.card A = D.A₁.card) :
    (0 < (rootedCopies D R root).card ↔ RootedIso D.T₁ D.root₁ R root) ∧
    (RootedIso D.T₁ D.root₁ R root → (rootedCopies D R root).card = 1) := by
  have hsub_eq : ∀ S₁ ∈ rootedCopies D R root, S₁ = D.A₁ := by
    intro S₁ hS₁
    rw [mem_rootedCopies_iff] at hS₁
    obtain ⟨hsub, _, ⟨φ, _⟩⟩ := hS₁
    have hc : S₁.card = Fintype.card A := by simpa using (Fintype.card_congr φ.toEquiv).symm
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · constructor
    · intro hpos
      obtain ⟨S₁, hS₁⟩ := Finset.card_pos.mp hpos
      have heq := hsub_eq S₁ hS₁
      subst heq
      rw [mem_rootedCopies_iff] at hS₁
      obtain ⟨_, _, ⟨φ, hφ⟩⟩ := hS₁
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨ψ.trans φ.symm, by
        dsimp [ψ, BicenterData.root₁]
        exact φ.symm_apply_eq.mpr (Subtype.ext hφ.symm)⟩
    · rintro ⟨φ, hφ⟩
      refine Finset.card_pos.mpr ⟨D.A₁, ?_⟩
      rw [mem_rootedCopies_iff]
      refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨φ.symm.trans ψ, by
        dsimp [ψ]
        have h1 : φ.symm root = D.root₁ := φ.symm_apply_eq.mpr hφ.symm
        rw [h1]
        rfl⟩
  · intro h_iso
    have hpos : 0 < (rootedCopies D R root).card := by
      obtain ⟨φ, hφ⟩ := h_iso
      refine Finset.card_pos.mpr ⟨D.A₁, ?_⟩
      rw [mem_rootedCopies_iff]
      refine ⟨Finset.Subset.refl _, mem_A₁_self D, ?_⟩
      let ψ : D.T₁ ≃g T.induce (D.A₁ : Set V) :=
        { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr ((mem_A₁_iff D).mpr x.2)⟩
          invFun := fun x => ⟨x.1, (mem_A₁_iff D).mp (Finset.mem_coe.mp x.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := fun {_ _} => Iff.rfl }
      exact ⟨φ.symm.trans ψ, by
        dsimp [ψ]
        have h1 : φ.symm root = D.root₁ := φ.symm_apply_eq.mpr hφ.symm
        rw [h1]
        rfl⟩
    have hle1 : (rootedCopies D R root).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [hsub_eq a ha, hsub_eq b hb]
    omega

private lemma rootedCopies_card_le_of_rootedIso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hiso : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    (rootedCopies DG R root).card ≤ (rootedCopies DH R root).card := by
  obtain ⟨ψ, hψ⟩ := hiso
  let mapS : Finset V → Finset W := fun S₁ =>
    (Finset.univ.filter (fun y : DH.side₁ => (ψ.symm y).1 ∈ S₁)).image Subtype.val
  refine Finset.card_le_card_of_injOn mapS ?_ ?_
  · intro S₁ hS₁
    rw [Finset.mem_coe, mem_rootedCopies_iff] at hS₁ ⊢
    obtain ⟨hsub, hc₁, ⟨φ, hφ⟩⟩ := hS₁
    have hc₁_map : DH.c₁ ∈ mapS S₁ := by
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨DH.root₁, ?_, rfl⟩
      have hsym : ψ.symm DH.root₁ = DG.root₁ := ψ.symm_apply_eq.mpr hψ.symm
      rw [hsym]
      exact hc₁
    have hmem_map_side : ∀ {w : W}, w ∈ mapS S₁ → w ∈ DH.side₁ := by
      intro w hw
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      obtain ⟨y', _, rfl⟩ := hw
      exact y'.2
    have hmem_map_inv : ∀ {w : W} (hw : w ∈ mapS S₁),
        (ψ.symm ⟨w, hmem_map_side hw⟩).1 ∈ S₁ := by
      intro w hw
      have hw0 := hw
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
      obtain ⟨y', hy'_in, hy'_eq⟩ := hw0
      have : (⟨w, hmem_map_side hw⟩ : DH.side₁) = y' := Subtype.ext hy'_eq.symm
      rw [this]
      exact hy'_in
    have hmem_to_map : ∀ x : (S₁ : Set V),
        (ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩).1 ∈ mapS S₁ := by
      intro x
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩,
        by rw [ψ.symm_apply_apply]; exact Finset.mem_coe.mp x.2, rfl⟩
    let ψS : G.induce (S₁ : Set V) ≃g H.induce (mapS S₁ : Set W) :=
      { toFun := fun x =>
          ⟨(ψ ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩).1,
            Finset.mem_coe.mpr (hmem_to_map x)⟩
        invFun := fun y =>
          ⟨(ψ.symm ⟨y.1, hmem_map_side (Finset.mem_coe.mp y.2)⟩).1,
            Finset.mem_coe.mpr (hmem_map_inv (Finset.mem_coe.mp y.2))⟩
        left_inv := fun x => by
          ext
          dsimp only
          exact congrArg (Subtype.val : DG.side₁ → V)
            (ψ.symm_apply_apply ⟨x.1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp x.2))⟩)
        right_inv := fun y => by
          ext
          dsimp only
          exact congrArg (Subtype.val : DH.side₁ → W)
            (ψ.apply_symm_apply ⟨y.1, hmem_map_side (Finset.mem_coe.mp y.2)⟩)
        map_rel_iff' := fun {a b} => ψ.map_rel_iff }
    have hroot : (⟨(φ root).1, (mem_A₁_iff DG).mp (hsub (Finset.mem_coe.mp (φ root).2))⟩ : DG.side₁) =
        DG.root₁ := Subtype.ext hφ
    refine ⟨fun y hy => (mem_A₁_iff DH).mpr (hmem_map_side hy), hc₁_map, φ.trans ψS, ?_⟩
    exact (congrArg (fun z => (ψ z).1) hroot).trans (congrArg Subtype.val hψ)
  · intro S₁ hS₁ S₂ hS₂ heq
    rw [Finset.mem_coe, mem_rootedCopies_iff] at hS₁ hS₂
    ext x
    by_cases hx : x ∈ DG.A₁
    · let x_sub : DG.side₁ := ⟨x, (mem_A₁_iff DG).mp hx⟩
      have hm := Finset.ext_iff.mp heq (ψ x_sub).1
      simp only [mapS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      constructor <;> intro hxS
      · obtain ⟨y', hy', hy'_eq⟩ := hm.mp ⟨ψ x_sub, by simpa using hxS, rfl⟩
        have : y' = ψ x_sub := Subtype.ext hy'_eq
        rw [this, ψ.symm_apply_apply] at hy'
        exact hy'
      · obtain ⟨y', hy', hy'_eq⟩ := hm.mpr ⟨ψ x_sub, by simpa using hxS, rfl⟩
        have : y' = ψ x_sub := Subtype.ext hy'_eq
        rw [this, ψ.symm_apply_apply] at hy'
        exact hy'
    · exact ⟨fun h => False.elim (hx (hS₁.1 h)), fun h => False.elim (hx (hS₂.1 h))⟩

private lemma rootedCopies_card_eq_of_rootedIso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hiso : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    {A : Type} [Fintype A] (R : SimpleGraph A) (root : A) :
    (rootedCopies DG R root).card = (rootedCopies DH R root).card :=
  le_antisymm (rootedCopies_card_le_of_rootedIso DG DH hiso R root)
    (rootedCopies_card_le_of_rootedIso DH DG hiso.symm R root)

private lemma glue_bicenter_iso {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (DG : BicenterData G r) (DH : BicenterData H r)
    (h1 : RootedIso DG.T₁ DG.root₁ DH.T₁ DH.root₁)
    (h2 : RootedIso DG.swap.T₁ DG.swap.root₁ DH.swap.T₁ DH.swap.root₁) :
    Nonempty (G ≃g H) := by
  obtain ⟨φ₁, hφ₁⟩ := h1
  obtain ⟨φ₂, hφ₂⟩ := h2
  let toF : V → W := fun x =>
    if hx : x ∈ DG.side₁ then (φ₁ ⟨x, hx⟩).1
    else (φ₂ ⟨x, mem_swap_side₁_of_not_mem DG hx⟩).1
  let invF : W → V := fun y =>
    if hy : y ∈ DH.side₁ then (φ₁.symm ⟨y, hy⟩).1
    else (φ₂.symm ⟨y, mem_swap_side₁_of_not_mem DH hy⟩).1
  have hleft : Function.LeftInverse invF toF := by
    intro x
    dsimp only [toF, invF]
    by_cases hx : x ∈ DG.side₁
    · rw [dif_pos hx, dif_pos (φ₁ ⟨x, hx⟩).2]
      simp
    · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
      have hnot : (φ₂ ⟨x, hx2⟩).1 ∉ DH.side₁ := by
        intro hmem
        have hmem2 : (φ₂ ⟨x, hx2⟩).1 ∈ DH.swap.side₁ := (φ₂ ⟨x, hx2⟩).2
        change H.dist _ DH.c₁ < H.dist _ DH.c₂ at hmem
        change H.dist _ DH.c₂ < H.dist _ DH.c₁ at hmem2
        omega
      rw [dif_neg hx, dif_neg hnot]
      simp
  have hright : Function.RightInverse invF toF := by
    intro y
    dsimp only [toF, invF]
    by_cases hy : y ∈ DH.side₁
    · rw [dif_pos hy, dif_pos (φ₁.symm ⟨y, hy⟩).2]
      simp
    · have hy2 : y ∈ DH.swap.side₁ := mem_swap_side₁_of_not_mem DH hy
      have hnot : (φ₂.symm ⟨y, hy2⟩).1 ∉ DG.side₁ := by
        intro hmem
        have hmem2 : (φ₂.symm ⟨y, hy2⟩).1 ∈ DG.swap.side₁ := (φ₂.symm ⟨y, hy2⟩).2
        change G.dist _ DG.c₁ < G.dist _ DG.c₂ at hmem
        change G.dist _ DG.c₂ < G.dist _ DG.c₁ at hmem2
        omega
      rw [dif_neg hy, dif_neg hnot]
      simp
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro x y
  dsimp only [Equiv.coe_fn_mk, toF]
  by_cases hx : x ∈ DG.side₁ <;> by_cases hy : y ∈ DG.side₁
  · rw [dif_pos hx, dif_pos hy]
    exact φ₁.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  · have hy2 : y ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hy
    rw [dif_pos hx, dif_neg hy]
    constructor
    · intro hadj
      obtain ⟨hx_c, hy_c⟩ := eq_center_of_adj_across DH (φ₁ ⟨x, hx⟩).2 (φ₂ ⟨y, hy2⟩).2 hadj
      have hx1 : (⟨x, hx⟩ : DG.side₁) = DG.root₁ :=
        φ₁.injective (Subtype.ext (hx_c.trans (congrArg Subtype.val hφ₁).symm))
      have hy1 : (⟨y, hy2⟩ : DG.swap.side₁) = DG.swap.root₁ :=
        φ₂.injective (Subtype.ext (hy_c.trans (congrArg Subtype.val hφ₂).symm))
      have hx_eq : x = DG.c₁ := congrArg Subtype.val hx1
      have hy_eq : y = DG.c₂ := congrArg Subtype.val hy1
      rw [hx_eq, hy_eq]
      exact DG.hadj
    · intro hadj
      obtain ⟨hx_c, hy_c⟩ := eq_center_of_adj_across DG hx hy2 hadj
      have hx1 : (⟨x, hx⟩ : DG.side₁) = DG.root₁ := Subtype.ext hx_c
      have hy1 : (⟨y, hy2⟩ : DG.swap.side₁) = DG.swap.root₁ := Subtype.ext hy_c
      rw [hx1, hy1, hφ₁, hφ₂]
      exact DH.hadj
  · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
    rw [dif_neg hx, dif_pos hy]
    rw [adj_comm, adj_comm (G := G)]
    constructor
    · intro hadj
      obtain ⟨hy_c, hx_c⟩ := eq_center_of_adj_across DH (φ₁ ⟨y, hy⟩).2 (φ₂ ⟨x, hx2⟩).2 hadj
      have hy1 : (⟨y, hy⟩ : DG.side₁) = DG.root₁ :=
        φ₁.injective (Subtype.ext (hy_c.trans (congrArg Subtype.val hφ₁).symm))
      have hx1 : (⟨x, hx2⟩ : DG.swap.side₁) = DG.swap.root₁ :=
        φ₂.injective (Subtype.ext (hx_c.trans (congrArg Subtype.val hφ₂).symm))
      have hy_eq : y = DG.c₁ := congrArg Subtype.val hy1
      have hx_eq : x = DG.c₂ := congrArg Subtype.val hx1
      rw [hy_eq, hx_eq]
      exact DG.hadj
    · intro hadj
      obtain ⟨hy_c, hx_c⟩ := eq_center_of_adj_across DG hy hx2 hadj
      have hy1 : (⟨y, hy⟩ : DG.side₁) = DG.root₁ := Subtype.ext hy_c
      have hx1 : (⟨x, hx2⟩ : DG.swap.side₁) = DG.swap.root₁ := Subtype.ext hx_c
      rw [hy1, hx1, hφ₁, hφ₂]
      exact DH.hadj
  · have hx2 : x ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hx
    have hy2 : y ∈ DG.swap.side₁ := mem_swap_side₁_of_not_mem DG hy
    rw [dif_neg hx, dif_neg hy]
    exact φ₂.map_rel_iff (a := ⟨x, hx2⟩) (b := ⟨y, hy2⟩)

private lemma h3_max_side {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {r : ℕ}
    (hcard : Fintype.card V = Fintype.card W)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      Fintype.card U < Fintype.card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (DG : BicenterData G r) (DH : BicenterData H r)
    (hmax1 : DG.swap.A₁.card ≤ DG.A₁.card)
    (hmax2 : DH.A₁.card ≤ DG.A₁.card)
    (hmax3 : DH.swap.A₁.card ≤ DG.A₁.card) :
    Nonempty (G ≃g H) := by
  have hlt₁ : Fintype.card (DG.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
    rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
    have h2 : r + 2 ≤ DG.swap.A₁.card := by rw [A₁_card_eq_ncard]; exact DG.hbig₂
    have hsum := card_A₁_add_swap DG
    omega
  have hG_big : r + 2 ≤ Fintype.card DG.side₁ := by
    rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DG.hbig₁
  have hQ₁ := hkelly (DG.side₁ ⊕ Fin (r + 1)) (attachPath DG.T₁ DG.root₁ r) hlt₁
  rw [ncard_attachPath_eq DG DG.ht_side₁ (exists_far_vertex DG) hG_big,
    ncard_attachPath_eq DH DG.ht_side₁ (exists_far_vertex DG) hG_big] at hQ₁
  have h_pos_G : 0 < (rootedCopies DG DG.T₁ DG.root₁).card *
      (rootedCopies DG.swap (pathGraph (r + 1)) 0).card :=
    Nat.mul_pos (Finset.card_pos.mpr ⟨DG.A₁, mem_rootedCopies_self DG⟩)
      (rootedCopies_rays_pos DG.swap)
  have h_pos_H : 0 < (rootedCopies DH DG.T₁ DG.root₁).card *
      (rootedCopies DH.swap (pathGraph (r + 1)) 0).card +
      (rootedCopies DH.swap DG.T₁ DG.root₁).card *
      (rootedCopies DH (pathGraph (r + 1)) 0).card := by omega
  have choose_side : ∀ (DH' : BicenterData H r),
      DH'.A₁.card ≤ DG.A₁.card → DH'.swap.A₁.card ≤ DG.A₁.card →
      0 < (rootedCopies DH' DG.T₁ DG.root₁).card →
      Nonempty (G ≃g H) := by
    intro DH' hleA hleB hpos_copy
    have hc_ge := rootedCopies_nonempty_implies_le_card DH' hpos_copy
    rw [card_side₁_eq_A₁_card] at hc_ge
    have hc_eq : DH'.A₁.card = DG.A₁.card := le_antisymm hleA hc_ge
    have hc_swap_eq : DG.swap.A₁.card = DH'.swap.A₁.card := by
      have s1 := card_A₁_add_swap DG
      have s2 := card_A₁_add_swap DH'
      omega
    have hiso₁ : RootedIso DG.T₁ DG.root₁ DH'.T₁ DH'.root₁ := by
      have heq_f : Fintype.card DG.side₁ = DH'.A₁.card := by
        rw [card_side₁_eq_A₁_card, hc_eq]
      exact ((rootedCopies_eq_one_of_eq_card DH' heq_f).1.mp hpos_copy).symm
    have hlt₂ : Fintype.card (DG.swap.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
      rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
      have h1 : r + 2 ≤ DG.A₁.card := by rw [A₁_card_eq_ncard]; exact DG.hbig₁
      have hsum := card_A₁_add_swap DG
      omega
    have hG₂_big : r + 2 ≤ Fintype.card DG.swap.side₁ := by
      rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DG.hbig₂
    have hH₂_big : r + 2 ≤ Fintype.card DH'.swap.side₁ := by
      rw [card_side₁_eq_A₁_card, A₁_card_eq_ncard]; exact DH'.hbig₂
    have hlt_H2 : Fintype.card (DH'.swap.side₁ ⊕ Fin (r + 1)) < Fintype.card V := by
      rw [Fintype.card_sum, Fintype.card_fin, card_side₁_eq_A₁_card]
      have h1 : r + 2 ≤ DH'.A₁.card := by rw [A₁_card_eq_ncard]; exact DH'.hbig₁
      have hsum := card_A₁_add_swap DH'
      omega
    by_cases hsymG : RootedIso DG.T₁ DG.root₁ DG.swap.T₁ DG.swap.root₁
    · by_cases hsymH : RootedIso DH'.T₁ DH'.root₁ DH'.swap.T₁ DH'.swap.root₁
      · exact glue_bicenter_iso DG DH' hiso₁ (hsymG.symm.trans (hiso₁.trans hsymH))
      · exfalso
        have hQ₂ := hkelly (DH'.swap.side₁ ⊕ Fin (r + 1))
          (attachPath DH'.swap.T₁ DH'.swap.root₁ r) hlt_H2
        rw [ncard_attachPath_eq DG DH'.swap.ht_side₁ (exists_far_vertex DH'.swap) hH₂_big,
          ncard_attachPath_eq DH' DH'.swap.ht_side₁ (exists_far_vertex DH'.swap) hH₂_big] at hQ₂
        have hpos_rhs : 0 < (rootedCopies DH'.swap DH'.swap.T₁ DH'.swap.root₁).card *
            (rootedCopies DH' (pathGraph (r + 1)) 0).card :=
          Nat.mul_pos (Finset.card_pos.mpr ⟨DH'.swap.A₁, mem_rootedCopies_self DH'.swap⟩)
            (rootedCopies_rays_pos DH')
        have hcard_H2_eq : Fintype.card DH'.swap.side₁ = DG.A₁.card := by
          have h1 := hsymG.card_eq
          rw [card_side₁_eq_A₁_card, card_side₁_eq_A₁_card] at h1
          rw [card_side₁_eq_A₁_card]
          exact hc_swap_eq.symm.trans h1.symm
        have h0_a : (rootedCopies DG DH'.swap.T₁ DH'.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DG hcard_H2_eq).1.mp hp
          exact hsymH (hiso₁.symm.trans hri)
        have hcard_H2_eq2 : Fintype.card DH'.swap.side₁ = DG.swap.A₁.card := by
          rw [card_side₁_eq_A₁_card]; exact hc_swap_eq.symm
        have h0_b : (rootedCopies DG.swap DH'.swap.T₁ DH'.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DG.swap hcard_H2_eq2).1.mp hp
          exact hsymH (hiso₁.symm.trans (hsymG.trans hri))
        rw [h0_a, h0_b] at hQ₂
        omega
    · have hnsymH : ¬ RootedIso DH'.T₁ DH'.root₁ DH'.swap.T₁ DH'.swap.root₁ := by
        intro hsymH
        have hQ₂ := hkelly (DG.swap.side₁ ⊕ Fin (r + 1))
          (attachPath DG.swap.T₁ DG.swap.root₁ r) hlt₂
        rw [ncard_attachPath_eq DG DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big,
          ncard_attachPath_eq DH' DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big] at hQ₂
        have hpos_lhs : 0 < (rootedCopies DG.swap DG.swap.T₁ DG.swap.root₁).card *
            (rootedCopies DG (pathGraph (r + 1)) 0).card :=
          Nat.mul_pos (Finset.card_pos.mpr ⟨DG.swap.A₁, mem_rootedCopies_self DG.swap⟩)
            (rootedCopies_rays_pos DG)
        have hcard_G2_eq1 : Fintype.card DG.swap.side₁ = DH'.A₁.card := by
          have h1 := hsymH.card_eq
          rw [card_side₁_eq_A₁_card, card_side₁_eq_A₁_card] at h1
          rw [card_side₁_eq_A₁_card]
          exact hc_swap_eq.trans h1.symm
        have h0_a : (rootedCopies DH' DG.swap.T₁ DG.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DH' hcard_G2_eq1).1.mp hp
          exact hsymG (hiso₁.trans hri)
        have hcard_G2_eq2 : Fintype.card DG.swap.side₁ = DH'.swap.A₁.card := by
          rw [card_side₁_eq_A₁_card]; exact hc_swap_eq
        have h0_b : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card = 0 := by
          by_contra hne
          have hp := Nat.pos_of_ne_zero hne
          have hri := (rootedCopies_eq_one_of_eq_card DH'.swap hcard_G2_eq2).1.mp hp
          exact hsymG (hiso₁.trans (hsymH.trans hri))
        rw [h0_a, h0_b] at hQ₂
        omega
      have hQ₁' := hkelly (DG.side₁ ⊕ Fin (r + 1)) (attachPath DG.T₁ DG.root₁ r) hlt₁
      rw [ncard_attachPath_eq DG DG.ht_side₁ (exists_far_vertex DG) hG_big,
        ncard_attachPath_eq DH' DG.ht_side₁ (exists_far_vertex DG) hG_big] at hQ₁'
      have hc_G1 : (rootedCopies DG DG.T₁ DG.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DG (card_side₁_eq_A₁_card DG)).2 (RootedIso.refl _ _)
      have hc_H1 : (rootedCopies DH' DG.T₁ DG.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DH' (by rw [card_side₁_eq_A₁_card, hc_eq])).2 hiso₁.symm
      have h0_G2 : (rootedCopies DG.swap DG.T₁ DG.root₁).card = 0 := by
        by_contra hne
        have hp := Nat.pos_of_ne_zero hne
        have hle := rootedCopies_nonempty_implies_le_card DG.swap hp
        rw [card_side₁_eq_A₁_card] at hle
        have hsame : DG.swap.A₁.card = DG.A₁.card := le_antisymm hmax1 hle
        have hri := (rootedCopies_eq_one_of_eq_card DG.swap
          (by rw [card_side₁_eq_A₁_card, hsame])).1.mp hp
        exact hsymG hri.symm
      have h0_H2 : (rootedCopies DH'.swap DG.T₁ DG.root₁).card = 0 := by
        by_contra hne
        have hp := Nat.pos_of_ne_zero hne
        have hle := rootedCopies_nonempty_implies_le_card DH'.swap hp
        rw [card_side₁_eq_A₁_card] at hle
        have hsame : DH'.swap.A₁.card = DH'.A₁.card := le_antisymm (hc_eq.symm ▸ hleB) (hc_eq ▸ hle)
        have hri := (rootedCopies_eq_one_of_eq_card DH'.swap
          (by rw [card_side₁_eq_A₁_card, hsame, hc_eq])).1.mp hp
        exact hnsymH (hiso₁.symm.trans hri.symm)
      rw [hc_G1, hc_H1, h0_G2, h0_H2] at hQ₁'
      have hrays₂ : (rootedCopies DG.swap (pathGraph (r + 1)) 0).card =
          (rootedCopies DH'.swap (pathGraph (r + 1)) 0).card := by omega
      have hQ₂ := hkelly (DG.swap.side₁ ⊕ Fin (r + 1))
        (attachPath DG.swap.T₁ DG.swap.root₁ r) hlt₂
      rw [ncard_attachPath_eq DG DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big,
        ncard_attachPath_eq DH' DG.swap.ht_side₁ (exists_far_vertex DG.swap) hG₂_big] at hQ₂
      have heq_cross : (rootedCopies DG DG.swap.T₁ DG.swap.root₁).card =
          (rootedCopies DH' DG.swap.T₁ DG.swap.root₁).card :=
        rootedCopies_card_eq_of_rootedIso DG DH' hiso₁ DG.swap.T₁ DG.swap.root₁
      have heq_rays₁ : (rootedCopies DG (pathGraph (r + 1)) 0).card =
          (rootedCopies DH' (pathGraph (r + 1)) 0).card :=
        rootedCopies_card_eq_of_rootedIso DG DH' hiso₁ (pathGraph (r + 1)) 0
      have hc_G2 : (rootedCopies DG.swap DG.swap.T₁ DG.swap.root₁).card = 1 :=
        (rootedCopies_eq_one_of_eq_card DG.swap (card_side₁_eq_A₁_card DG.swap)).2 (RootedIso.refl _ _)
      rw [heq_cross, hrays₂, ← heq_rays₁, hc_G2, one_mul] at hQ₂
      have hc_H2 : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card = 1 := by
        have hpos_r1 := rootedCopies_rays_pos DG
        have hmul_eq : (rootedCopies DH'.swap DG.swap.T₁ DG.swap.root₁).card *
            (rootedCopies DG (pathGraph (r + 1)) 0).card =
            1 * (rootedCopies DG (pathGraph (r + 1)) 0).card := by omega
        exact Nat.eq_of_mul_eq_mul_right hpos_r1 hmul_eq
      have hiso₂ : RootedIso DG.swap.T₁ DG.swap.root₁ DH'.swap.T₁ DH'.swap.root₁ :=
        ((rootedCopies_eq_one_of_eq_card DH'.swap (by rw [card_side₁_eq_A₁_card, hc_swap_eq])).1.mp
          (hc_H2 ▸ Nat.zero_lt_one)).symm
      exact glue_bicenter_iso DG DH' hiso₁ hiso₂
  rcases Nat.eq_zero_or_pos (rootedCopies DH DG.T₁ DG.root₁).card with h0 | hpos
  · have hpos_swap : 0 < (rootedCopies DH.swap DG.T₁ DG.root₁).card := by
      rw [h0, zero_mul, zero_add] at hQ₁
      by_contra h0s
      have h0s' : (rootedCopies DH.swap DG.T₁ DG.root₁).card = 0 := by omega
      rw [h0s', zero_mul] at hQ₁
      omega
    exact choose_side DH.swap hmax3 hmax2 hpos_swap
  · exact choose_side DH hmax2 hmax3 hpos

end Tree3485H3

theorem OMA.solution :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H4_R1.H3 := by
  intro V W _ _ G H hTG hTH hcard r hr hGd hHd hkelly
    c₁ c₂ hc_adj hc_ne hc_le1 hc_le2 hc_t1 hc_t2 hc_dist hc_big1 hc_big2
    d₁ d₂ hd_adj hd_ne hd_le1 hd_le2 hd_t1 hd_t2 hd_dist hd_big1 hd_big2
  let DG : BicenterData G r :=
    ⟨c₁, c₂, hr, hTG, hGd, hc_adj, hc_ne, hc_le1, hc_le2, hc_t1, hc_t2, hc_dist, hc_big1, hc_big2⟩
  let DH : BicenterData H r :=
    ⟨d₁, d₂, hr, hTH, hHd, hd_adj, hd_ne, hd_le1, hd_le2, hd_t1, hd_t2, hd_dist, hd_big1, hd_big2⟩
  let DG' : BicenterData G r := if DG.swap.A₁.card ≤ DG.A₁.card then DG else DG.swap
  let DH' : BicenterData H r := if DH.swap.A₁.card ≤ DH.A₁.card then DH else DH.swap
  have hDG' : DG'.swap.A₁.card ≤ DG'.A₁.card := by
    dsimp only [DG']
    split_ifs with h
    · exact h
    · exact Nat.le_of_not_ge h
  have hDH' : DH'.swap.A₁.card ≤ DH'.A₁.card := by
    dsimp only [DH']
    split_ifs with h
    · exact h
    · exact Nat.le_of_not_ge h
  by_cases hGH : DH'.A₁.card ≤ DG'.A₁.card
  · exact h3_max_side hcard hkelly DG' DH' hDG' hGH (hDH'.trans hGH)
  · have hHG : DG'.A₁.card ≤ DH'.A₁.card := Nat.le_of_not_ge hGH
    have hkelly_symm : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        Fintype.card U < Fintype.card W →
        {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
          {T : Finset V | Nonempty (G.induce (T : Set V) ≃g Q)}.ncard :=
      fun U _ Q hU => (hkelly U Q (hcard ▸ hU)).symm
    obtain ⟨φ⟩ := h3_max_side hcard.symm hkelly_symm DH' DG' hDH' hHG (hDG'.trans hHG)
    exact ⟨φ.symm⟩
