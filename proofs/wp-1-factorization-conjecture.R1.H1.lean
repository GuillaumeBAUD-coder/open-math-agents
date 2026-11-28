import OMAReductions.R_wp_1_factorization_conjecture_R1
-- Step wp-1-factorization-conjecture.R1.H1: hypothesis H1 of reduction wp-1-factorization-conjecture.R1 (Chetwynd–Hilton, Discrete Math. 75 (1989), dense range 12n/7 ≤ k)
-- Credit: @PandaWill
-- ===== LemmasPM.lean =====

/-
Dense perfect matching lemma (Dirac-type, via Mathlib's Tutte theorem):
a finite graph of even order `N` with minimum degree `≥ N/2` has a perfect matching.
-/

namespace OMA.H1

open SimpleGraph

/-- the odd components of a finite graph have total size at most the number of vertices -/
lemma sum_components_le {W : Type*} [Fintype W] (H : SimpleGraph W) [Fintype H.ConnectedComponent]
    (S : Finset H.ConnectedComponent) :
    ∑ c ∈ S, c.supp.ncard ≤ Fintype.card W := by
  classical
  have h1 : ∑ c ∈ S, c.supp.ncard ≤
      ∑ c : H.ConnectedComponent, c.supp.ncard :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 : ∑ c : H.ConnectedComponent, c.supp.ncard = Fintype.card W := by
    rw [← (set_fintype_card_eq_univ_iff _).mpr H.iUnion_connectedComponentSupp,
      ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
    rw [Finset.card_biUnion
      (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
    simp_rw [← Set.ncard_eq_toFinset_card']
  omega

theorem exists_isPerfectMatching_of_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hδ : ∀ v, Fintype.card V ≤ 2 * G.degree v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  rw [tutte]
  intro u hu
  unfold IsTutteViolator at hu
  set N := Fintype.card V
  set H := ((⊤ : G.Subgraph).deleteVerts u).coe
  set s := u.ncard
  set z := H.oddComponents.ncard
  -- vertex type of H
  have hverts : ((⊤ : G.Subgraph).deleteVerts u).verts = Set.univ \ u := by
    simp [Subgraph.verts_top]
  have hcardW : Fintype.card ((⊤ : G.Subgraph).deleteVerts u).verts = N - s := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hverts, Set.ncard_sdiff (Set.subset_univ _),
      Set.ncard_univ, Nat.card_eq_fintype_card]
  have hsN : s ≤ N := by
    have := Set.ncard_le_ncard (Set.subset_univ u)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  obtain ⟨D, hD⟩ := id hev
  have hδ' : ∀ v, D ≤ G.degree v := fun v => by have := hδ v; omega
  -- each component has size ≥ δ + 1 - s
  have hcomp : ∀ c : H.ConnectedComponent, D + 1 ≤ c.supp.ncard + s := by
    intro c
    obtain ⟨x, hx⟩ := c.nonempty_supp
    have hxu : x.val ∉ u := by
      have := x.prop; simp only [Subgraph.deleteVerts_verts] at this; exact this.2
    -- the closed neighbourhood of x outside u lies in c
    let S : Finset V := (insert x.val (G.neighborFinset x.val)) \ u.toFinset
    have hS : D + 1 ≤ S.card + s := by
      have h1 := Finset.card_le_card_sdiff_add_card (s := insert x.val (G.neighborFinset x.val)) (t := u.toFinset)
      have h2 : (insert x.val (G.neighborFinset x.val)).card = G.degree x.val + 1 := by
        rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
      have h3 : u.toFinset.card = s := by simp only [s, Set.ncard_eq_toFinset_card']
      have h4 := hδ' x.val
      simp only [S]; omega
    have hinj : S.card ≤ c.supp.ncard := by
      let f : ∀ y ∈ S, ((⊤ : G.Subgraph).deleteVerts u).verts := fun y hy =>
        ⟨y, by
          rw [hverts]
          have hy' := (Finset.mem_sdiff.1 hy).2
          rw [Set.mem_toFinset] at hy'
          exact ⟨trivial, hy'⟩⟩
      rw [← Set.ncard_coe_finset S]
      refine Set.ncard_le_ncard_of_injOn (fun y => if hy : y ∈ S then (f y hy) else x) ?_ ?_
      · intro y hy
        have hy' : y ∈ S := hy
        simp only [dif_pos hy']
        simp only [S, Finset.mem_sdiff, Finset.mem_insert, mem_neighborFinset] at hy'
        rcases hy'.1 with rfl | hadj
        · exact hx
        · rw [ConnectedComponent.mem_supp_iff] at hx ⊢
          rw [← hx]
          apply ConnectedComponent.connectedComponentMk_eq_of_adj
          simp only [H, Subgraph.coe_adj, Subgraph.deleteVerts_adj, Subgraph.top_adj, f]
          refine ⟨trivial, ?_, trivial, hxu, hadj.symm⟩
          have hy2 := (Finset.mem_sdiff.1 hy).2
          rwa [Set.mem_toFinset] at hy2
      · intro a ha b hb hab
        have ha' : a ∈ S := ha
        have hb' : b ∈ S := hb
        simp only [dif_pos ha', dif_pos hb', f, Subtype.mk.injEq] at hab
        exact hab
    omega
  have hsum := sum_components_le H H.oddComponents.toFinset
  rw [hcardW] at hsum
  have hz' : z = H.oddComponents.toFinset.card := by
    simp [z, Set.ncard_eq_toFinset_card']
  -- lower bound for the sum
  have hlow : ∀ m, (∀ c ∈ H.oddComponents.toFinset, m ≤ c.supp.ncard) →
      z * m ≤ N - s := by
    intro m hm
    have := Finset.card_nsmul_le_sum _ _ m hm
    rw [smul_eq_mul, ← hz'] at this
    omega
  have hone : z * 1 ≤ N - s := hlow 1 (fun c hc => by
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hc; exact hc.pos)
  have hbig : z * (D + 1 - s) ≤ N - s := hlow _ (fun c _ => by have := hcomp c; omega)
  -- parity when s = 0
  by_cases hs0 : s = 0
  · have hpar : Even z := by
      rw [← Nat.not_odd_iff_even, odd_ncard_oddComponents, Nat.card_eq_fintype_card, hcardW,
        hs0, Nat.sub_zero, Nat.not_odd_iff_even]
      exact hev
    have hz2 : 2 ≤ z := by
      obtain ⟨r, hr⟩ := hpar; omega
    have : 2 * (D + 1) ≤ z * (D + 1 - s) := by
      rw [hs0, Nat.sub_zero]; exact Nat.mul_le_mul_right _ hz2
    omega
  · by_cases hsd : D < s
    · omega
    · have hz1 : s + 1 ≤ z := hu
      have : (s + 1) * (D + 1 - s) ≤ z * (D + 1 - s) := Nat.mul_le_mul_right _ hz1
      obtain ⟨t, ht⟩ : ∃ t, D = s + t := ⟨D - s, by omega⟩
      have e : D + 1 - s = t + 1 := by omega
      rw [e] at this hbig
      have : (s + 1) * (t + 1) ≤ N - s := le_trans this hbig
      have e2 : N - s = s + 2 * t := by omega
      have hst : t ≤ s * t := Nat.le_mul_of_pos_left t (by omega)
      nlinarith
end OMA.H1
-- ===== LemmasBasic.lean =====

/-
Basic reusable lemmas for H1:
* `coloring_succ_of_perfectMatching` : colour a perfect matching with a new colour.
* `isRegularOfDegree_sdiff` : removing a perfect matching from a k-regular graph leaves a (k-1)-regular one.
* `coloring_of_sub_regular` : greedy step (dense perfect matching + induction).
-/

namespace OMA.H1

open SimpleGraph OMA.R_wp_1_factorization_conjecture_R1

theorem coloring_succ_of_perfectMatching {V : Type*} (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsPerfectMatching) {k : ℕ}
    (C : (G \ M.spanningCoe).lineGraph.Coloring (Fin k)) :
    Nonempty (G.lineGraph.Coloring (Fin (k + 1))) := by
  classical
  let c : V → V → Fin (k + 1) := fun v w =>
    if M.Adj v w then Fin.last k else
      if h : (G \ M.spanningCoe).Adj v w then (C ⟨s(v, w), h⟩).castSucc else 0
  refine coloring_of_pair G c ?_ ?_
  · intro x y
    simp only [c]
    by_cases hm : M.Adj x y
    · simp [hm, hm.symm]
    · have hm' : ¬ M.Adj y x := fun h => hm h.symm
      simp only [hm, hm', if_false]
      by_cases h : (G \ M.spanningCoe).Adj x y
      · rw [dif_pos h, dif_pos h.symm]; simp [Sym2.eq_swap]
      · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]
  · intro v y z hy hz e
    have hpm := Subgraph.isPerfectMatching_iff.1 hM v
    by_cases my : M.Adj v y <;> by_cases mz : M.Adj v z
    · obtain ⟨w, -, hw⟩ := hpm
      exact (hw y my).trans (hw z mz).symm
    · have hz' : (G \ M.spanningCoe).Adj v z := by
        rw [sdiff_adj]; exact ⟨hz, by simpa using mz⟩
      simp only [c, my, mz, if_true, if_false, dif_pos hz'] at e
      exact absurd e.symm (Fin.castSucc_lt_last _).ne
    · have hy' : (G \ M.spanningCoe).Adj v y := by
        rw [sdiff_adj]; exact ⟨hy, by simpa using my⟩
      simp only [c, my, mz, if_true, if_false, dif_pos hy'] at e
      exact absurd e (Fin.castSucc_lt_last _).ne
    · have hy' : (G \ M.spanningCoe).Adj v y := by
        rw [sdiff_adj]; exact ⟨hy, by simpa using my⟩
      have hz' : (G \ M.spanningCoe).Adj v z := by
        rw [sdiff_adj]; exact ⟨hz, by simpa using mz⟩
      simp only [c, my, mz, if_false, dif_pos hy', dif_pos hz', Fin.castSucc_inj] at e
      by_contra hne
      have hadj : (G \ M.spanningCoe).lineGraph.Adj ⟨s(v, y), hy'⟩ ⟨s(v, z), hz'⟩ := by
        rw [lineGraph_adj_iff_exists]
        refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
        intro heq
        have := congrArg Subtype.val heq
        simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
        rcases this with ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact hne h2
        · exact hne (h2.trans h1)
      exact C.valid hadj e

theorem isRegularOfDegree_sdiff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) [DecidableRel (G \ M.spanningCoe).Adj]
    (hM : M.IsPerfectMatching) {k : ℕ}
    (hG : G.IsRegularOfDegree k) :
    (G \ M.spanningCoe).IsRegularOfDegree (k - 1) := by
  intro v
  obtain ⟨w, hw, hu⟩ := Subgraph.isPerfectMatching_iff.1 hM v
  have : (G \ M.spanningCoe).neighborFinset v = (G.neighborFinset v).erase w := by
    ext x
    simp only [mem_neighborFinset, sdiff_adj, Subgraph.spanningCoe_adj, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 (h ▸ hw), h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 (hu x h)⟩
  rw [← card_neighborFinset_eq_degree, this, Finset.card_erase_of_mem
    ((mem_neighborFinset _ _ _).2 (M.adj_sub hw)), card_neighborFinset_eq_degree, hG v]

end OMA.H1
-- ===== LemmasGreedy.lean =====
-- depends on LemmasPM.lean, LemmasBasic.lean (assembled by build_all.sh)
namespace OMA.H1

open SimpleGraph OMA.R_wp_1_factorization_conjecture_R1

/-- Greedy step: a k-regular graph of even order `N ≤ 2k` is class 1 as soon as every
(k-1)-regular spanning subgraph of it is class 1. -/
theorem coloring_of_sub_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hG : G.IsRegularOfDegree k) (hev : Even (Fintype.card V))
    (hk : Fintype.card V ≤ 2 * k) (hk1 : 1 ≤ k)
    (h : ∀ (H : SimpleGraph V) [DecidableRel H.Adj], H ≤ G → H.IsRegularOfDegree (k - 1) →
      Nonempty (H.lineGraph.Coloring (Fin (k - 1)))) :
    Nonempty (G.lineGraph.Coloring (Fin k)) := by
  classical
  obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_minDegree G hev (fun v => by rw [hG v]; exact hk)
  obtain ⟨C⟩ := h (G \ M.spanningCoe) sdiff_le (isRegularOfDegree_sdiff G M hM hG)
  have := coloring_succ_of_perfectMatching G M hM C
  rwa [Nat.sub_add_cancel hk1] at this

/-- Iterated greedy step: to show a k-regular graph of even order `N` is class 1 it suffices to show
all its `r`-regular spanning subgraphs are class 1, for any `r ≤ k` with `N ≤ 2 (r + 1)`. -/
theorem coloring_of_sub_regular_iter {V : Type*} [Fintype V] [DecidableEq V]
    (hev : Even (Fintype.card V)) (r : ℕ) :
    ∀ j : ℕ, Fintype.card V ≤ 2 * (r + 1) → ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree (r + j) →
      (∀ (H : SimpleGraph V) [DecidableRel H.Adj], H ≤ G → H.IsRegularOfDegree r →
        Nonempty (H.lineGraph.Coloring (Fin r))) →
      Nonempty (G.lineGraph.Coloring (Fin (r + j))) := by
  intro j
  induction j with
  | zero => intro _ G _ hG h; exact h G le_rfl hG
  | succ j ih =>
    intro hN G _ hG h
    refine coloring_of_sub_regular G hG hev (by omega) (by omega) ?_
    intro H _ hHG hH
    have e : r + (j + 1) - 1 = r + j := by omega
    rw [e] at hH ⊢
    exact ih hN H hH (fun H' _ hH' hr => h H' (hH'.trans hHG) hr)

end OMA.H1
-- ===== LemmasDelete.lean =====
-- depends on the reduction module (coloring_of_pair); assembled by build_all.sh
namespace OMA.H1

open SimpleGraph OMA.R_wp_1_factorization_conjecture_R1

/-- A proper edge-colouring (line graph colouring) as a symmetric proper function on pairs. -/
lemma pair_of_coloring {W α : Type*} [Inhabited α] (H : SimpleGraph W) (C : H.lineGraph.Coloring α) :
    ∃ c : W → W → α, (∀ x y, c x y = c y x) ∧
      (∀ v y z, H.Adj v y → H.Adj v z → c v y = c v z → y = z) ∧
      (∀ x y (h : H.Adj x y), c x y = C ⟨s(x, y), h⟩) := by
  classical
  refine ⟨fun x y => if h : H.Adj x y then C ⟨s(x, y), h⟩ else default, ?_, ?_, ?_⟩
  · intro x y
    by_cases h : H.Adj x y
    · simp only [dif_pos h, dif_pos h.symm, Sym2.eq_swap]
    · simp only [dif_neg h, dif_neg (fun h' : H.Adj y x => h h'.symm)]
  · intro v y z hy hz e
    simp only [dif_pos hy, dif_pos hz] at e
    by_contra hne
    have hadj : H.lineGraph.Adj ⟨s(v, y), hy⟩ ⟨s(v, z), hz⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      intro heq
      have := congrArg Subtype.val heq
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
      rcases this with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hne (h2.trans h1)
    exact C.valid hadj e
  · intro x y h; simp only [dif_pos h]

/-- Vertex deletion: a k-regular graph of even order is class 1 if `G - w` is k-edge-colourable.
(Each colour misses exactly one vertex of `G - w`, these are exactly the neighbours of `w`.) -/
theorem coloring_of_deleteVertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} [NeZero k] (hG : G.IsRegularOfDegree k)
    (hev : Even (Fintype.card V)) (w : V)
    (C : (G.induce {v | v ≠ w}).lineGraph.Coloring (Fin k)) :
    Nonempty (G.lineGraph.Coloring (Fin k)) := by
  classical
  obtain ⟨c1, hs1, hp1, -⟩ := pair_of_coloring _ C
  -- extend to V
  let c0 : V → V → Fin k := fun v x =>
    if hv : v ≠ w then (if hx : x ≠ w then c1 ⟨v, hv⟩ ⟨x, hx⟩ else 0) else 0
  have hs0 : ∀ x y, c0 x y = c0 y x := by
    intro x y; simp only [c0]
    by_cases hx : x ≠ w <;> by_cases hy : y ≠ w <;> simp [hx, hy, hs1]
  have hp0 : ∀ v y z, v ≠ w → y ≠ w → z ≠ w → G.Adj v y → G.Adj v z → c0 v y = c0 v z → y = z := by
    intro v y z hv hy hz hvy hvz e
    simp only [c0, dif_pos hv, dif_pos hy, dif_pos hz] at e
    have := hp1 ⟨v, hv⟩ ⟨y, hy⟩ ⟨z, hz⟩ (by simpa using hvy) (by simpa using hvz) e
    simpa using congrArg Subtype.val this
  -- colours used at v (in G - w)
  let used : V → Finset (Fin k) := fun v => ((G.neighborFinset v).erase w).image (c0 v)
  have hused_card : ∀ v, v ≠ w → (used v).card = k - (if G.Adj v w then 1 else 0) := by
    intro v hv
    rw [Finset.card_image_of_injOn]
    · by_cases h : G.Adj v w
      · rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 h), card_neighborFinset_eq_degree,
          hG v, if_pos h]
      · rw [Finset.erase_eq_of_notMem (by simpa using h), card_neighborFinset_eq_degree, hG v, if_neg h, Nat.sub_zero]
    · intro y hy z hz e
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, mem_neighborFinset,
        Set.mem_singleton_iff] at hy hz
      exact hp0 v y z hv hy.2 hz.2 hy.1 hz.1 e
  let missing : Fin k → Finset V := fun i => Finset.univ.filter (fun v => v ≠ w ∧ i ∉ used v)
  -- each colour misses at least one vertex (parity)
  have hmiss_pos : ∀ i, 1 ≤ (missing i).card := by
    intro i
    let M : G.Subgraph :=
      { verts := {v | v ≠ w ∧ i ∈ used v}
        Adj := fun a b => a ≠ w ∧ b ≠ w ∧ G.Adj a b ∧ c0 a b = i
        adj_sub := fun h => h.2.2.1
        edge_vert := fun {a b} h => ⟨h.1, Finset.mem_image.2 ⟨b, by simp [h.2.1, h.2.2.1], h.2.2.2⟩⟩
        symm := ⟨fun a b h => ⟨h.2.1, h.1, h.2.2.1.symm, (hs0 _ _).trans h.2.2.2⟩⟩ }
    have hM : M.IsMatching := by
      rintro v ⟨hv, hi⟩
      obtain ⟨b, hb, e⟩ := Finset.mem_image.1 hi
      simp only [Finset.mem_erase, mem_neighborFinset] at hb
      refine ⟨b, ⟨hv, hb.1, hb.2, e⟩, ?_⟩
      rintro y ⟨-, hy, hvy, ey⟩
      exact hp0 v y b hv hy hb.1 hvy hb.2 (ey.trans e.symm)
    have hev' := hM.even_card
    have hsplit : (M.verts.toFinset).card + (missing i).card = Fintype.card V - 1 := by
      have : M.verts.toFinset = Finset.univ.filter (fun v => v ≠ w ∧ i ∈ used v) := by
        ext v; simp [M]
      rw [this]
      have h2 : (Finset.univ.filter (fun v => v ≠ w ∧ i ∈ used v)) ∪ missing i =
          Finset.univ.erase w := by
        ext v; by_cases hv : v = w <;> by_cases hi : i ∈ used v <;> simp [missing, hv, hi]
      rw [← Finset.card_union_of_disjoint, h2, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [missing, Finset.mem_filter] at h1 h2
      exact h2.2.2 h1.2.2
    have hN : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨w⟩
    obtain ⟨r, hr⟩ := hev'
    obtain ⟨t, ht⟩ := hev
    omega
  -- total number of misses is k
  have htotal : ∑ i, (missing i).card = k := by
    have h1 : ∑ i, (missing i).card =
        ∑ v ∈ Finset.univ.erase w, (Finset.univ.filter (fun i => i ∉ used v)).card := by
      simp only [missing, Finset.card_filter]
      rw [Finset.sum_comm]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ w)]
      simp only [ne_eq, not_true_eq_false, false_and, if_false, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hv' : v ≠ w := Finset.ne_of_mem_erase hv
      simp [hv']
    have h2 : ∀ v ∈ Finset.univ.erase w, (Finset.univ.filter (fun i => i ∉ used v)).card =
        if G.Adj v w then 1 else 0 := by
      intro v hv
      have hv' : v ≠ w := Finset.ne_of_mem_erase hv
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
        (fun i => i ∈ used v)
      have h3 : (Finset.univ.filter (fun i => i ∈ used v)) = used v := by ext; simp
      rw [h3, hused_card v hv', Finset.card_univ, Fintype.card_fin] at this
      have hle : (if G.Adj v w then 1 else 0) ≤ k := by
        have := NeZero.pos k; split_ifs <;> omega
      omega
    rw [h1, Finset.sum_congr rfl h2, ← Finset.card_filter]
    have : (Finset.univ.erase w).filter (fun v => G.Adj v w) = G.neighborFinset w := by
      ext v; simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset]
      constructor
      · rintro ⟨-, h⟩; exact h.symm
      · intro h; exact ⟨⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩, h.symm⟩
    rw [this, card_neighborFinset_eq_degree, hG w]
  have hmiss1 : ∀ i, (missing i).card = 1 := by
    intro i
    by_contra hne
    have h2 : 2 ≤ (missing i).card := by have := hmiss_pos i; omega
    have : ∑ _j : Fin k, (1 : ℕ) + 1 ≤ ∑ j, (missing j).card := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add (f := fun j => (missing j).card) _ (Finset.mem_univ i)]
      have := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hmiss_pos j)
      omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
    omega
  -- the missing colour at a neighbour of w
  have hφ : ∀ v, G.Adj w v → ∃ i, i ∉ used v := by
    intro v h
    have hv : v ≠ w := (G.ne_of_adj h).symm
    by_contra hall
    push Not at hall
    have : Finset.univ ⊆ used v := fun i _ => hall i
    have := Finset.card_le_card this
    rw [hused_card v hv, if_pos h.symm, Finset.card_univ, Fintype.card_fin] at this
    have := NeZero.pos k
    omega
  let φ : V → Fin k := fun v => if h : G.Adj w v then (hφ v h).choose else 0
  have hφu : ∀ v (h : G.Adj w v), φ v ∉ used v := fun v h => by
    simp only [φ, dif_pos h]; exact (hφ v h).choose_spec
  have hφm : ∀ v (h : G.Adj w v), v ∈ missing (φ v) := fun v h => by
    simp only [missing, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(G.ne_of_adj h).symm, hφu v h⟩
  let c : V → V → Fin k := fun v x => if v = w then φ x else if x = w then φ v else c0 v x
  refine coloring_of_pair G c ?_ ?_
  · intro x y
    simp only [c]
    by_cases hx : x = w <;> by_cases hy : y = w
    · subst hx; subst hy; rfl
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy, hs0]
  · intro v y z hy hz e
    by_cases hv : v = w
    · subst hv
      simp only [c, if_true] at e
      have h1 := hφm y hy
      have h2 := hφm z hz
      rw [e] at h1
      exact Finset.card_le_one.1 (hmiss1 (φ z)).le y h1 z h2
    · have hu : ∀ x, x ≠ w → G.Adj v x → c0 v x ∈ used v := fun x hx hvx =>
        Finset.mem_image.2 ⟨x, by simp [hx, hvx], rfl⟩
      by_cases hyw : y = w <;> by_cases hzw : z = w
      · rw [hyw, hzw]
      · subst hyw
        simp only [c, hv, if_true, if_false, hzw] at e
        exact absurd (e ▸ hu z hzw hz) (hφu v hy.symm)
      · subst hzw
        simp only [c, hv, if_true, if_false, hyw] at e
        exact absurd (e.symm ▸ hu y hyw hy) (hφu v hz.symm)
      · simp only [c, hv, hyw, hzw, if_false] at e
        exact hp0 v y z hv hyw hzw hy hz e

end OMA.H1
-- ===== LemmasExtend.lean =====
-- depends on LemmasPM.lean; assembled by build_all.sh
/-
The Chetwynd–Hilton greedy step (condition (a),(b) of "Lemma 1" in Cariolaro–Hilton's account):
given edge-disjoint matchings `M 0, …, M (t-1)` of a graph `X` of odd order and vertices `ξ i` not
covered by `M i`, if `X` has large minimum degree there are pairwise edge-disjoint near-1-factors
`F i ⊇ M i` of `X`, `F i` missing exactly `ξ i`.
-/
namespace OMA.H1

open SimpleGraph

/-- number of vertices covered by a graph (used for matchings) -/
noncomputable def coverCard {V : Type*} [Fintype V] (M : SimpleGraph V) : ℕ :=
  by classical exact (Finset.univ.filter (fun v => ∃ u, M.Adj v u)).card

lemma even_coverCard {V : Type*} [Fintype V] (M : SimpleGraph V)
    (hM : ∀ v u u', M.Adj v u → M.Adj v u' → u = u') : Even (coverCard M) := by
  classical
  let S : (⊤ : SimpleGraph V).Subgraph :=
    { verts := {v | ∃ u, M.Adj v u}
      Adj := M.Adj
      adj_sub := fun h => M.ne_of_adj h
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => h.symm⟩ }
  have hS : S.IsMatching := by
    rintro v ⟨u, hu⟩
    exact ⟨u, hu, fun u' hu' => hM v u' u hu' hu⟩
  have := hS.even_card
  unfold coverCard
  convert this using 2
  ext v; simp [S]

/-- edge-disjointness, spelled out -/
def EDisj {V : Type*} (A B : SimpleGraph V) : Prop := ∀ a b, A.Adj a b → ¬ B.Adj a b

theorem exists_near_factors {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
    [DecidableRel X.Adj] (t δ : ℕ) (hδ : ∀ v, δ ≤ X.degree v) (hodd : Odd (Fintype.card V))
    (M : ℕ → SimpleGraph V) (ξ : ℕ → V)
    (hMX : ∀ i, M i ≤ X) (hMm : ∀ i v u u', (M i).Adj v u → (M i).Adj v u' → u = u')
    (hξ : ∀ i u, ¬ (M i).Adj (ξ i) u) (hdisj : ∀ i j, i ≠ j → EDisj (M i) (M j))
    (hsize : ∀ i < t, Fintype.card V - 1 - coverCard (M i) + 2 * (t + coverCard (M i)) ≤ 2 * δ) :
    ∃ F : ℕ → SimpleGraph V, ∀ i < t, F i ≤ X ∧ M i ≤ F i ∧ (∀ u, ¬ (F i).Adj (ξ i) u) ∧
      (∀ v, v ≠ ξ i → ∃! u, (F i).Adj v u) ∧ (∀ j < t, i ≠ j → EDisj (F i) (F j)) := by
  classical
  -- invariant for the first s factors
  suffices H : ∀ s ≤ t, ∃ F : ℕ → SimpleGraph V, ∀ i < s, F i ≤ X ∧ M i ≤ F i ∧
      (∀ u, ¬ (F i).Adj (ξ i) u) ∧ (∀ v, v ≠ ξ i → ∃! u, (F i).Adj v u) ∧
      (∀ v u u', (F i).Adj v u → (F i).Adj v u' → u = u') ∧
      (∀ j < s, i ≠ j → EDisj (F i) (F j)) ∧ (∀ j < t, i ≠ j → EDisj (F i) (M j)) by
    obtain ⟨F, hF⟩ := H t le_rfl
    exact ⟨F, fun i hi => ⟨(hF i hi).1, (hF i hi).2.1, (hF i hi).2.2.1, (hF i hi).2.2.2.1,
      (hF i hi).2.2.2.2.2.1⟩⟩
  intro s
  induction s with
  | zero => intro _; exact ⟨fun _ => ⊥, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ s ih =>
    intro hst
    obtain ⟨F, hF⟩ := ih (by omega)
    have hs : s < t := by omega
    -- the available graph
    let R : SimpleGraph V :=
      { Adj := fun a b => X.Adj a b ∧ (∀ i < s, ¬ (F i).Adj a b) ∧
          (∀ j, s < j → j < t → ¬ (M j).Adj a b)
        symm := ⟨fun a b h => ⟨h.1.symm, fun i hi h' => h.2.1 i hi h'.symm,
          fun j h1 h2 h' => h.2.2 j h1 h2 h'.symm⟩⟩
        loopless := ⟨fun a h => X.loopless.irrefl a h.1⟩ }
    let W : Set V := {v | v ≠ ξ s ∧ ¬ ∃ u, (M s).Adj v u}
    let D : Finset V := Finset.univ.filter (fun u => u = ξ s ∨ ∃ x, (M s).Adj u x)
    have hDcard : D.card = coverCard (M s) + 1 := by
      have : D = insert (ξ s) (Finset.univ.filter (fun u => ∃ x, (M s).Adj u x)) := by
        ext u; simp [D]
      rw [this, Finset.card_insert_of_notMem (by simpa using hξ s), coverCard]
    have hWcard : Fintype.card W = Fintype.card V - 1 - coverCard (M s) := by
      have h1 : Fintype.card W = (Finset.univ.filter (fun v => v ∈ W)).card := by
        rw [Fintype.card_subtype]
      have h2 : Finset.univ.filter (fun v => v ∈ W) = Finset.univ \ D := by
        ext v; simp [W, D, not_or]
      rw [h1, h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), hDcard, Finset.card_univ]
      omega
    have hev : Even (Fintype.card W) := by
      rw [hWcard]
      obtain ⟨r, hr⟩ := even_coverCard (M s) (hMm s)
      obtain ⟨q, hq⟩ := hodd
      have : coverCard (M s) + 1 ≤ Fintype.card V := by
        rw [← hDcard]; exact Finset.card_le_univ _
      exact ⟨q - r, by omega⟩
    -- minimum degree of R.induce W
    have hdeg : ∀ x : W, Fintype.card W ≤ 2 * (R.induce W).degree x := by
      intro ⟨v, hv⟩
      let B1 : Finset V := (Finset.range s).biUnion (fun i => Finset.univ.filter (fun u => (F i).Adj v u))
      let B2 : Finset V := (Finset.Ioo s t).biUnion (fun j => Finset.univ.filter (fun u => (M j).Adj v u))
      have hB1 : B1.card ≤ s := by
        refine (Finset.card_biUnion_le).trans ?_
        have : ∀ i ∈ Finset.range s, (Finset.univ.filter (fun u => (F i).Adj v u)).card ≤ 1 := by
          intro i hi
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact (hF i (Finset.mem_range.1 hi)).2.2.2.2.1 v a b ha hb
        refine (Finset.sum_le_sum this).trans ?_
        simp
      have hB2 : B2.card ≤ t - 1 - s := by
        refine (Finset.card_biUnion_le).trans ?_
        have : ∀ j ∈ Finset.Ioo s t, (Finset.univ.filter (fun u => (M j).Adj v u)).card ≤ 1 := by
          intro j _
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact hMm j v a b ha hb
        refine (Finset.sum_le_sum this).trans ?_
        simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ioo]
        omega
      let A : Finset V := X.neighborFinset v \ (B1 ∪ B2 ∪ D)
      have hA : δ ≤ A.card + s + (t - 1 - s) + (coverCard (M s) + 1) := by
        have h1 := Finset.card_le_card_sdiff_add_card (s := X.neighborFinset v) (t := B1 ∪ B2 ∪ D)
        have h2 := Finset.card_union_le (B1 ∪ B2) D
        have h3 := Finset.card_union_le B1 B2
        rw [card_neighborFinset_eq_degree] at h1
        have := hδ v
        have hAeq : A.card = (X.neighborFinset v \ (B1 ∪ B2 ∪ D)).card := rfl
        omega
      have hinj : A.card ≤ (R.induce W).degree ⟨v, hv⟩ := by
        rw [← card_neighborFinset_eq_degree]
        refine Finset.card_le_card_of_injOn (fun u => if hu : u ∈ W then ⟨u, hu⟩ else ⟨v, hv⟩) ?_ ?_
        · intro u hu
          simp only [A, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, mem_neighborFinset,
            Finset.coe_union, Set.mem_union, not_or] at hu
          obtain ⟨hxu, ⟨hu1, hu2⟩, hu3⟩ := hu
          have huW : u ∈ W := by
            simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hu3
            exact ⟨hu3.1, hu3.2⟩
          simp only [Finset.mem_coe, dif_pos huW, mem_neighborFinset, comap_adj,
            Function.Embedding.coe_subtype]
          refine ⟨hxu, fun i hi h => hu1 ?_, fun j h1 h2 h => hu2 ?_⟩
          · simp only [B1, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨i, hi, h⟩
          · simp only [B2, Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨j, ⟨h1, h2⟩, h⟩
        · intro a ha b hb hab
          have haW : a ∈ W := by
            simp only [A, D, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.coe_union,
              Set.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at ha
            exact ⟨ha.2.2.1, ha.2.2.2⟩
          have hbW : b ∈ W := by
            simp only [A, D, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.coe_union,
              Set.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hb
            exact ⟨hb.2.2.1, hb.2.2.2⟩
          simp only [dif_pos haW, dif_pos hbW, Subtype.mk.injEq] at hab
          exact hab
      have := hsize s hs
      rw [hWcard]
      omega
    obtain ⟨P, hP⟩ := exists_isPerfectMatching_of_minDegree (R.induce W) hev hdeg
    -- lift P to V
    let Pl : SimpleGraph V :=
      { Adj := fun a b => ∃ (ha : a ∈ W) (hb : b ∈ W), P.Adj ⟨a, ha⟩ ⟨b, hb⟩
        symm := ⟨fun a b ⟨ha, hb, h⟩ => ⟨hb, ha, h.symm⟩⟩
        loopless := ⟨fun a ⟨ha, _, h⟩ => P.loopless.irrefl _ h⟩ }
    have hPlR : ∀ a b, Pl.Adj a b → R.Adj a b := by
      rintro a b ⟨ha, hb, h⟩
      have := P.adj_sub h
      simpa using this
    have hPlW : ∀ a b, Pl.Adj a b → a ∈ W := fun a b ⟨ha, _, _⟩ => ha
    let Fs : SimpleGraph V := M s ⊔ Pl
    have hMWnot : ∀ a b, (M s).Adj a b → a ∉ W := fun a b h ha => ha.2 ⟨b, h⟩
    refine ⟨Function.update F s Fs, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    swap
    · subst i
      simp only [Function.update_self]
      refine ⟨sup_le (hMX s) (fun a b h => (hPlR a b h).1), le_sup_left, ?_, ?_, ?_, ?_, ?_⟩
      · intro u h
        rcases h with hm | hp
        · exact hξ s u hm
        · exact (hPlW _ _ hp).1 rfl
      · intro v hv
        by_cases hvM : ∃ u, (M s).Adj v u
        · obtain ⟨u, hu⟩ := hvM
          refine ⟨u, Or.inl hu, fun u' hu' => ?_⟩
          rcases hu' with hm | hp
          · exact hMm s v u' u hm hu
          · exact absurd (hPlW _ _ hp) (hMWnot v u hu)
        · have hvW : v ∈ W := ⟨hv, hvM⟩
          obtain ⟨⟨u, huW⟩, hu, huniq⟩ := Subgraph.isPerfectMatching_iff.1 hP ⟨v, hvW⟩
          refine ⟨u, Or.inr ⟨hvW, huW, hu⟩, fun u' hu' => ?_⟩
          rcases hu' with hm | ⟨_, hu'W, hp⟩
          · exact absurd ⟨u', hm⟩ hvM
          · have := huniq ⟨u', hu'W⟩ hp
            exact congrArg Subtype.val this
      · intro v u u' h h'
        rcases h with hm | ⟨hvW, huW, hp⟩ <;> rcases h' with hm' | ⟨hvW', hu'W, hp'⟩
        · exact hMm s v u u' hm hm'
        · exact absurd hvW' (hMWnot v u hm)
        · exact absurd hvW (hMWnot v u' hm')
        · have := hP.1.eq_of_adj_left hp hp'
          exact congrArg Subtype.val this
      · intro j hj hij
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [Function.update_of_ne (by omega)]
          intro a b hab hF'
          rcases hab with hm | hp
          · exact (hF j hj).2.2.2.2.2.2 s hs (Ne.symm hij) a b hF' hm
          · exact (hPlR a b hp).2.1 j hj hF'
        · exact absurd hj.symm hij
      · intro j hj hij a b hab hmj
        rcases hab with hm | hp
        · exact hdisj s j hij a b hm hmj
        · rcases lt_or_gt_of_ne hij with h | h
          · exact (hPlR a b hp).2.2 j h hj hmj
          · exact (hPlR a b hp).2.1 j h ((hF j h).2.1 hmj)
    · -- old factors
      have hne : i ≠ s := by omega
      simp only [Function.update_of_ne hne]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hF i hi
      refine ⟨h1, h2, h3, h4, h5, fun j hj hij => ?_, h7⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [Function.update_of_ne (by omega)]; exact h6 j hj hij
      · subst j
        rw [Function.update_self]
        intro a b hab hs'
        rcases hs' with hm | hp
        · exact h7 s hs hij a b hab hm
        · exact (hPlR a b hp).2.1 i hi hab

end OMA.H1
-- ===== LemmasCount.lean =====
-- standalone (Mathlib only); assembled by build_all.sh
/-
Chetwynd–Hilton counting lemma ("[5, Lemma 3]"): in a `D`-regular graph `H` on `N ≥ 2` vertices
some two distinct vertices have at least `D(D-1)/(N-1)` common neighbours.
Applied to the complement of `G` this is `p ≥ (2n-d-1)(2n-d-2)/(2n-1)`.
-/
namespace OMA.H1

open SimpleGraph

theorem exists_many_common_neighbors {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {D : ℕ} (hH : H.IsRegularOfDegree D) (hN : 2 ≤ Fintype.card V) :
    ∃ x y, x ≠ y ∧
      D * (D - 1) ≤ (Fintype.card V - 1) *
        (Finset.univ.filter (fun z => H.Adj x z ∧ H.Adj y z)).card := by
  classical
  set N := Fintype.card V
  let p : V × V → ℕ := fun xy => (Finset.univ.filter (fun z => H.Adj xy.1 z ∧ H.Adj xy.2 z)).card
  have hsum : ∑ xy ∈ (Finset.univ : Finset V).offDiag, p xy = N * (D * (D - 1)) := by
    have : ∀ z : V, ((Finset.univ : Finset V).offDiag.filter
        (fun xy => H.Adj xy.1 z ∧ H.Adj xy.2 z)).card = D * (D - 1) := by
      intro z
      have e : (Finset.univ : Finset V).offDiag.filter (fun xy => H.Adj xy.1 z ∧ H.Adj xy.2 z) =
          (H.neighborFinset z).offDiag := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
          mem_neighborFinset]
        constructor
        · rintro ⟨hxy, hx, hy⟩; exact ⟨hx.symm, hy.symm, hxy⟩
        · rintro ⟨hx, hy, hxy⟩; exact ⟨hxy, hx.symm, hy.symm⟩
      rw [e, Finset.offDiag_card, card_neighborFinset_eq_degree, hH z, Nat.mul_sub_one]
    simp only [p, Finset.card_filter]
    rw [Finset.sum_comm]
    simp only [← Finset.card_filter, this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  have hne : ((Finset.univ : Finset V).offDiag).Nonempty := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < N by omega)
    exact ⟨(a, b), by simp [hab]⟩
  have hle : ∑ xy ∈ (Finset.univ : Finset V).offDiag, D * (D - 1) ≤
      ∑ xy ∈ (Finset.univ : Finset V).offDiag, (N - 1) * p xy := by
    rw [Finset.sum_const, ← Finset.mul_sum, hsum, Finset.offDiag_card, Finset.card_univ,
      smul_eq_mul]
    have : N * N - N = N * (N - 1) := by rw [Nat.mul_sub_one]
    rw [this]; apply le_of_eq; ring
  obtain ⟨⟨x, y⟩, hxy, h⟩ := Finset.exists_le_of_sum_le hne hle
  simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hxy
  exact ⟨x, y, hxy, h⟩

end OMA.H1
-- ===== LemmasExtendCH.lean =====
-- depends on LemmasPM.lean, LemmasExtend.lean (coverCard, even_coverCard, EDisj); assembled by build_all.sh
/-
Chetwynd–Hilton greedy step in its original form (Cariolaro–Hilton, eq. (3)–(4)):
`F i` is a near-1-factor of `X - (F 0 ∪ … ∪ F (i-1))` missing `ξ i` and containing what is left of
`M i`; the later matchings are NOT reserved, only `⋃ F ⊇ ⋃ M` is guaranteed. The degree loss at step
`i` is therefore only `i`.
-/
namespace OMA.H1

open SimpleGraph

theorem exists_near_factors_CH {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V)
    [DecidableRel X.Adj] (t δ : ℕ) (hδ : ∀ v, δ ≤ X.degree v) (hodd : Odd (Fintype.card V))
    (M : ℕ → SimpleGraph V) (ξ : ℕ → V)
    (hMX : ∀ i, M i ≤ X) (hMm : ∀ i v u u', (M i).Adj v u → (M i).Adj v u' → u = u')
    (hξ : ∀ i u, ¬ (M i).Adj (ξ i) u)
    (hsize : ∀ i < t, Fintype.card V - 1 - coverCard (M i) + 2 * (i + 1 + coverCard (M i)) ≤ 2 * δ) :
    ∃ F : ℕ → SimpleGraph V, ∀ i < t, F i ≤ X ∧ (∀ a b, (M i).Adj a b → ∃ j ≤ i, (F j).Adj a b) ∧
      (∀ u, ¬ (F i).Adj (ξ i) u) ∧ (∀ v, v ≠ ξ i → ∃! u, (F i).Adj v u) ∧
      (∀ j < t, i ≠ j → EDisj (F i) (F j)) := by
  classical
  suffices H : ∀ s ≤ t, ∃ F : ℕ → SimpleGraph V, ∀ i < s, F i ≤ X ∧
      (∀ a b, (M i).Adj a b → ∃ j ≤ i, (F j).Adj a b) ∧
      (∀ u, ¬ (F i).Adj (ξ i) u) ∧ (∀ v, v ≠ ξ i → ∃! u, (F i).Adj v u) ∧
      (∀ v u u', (F i).Adj v u → (F i).Adj v u' → u = u') ∧
      (∀ j < s, i ≠ j → EDisj (F i) (F j)) by
    obtain ⟨F, hF⟩ := H t le_rfl
    exact ⟨F, fun i hi => ⟨(hF i hi).1, (hF i hi).2.1, (hF i hi).2.2.1, (hF i hi).2.2.2.1,
      (hF i hi).2.2.2.2.2⟩⟩
  intro s
  induction s with
  | zero => intro _; exact ⟨fun _ => ⊥, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ s ih =>
    intro hst
    obtain ⟨F, hF⟩ := ih (by omega)
    have hs : s < t := by omega
    -- what is left of M s
    let Ms : SimpleGraph V :=
      { Adj := fun a b => (M s).Adj a b ∧ ∀ j < s, ¬ (F j).Adj a b
        symm := ⟨fun a b h => ⟨h.1.symm, fun j hj h' => h.2 j hj h'.symm⟩⟩
        loopless := ⟨fun a h => (M s).loopless.irrefl a h.1⟩ }
    have hMsm : ∀ v u u', Ms.Adj v u → Ms.Adj v u' → u = u' :=
      fun v u u' h h' => hMm s v u u' h.1 h'.1
    have hcov : coverCard Ms ≤ coverCard (M s) := by
      unfold coverCard
      exact Finset.card_le_card (fun v hv => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨u, hu⟩ := hv; exact ⟨u, hu.1⟩)
    -- the available graph
    let R : SimpleGraph V :=
      { Adj := fun a b => X.Adj a b ∧ (∀ i < s, ¬ (F i).Adj a b)
        symm := ⟨fun a b h => ⟨h.1.symm, fun i hi h' => h.2 i hi h'.symm⟩⟩
        loopless := ⟨fun a h => X.loopless.irrefl a h.1⟩ }
    let W : Set V := {v | v ≠ ξ s ∧ ¬ ∃ u, Ms.Adj v u}
    let D : Finset V := Finset.univ.filter (fun u => u = ξ s ∨ ∃ x, Ms.Adj u x)
    have hDcard : D.card = coverCard Ms + 1 := by
      have : D = insert (ξ s) (Finset.univ.filter (fun u => ∃ x, Ms.Adj u x)) := by
        ext u; simp [D]
      rw [this, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
        exact fun x h => hξ s x h.1)]
      unfold coverCard
      congr 1
      exact Finset.card_bij (fun a _ => a) (fun a ha => by simpa using ha) (fun _ _ _ _ h => h)
        (fun b hb => ⟨b, by simpa using hb, rfl⟩)
    have hDle : coverCard Ms + 1 ≤ Fintype.card V := by
      rw [← hDcard]; exact Finset.card_le_univ _
    have hWcard : Fintype.card W = Fintype.card V - 1 - coverCard Ms := by
      have h1 : Fintype.card W = (Finset.univ.filter (fun v => v ∈ W)).card := by
        rw [Fintype.card_subtype]
      have h2 : Finset.univ.filter (fun v => v ∈ W) = Finset.univ \ D := by
        ext v; simp [W, D, not_or]
      rw [h1, h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), hDcard, Finset.card_univ]
      omega
    have hev : Even (Fintype.card W) := by
      rw [hWcard]
      obtain ⟨r, hr⟩ := even_coverCard Ms hMsm
      obtain ⟨q, hq⟩ := hodd
      exact ⟨q - r, by omega⟩
    have hdeg : ∀ x : W, Fintype.card W ≤ 2 * (R.induce W).degree x := by
      intro ⟨v, hv⟩
      let B1 : Finset V := (Finset.range s).biUnion (fun i => Finset.univ.filter (fun u => (F i).Adj v u))
      have hB1 : B1.card ≤ s := by
        refine (Finset.card_biUnion_le).trans ?_
        have : ∀ i ∈ Finset.range s, (Finset.univ.filter (fun u => (F i).Adj v u)).card ≤ 1 := by
          intro i hi
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact (hF i (Finset.mem_range.1 hi)).2.2.2.2.1 v a b ha hb
        refine (Finset.sum_le_sum this).trans ?_
        simp
      let A : Finset V := X.neighborFinset v \ (B1 ∪ D)
      have hA : δ ≤ A.card + s + (coverCard Ms + 1) := by
        have h1 := Finset.card_le_card_sdiff_add_card (s := X.neighborFinset v) (t := B1 ∪ D)
        have h2 := Finset.card_union_le B1 D
        rw [card_neighborFinset_eq_degree] at h1
        have := hδ v
        have hAeq : A.card = (X.neighborFinset v \ (B1 ∪ D)).card := rfl
        omega
      have hinj : A.card ≤ (R.induce W).degree ⟨v, hv⟩ := by
        rw [← card_neighborFinset_eq_degree]
        refine Finset.card_le_card_of_injOn (fun u => if hu : u ∈ W then ⟨u, hu⟩ else ⟨v, hv⟩) ?_ ?_
        · intro u hu
          simp only [A, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, mem_neighborFinset,
            Finset.coe_union, Set.mem_union, not_or] at hu
          obtain ⟨hxu, hu1, hu3⟩ := hu
          have huW : u ∈ W := by
            simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hu3
            exact ⟨hu3.1, hu3.2⟩
          simp only [Finset.mem_coe, dif_pos huW, mem_neighborFinset, comap_adj,
            Function.Embedding.coe_subtype]
          refine ⟨hxu, fun i hi h => hu1 ?_⟩
          simp only [B1, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨i, hi, h⟩
        · intro a ha b hb hab
          have haW : a ∈ W := by
            simp only [A, D, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.coe_union,
              Set.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at ha
            exact ⟨ha.2.2.1, ha.2.2.2⟩
          have hbW : b ∈ W := by
            simp only [A, D, Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, Finset.coe_union,
              Set.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hb
            exact ⟨hb.2.2.1, hb.2.2.2⟩
          simp only [dif_pos haW, dif_pos hbW, Subtype.mk.injEq] at hab
          exact hab
      have := hsize s hs
      rw [hWcard]
      omega
    obtain ⟨P, hP⟩ := exists_isPerfectMatching_of_minDegree (R.induce W) hev hdeg
    let Pl : SimpleGraph V :=
      { Adj := fun a b => ∃ (ha : a ∈ W) (hb : b ∈ W), P.Adj ⟨a, ha⟩ ⟨b, hb⟩
        symm := ⟨fun a b ⟨ha, hb, h⟩ => ⟨hb, ha, h.symm⟩⟩
        loopless := ⟨fun a ⟨ha, _, h⟩ => P.loopless.irrefl _ h⟩ }
    have hPlR : ∀ a b, Pl.Adj a b → R.Adj a b := by
      rintro a b ⟨ha, hb, h⟩
      have := P.adj_sub h
      simpa using this
    have hPlW : ∀ a b, Pl.Adj a b → a ∈ W := fun a b ⟨ha, _, _⟩ => ha
    let Fs : SimpleGraph V := Ms ⊔ Pl
    have hMWnot : ∀ a b, Ms.Adj a b → a ∉ W := fun a b h ha => ha.2 ⟨b, h⟩
    refine ⟨Function.update F s Fs, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    swap
    · subst i
      simp only [Function.update_self]
      refine ⟨sup_le (fun a b h => hMX s h.1) (fun a b h => (hPlR a b h).1), ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        by_cases h : ∃ j < s, (F j).Adj a b
        · obtain ⟨j, hj, h⟩ := h
          refine ⟨j, hj.le, ?_⟩
          rw [Function.update_of_ne (by omega)]; exact h
        · push Not at h
          refine ⟨s, le_rfl, ?_⟩
          rw [Function.update_self]
          exact Or.inl ⟨hab, h⟩
      · intro u h
        rcases h with hm | hp
        · exact hξ s u hm.1
        · exact (hPlW _ _ hp).1 rfl
      · intro v hv
        by_cases hvM : ∃ u, Ms.Adj v u
        · obtain ⟨u, hu⟩ := hvM
          refine ⟨u, Or.inl hu, fun u' hu' => ?_⟩
          rcases hu' with hm | hp
          · exact hMsm v u' u hm hu
          · exact absurd (hPlW _ _ hp) (hMWnot v u hu)
        · have hvW : v ∈ W := ⟨hv, hvM⟩
          obtain ⟨⟨u, huW⟩, hu, huniq⟩ := Subgraph.isPerfectMatching_iff.1 hP ⟨v, hvW⟩
          refine ⟨u, Or.inr ⟨hvW, huW, hu⟩, fun u' hu' => ?_⟩
          rcases hu' with hm | ⟨_, hu'W, hp⟩
          · exact absurd ⟨u', hm⟩ hvM
          · have := huniq ⟨u', hu'W⟩ hp
            exact congrArg Subtype.val this
      · intro v u u' h h'
        rcases h with hm | ⟨hvW, huW, hp⟩ <;> rcases h' with hm' | ⟨hvW', hu'W, hp'⟩
        · exact hMsm v u u' hm hm'
        · exact absurd hvW' (hMWnot v u hm)
        · exact absurd hvW (hMWnot v u' hm')
        · have := hP.1.eq_of_adj_left hp hp'
          exact congrArg Subtype.val this
      · intro j hj hij
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [Function.update_of_ne (by omega)]
          intro a b hab hF'
          rcases hab with hm | hp
          · exact hm.2 j hj hF'
          · exact (hPlR a b hp).2 j hj hF'
        · exact absurd hj.symm hij
    · have hne : i ≠ s := by omega
      simp only [Function.update_of_ne hne]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF i hi
      refine ⟨h1, fun a b hab => ?_, h3, h4, h5, fun j hj hij => ?_⟩
      · obtain ⟨j, hj, h⟩ := h2 a b hab
        refine ⟨j, hj, ?_⟩
        rw [Function.update_of_ne (by omega)]; exact h
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [Function.update_of_ne (by omega)]; exact h6 j hj hij
        · subst j
          rw [Function.update_self]
          intro a b hab hs'
          rcases hs' with hm | hp
          · exact hm.2 i hi hab
          · exact (hPlR a b hp).2 i hi hab

end OMA.H1
-- ===== LemmasKempe.lean =====
-- standalone (Mathlib only); assembled by build_all.sh
/-
Kempe-chain infrastructure for edge colourings given as symmetric "pair functions".
* `three_ends` : in a graph of maximum degree ≤ 2, three distinct vertices of degree ≤ 1 cannot be
  in one connected component.
* `kempe_swap` : swapping two colours on a set closed under edges of those two colours keeps the
  colouring proper, and swaps the missing colours inside the set.
-/
namespace OMA.H1

open SimpleGraph

/-- `c` is a proper edge colouring of `H` (as a pair function) -/
def ProperOn {V α : Type*} (H : SimpleGraph V) (c : V → V → α) : Prop :=
  ∀ v a b, H.Adj v a → H.Adj v b → c v a = c v b → a = b

/-- colour `γ` is missing at `v` -/
def Miss {V α : Type*} (H : SimpleGraph V) (c : V → V → α) (v : V) (γ : α) : Prop :=
  ∀ u, H.Adj v u → c v u ≠ γ

theorem three_ends {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : ∀ v, K.degree v ≤ 2) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : K.degree a ≤ 1) (hb : K.degree b ≤ 1) (hc : K.degree c ≤ 1)
    (h1 : K.Reachable a b) (h2 : K.Reachable a c) : False := by
  classical
  let C := K.connectedComponentMk a
  let T := C.toSimpleGraph
  have hT : T.Connected := C.connected_toSimpleGraph
  have hcard := hT.card_vert_le_card_edgeSet_add_one
  have hsum := T.sum_degrees_eq_twice_card_edges
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at hcard
  -- degrees in T are at most degrees in K
  have hdeg : ∀ x : C, T.degree x ≤ K.degree x.1 := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_le_card_of_injOn Subtype.val (fun u hu => ?_) Subtype.val_injective.injOn
    simp only [Finset.mem_coe, mem_neighborFinset] at hu ⊢
    exact hu
  have ha' : a ∈ C := by
    show a ∈ C.supp; simp [C]
  have hb' : b ∈ C := by
    show b ∈ C.supp
    simp only [C, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]; exact h1.symm
  have hc' : c ∈ C := by
    show c ∈ C.supp
    simp only [C, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]; exact h2.symm
  let A : Finset C := {⟨a, ha'⟩, ⟨b, hb'⟩, ⟨c, hc'⟩}
  have hA : A.card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h; exact hbc (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨hab, hac⟩
  have hle : ∑ x : C, T.degree x ≤ 2 * Fintype.card C - 3 := by
    rw [← Finset.sum_add_sum_compl A]
    have h1 : ∑ x ∈ A, T.degree x ≤ 3 := by
      have : ∀ x ∈ A, T.degree x ≤ 1 := by
        intro x hx
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (hdeg _).trans ha
        · exact (hdeg _).trans hb
        · exact (hdeg _).trans hc
      have := Finset.sum_le_sum this
      simpa [hA] using this
    have h2 : ∑ x ∈ Aᶜ, T.degree x ≤ 2 * Aᶜ.card := by
      have : ∀ x ∈ Aᶜ, T.degree x ≤ 2 := fun x _ => (hdeg x).trans (hK _)
      have := Finset.sum_le_sum this
      simpa [mul_comm] using this
    have h3 : Aᶜ.card = Fintype.card C - 3 := by
      rw [Finset.card_compl, hA]
    have h4 : 3 ≤ Fintype.card C := by
      rw [← hA]; exact Finset.card_le_univ _
    omega
  have h4 : 3 ≤ Fintype.card C := by
    rw [← hA]; exact Finset.card_le_univ _
  omega

/-- Kempe swap of colours `α, β` on a set `S` closed under `α/β`-coloured edges. -/
theorem kempe_swap {V α : Type*} [DecidableEq α] (H : SimpleGraph V) (c : V → V → α)
    (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) (a b : α) (S : Set V)
    (hS : ∀ v u, v ∈ S → H.Adj v u → (c v u = a ∨ c v u = b) → u ∈ S) :
    ∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧ ProperOn H c' ∧
      (∀ v u, v ∉ S → c' v u = c v u) ∧
      (∀ v, v ∉ S → ∀ γ, Miss H c' v γ ↔ Miss H c v γ) ∧
      (∀ v, v ∈ S → ∀ γ, Miss H c' v γ ↔ Miss H c v (Equiv.swap a b γ)) := by
  classical
  let σ := Equiv.swap a b
  let P : V → V → Prop := fun v u => (v ∈ S ∨ u ∈ S) ∧ H.Adj v u ∧ (c v u = a ∨ c v u = b)
  have hP : ∀ v u, P v u ↔ P u v := fun v u => by
    simp only [P, hs v u]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h2.symm, h3⟩⟩
  -- for an edge at v ∈ S, P holds iff the colour is a or b
  have hPin : ∀ v u, v ∈ S → H.Adj v u → (P v u ↔ (c v u = a ∨ c v u = b)) := fun v u hv h =>
    ⟨fun h' => h'.2.2, fun h' => ⟨Or.inl hv, h, h'⟩⟩
  have hPout : ∀ v u, v ∉ S → ¬ P v u := by
    rintro v u hv ⟨h1, h2, h3⟩
    rcases h1 with h1 | h1
    · exact hv h1
    · exact hv (hS u v h1 h2.symm (by rw [hs]; exact h3))
  have hσab : ∀ γ, (γ = a ∨ γ = b) ↔ (σ γ = a ∨ σ γ = b) := by
    intro γ
    by_cases h1 : γ = a
    · subst h1; simp [σ]
    by_cases h2 : γ = b
    · subst h2; simp [σ]
    · simp [σ, Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]
  refine ⟨fun v u => if P v u then σ (c v u) else c v u, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only
    by_cases h : P x y
    · rw [if_pos h, if_pos ((hP x y).1 h), hs]
    · rw [if_neg h, if_neg (fun h' => h ((hP x y).2 h')), hs]
  · intro v x y hx hy e
    simp only at e
    by_cases hv : v ∈ S
    · by_cases px : P v x <;> by_cases py : P v y
      · rw [if_pos px, if_pos py] at e; exact hp v x y hx hy (σ.injective e)
      · rw [if_pos px, if_neg py] at e
        have h1 := (hPin v x hv hx).1 px
        have h2 : ¬ (c v y = a ∨ c v y = b) := fun h => py ((hPin v y hv hy).2 h)
        exact absurd (e ▸ (hσab _).1 h1) h2
      · rw [if_neg px, if_pos py] at e
        have h1 := (hPin v y hv hy).1 py
        have h2 : ¬ (c v x = a ∨ c v x = b) := fun h => px ((hPin v x hv hx).2 h)
        exact absurd (e.symm ▸ (hσab _).1 h1) h2
      · rw [if_neg px, if_neg py] at e; exact hp v x y hx hy e
    · rw [if_neg (hPout v x hv), if_neg (hPout v y hv)] at e
      exact hp v x y hx hy e
  · intro v u hv; simp only [if_neg (hPout v u hv)]
  · intro v hv γ
    simp only [Miss, if_neg (hPout v _ hv)]
  · intro v hv γ
    simp only [Miss]
    refine forall_congr' (fun u => imp_congr_right (fun hu => ?_))
    by_cases pu : P v u
    · rw [if_pos pu]
      constructor
      · intro h h'; apply h; rw [h', Equiv.swap_apply_self]
      · intro h h'; apply h; rw [← h']; simp [σ]
    · rw [if_neg pu]
      have hab : ¬ (c v u = a ∨ c v u = b) := fun h => pu ((hPin v u hv hu).2 h)
      push Not at hab
      constructor
      · intro h h'
        apply h
        rw [h']
        by_cases h1 : γ = a
        · subst h1; exact absurd (by rw [h']; simp) hab.2
        by_cases h2 : γ = b
        · subst h2; exact absurd (by rw [h']; simp) hab.1
        · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
      · intro h h'
        apply h
        rw [← h', Equiv.swap_apply_of_ne_of_ne hab.1 hab.2]

end OMA.H1
-- ===== LemmasFan.lean =====
-- depends on LemmasKempe.lean (ProperOn, Miss); assembled by build_all.sh
/-
Vizing fans: shifting a fan, adding an edge with a commonly missing colour.
-/
namespace OMA.H1

open SimpleGraph

lemma ProperOn.mono {V α : Type*} {G G' : SimpleGraph V} {c : V → V → α} (h : ProperOn G c)
    (hle : ∀ a b, G'.Adj a b → G.Adj a b) : ProperOn G' c :=
  fun v a b ha hb e => h v a b (hle _ _ ha) (hle _ _ hb) e

lemma Miss.mono {V α : Type*} {G G' : SimpleGraph V} {c : V → V → α} {v : V} {γ : α}
    (h : Miss G c v γ) (hle : ∀ a b, G'.Adj a b → G.Adj a b) : Miss G' c v γ :=
  fun u hu => h u (hle _ _ hu)

/-- a vertex of degree `< D` misses one of `D` colours -/
lemma exists_miss_of_degree_lt {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {D : ℕ} (c : V → V → Fin D) (v : V) (hv : H.degree v < D) :
    ∃ γ, Miss H c v γ := by
  classical
  by_contra h0
  have h : ∀ γ, ∃ u, H.Adj v u ∧ c v u = γ := by
    intro γ
    by_contra hc
    push Not at hc
    exact h0 ⟨γ, hc⟩
  have hsub : (Finset.univ : Finset (Fin D)) ⊆ (H.neighborFinset v).image (c v) := by
    intro γ _
    obtain ⟨u, hu, e⟩ := h γ
    exact Finset.mem_image.2 ⟨u, (mem_neighborFinset _ _ _).2 hu, e⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_univ, Fintype.card_fin, card_neighborFinset_eq_degree] at this
  omega

/-- add an edge `uv` coloured with a colour missing at both ends -/
lemma add_edge_coloring {V α : Type*} [DecidableEq V] (G : SimpleGraph V) (c : V → V → α)
    (hs : ∀ x y, c x y = c y x) (hp : ProperOn G c) {u v : V} (hne : u ≠ v)
    (hnadj : ¬ G.Adj u v) (γ : α) (hu : Miss G c u γ) (hv : Miss G c v γ) :
    ∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧ ProperOn (G ⊔ edge u v) c' ∧
      (∀ x y, G.Adj x y → c' x y = c x y) := by
  classical
  let P : V → V → Prop := fun a b => (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  refine ⟨fun a b => if P a b then γ else c a b, ?_, ?_, ?_⟩
  · intro x y
    by_cases h : P x y
    · have h' : P y x := by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [P]
      simp only [if_pos h, if_pos h']
    · have h' : ¬ P y x := fun h' => h (by rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [P])
      simp only [if_neg h, if_neg h', hs]
  · intro x a b ha hb e
    simp only [sup_adj, edge_adj] at ha hb
    simp only at e
    -- P x a iff edge is the new one
    have hPa : P x a ↔ ¬ G.Adj x a := by
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hnadj
        · exact fun h => hnadj h.symm
      · intro h; rcases ha with ha | ha
        · exact absurd ha h
        · exact ha.1
    have hPb : P x b ↔ ¬ G.Adj x b := by
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hnadj
        · exact fun h => hnadj h.symm
      · intro h; rcases hb with hb | hb
        · exact absurd hb h
        · exact hb.1
    by_cases pa : P x a <;> by_cases pb : P x b
    · rcases pa with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases pb with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h2, h4]
      · exact absurd (h1.symm.trans h3) hne
      · exact absurd (h3.symm.trans h1) hne
      · rw [h2, h4]
    · rw [if_pos pa, if_neg pb] at e
      have hxb : G.Adj x b := by by_contra h; exact pb (hPb.2 h)
      rcases pa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd e.symm (hu b hxb)
      · exact absurd e.symm (hv b hxb)
    · rw [if_neg pa, if_pos pb] at e
      have hxa : G.Adj x a := by by_contra h; exact pa (hPa.2 h)
      rcases pb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd e (hu a hxa)
      · exact absurd e (hv a hxa)
    · rw [if_neg pa, if_neg pb] at e
      have hxa : G.Adj x a := by by_contra h; exact pa (hPa.2 h)
      have hxb : G.Adj x b := by by_contra h; exact pb (hPb.2 h)
      exact hp x a b hxa hxb e
  · intro x y h
    have : ¬ P x y := by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hnadj h
      · exact hnadj h.symm
    simp only [if_neg this]

/-- data of a fan at `w` starting at the uncoloured neighbour `y` -/
structure IsFan {V α : Type*} (H : SimpleGraph V) (c : V → V → α) (w y : V) (f : ℕ → V) (j : ℕ) :
    Prop where
  zero : f 0 = y
  adj : ∀ i, 1 ≤ i → i ≤ j → H.Adj w (f i)
  inj : ∀ i i', i ≤ j → i' ≤ j → f i = f i' → i = i'
  miss : ∀ i, 1 ≤ i → i ≤ j → Miss H c (f (i - 1)) (c w (f i))

lemma IsFan.init {V α : Type*} {H : SimpleGraph V} {c : V → V → α} {w y : V} {f : ℕ → V} {j : ℕ}
    (hf : IsFan H c w y f j) {i : ℕ} (hi : i ≤ j) : IsFan H c w y f i :=
  ⟨hf.zero, fun k h1 h2 => hf.adj k h1 (h2.trans hi), fun k k' h1 h2 e => hf.inj k k' (h1.trans hi)
    (h2.trans hi) e, fun k h1 h2 => hf.miss k h1 (h2.trans hi)⟩

/-- shifting a fan: recolour `w f_i` with the old colour of `w f_{i+1}` (i < j); the edge `w f_j`
becomes uncoloured. -/
theorem shift_open {V α : Type*} [DecidableEq V] (H : SimpleGraph V) (c : V → V → α)
    (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) {w y : V} (hwy : ¬ H.Adj w y) (hne : w ≠ y)
    {f : ℕ → V} {j : ℕ} (hf : IsFan H c w y f j) :
    ∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧
      ProperOn ((H ⊔ edge w y).deleteEdges {s(w, f j)}) c' ∧
      (∀ γ, Miss H c w γ → Miss ((H ⊔ edge w y).deleteEdges {s(w, f j)}) c' w γ) ∧
      (∀ γ, Miss H c (f j) γ → Miss ((H ⊔ edge w y).deleteEdges {s(w, f j)}) c' (f j) γ) := by
  classical
  have hfw : ∀ i, i ≤ j → f i ≠ w := by
    intro i hi h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hf.zero] at h; exact hne h.symm
    · exact H.loopless.irrefl w (h ▸ hf.adj i hpos hi)
  let inF : V → Prop := fun b => ∃ i, i ≤ j ∧ f i = b
  let idx : V → ℕ := fun b => if h : inF b then Nat.find h else 0
  have hidx : ∀ i, i ≤ j → idx (f i) = i := by
    intro i hi
    have h : inF (f i) := ⟨i, hi, rfl⟩
    simp only [idx, dif_pos h]
    have := Nat.find_spec h
    exact hf.inj _ _ this.1 hi this.2
  have hfidx : ∀ b, inF b → f (idx b) = b ∧ idx b ≤ j := by
    intro b h
    simp only [idx, dif_pos h]
    exact ⟨(Nat.find_spec h).2, (Nat.find_spec h).1⟩
  let nc : V → α := fun b => c w (f (idx b + 1))
  let c' : V → V → α := fun a b =>
    if a = w ∧ inF b then nc b else if b = w ∧ inF a then nc a else c a b
  -- G'-adjacency
  let G' := (H ⊔ edge w y).deleteEdges {s(w, f j)}
  have hG' : ∀ a b, G'.Adj a b ↔ (H.Adj a b ∨ ((a = w ∧ b = y) ∨ (a = y ∧ b = w))) ∧
      ¬ ((a = w ∧ b = f j) ∨ (a = f j ∧ b = w)) := by
    intro a b
    simp only [G', deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases h1 with h1 | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · refine Or.inr ⟨h1, ?_⟩
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hne
        · exact hne.symm
  have hyF : inF y := ⟨0, Nat.zero_le _, hf.zero⟩
  -- G' neighbours of v ≠ w which are not w are H-neighbours
  have hHadj : ∀ a b, G'.Adj a b → a ≠ w → b ≠ w → H.Adj a b := by
    intro a b h ha hb
    rcases ((hG' a b).1 h).1 with h | ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact h
    · exact absurd rfl ha
    · exact absurd rfl hb
  -- neighbours of w in G'
  have hwnb : ∀ x, G'.Adj w x → (inF x ∧ idx x < j) ∨ (¬ inF x ∧ H.Adj w x) := by
    intro x h
    obtain ⟨h1, h2⟩ := (hG' w x).1 h
    by_cases hx : inF x
    · left
      refine ⟨hx, ?_⟩
      obtain ⟨e1, e2⟩ := hfidx x hx
      rcases lt_or_eq_of_le e2 with h3 | h3
      · exact h3
      · exact absurd (Or.inl ⟨rfl, by rw [← e1, h3]⟩) h2
    · right
      refine ⟨hx, ?_⟩
      rcases h1 with h1 | ⟨-, rfl⟩ | ⟨h3, -⟩
      · exact h1
      · exact absurd hyF hx
      · exact absurd h3 hne
  have hnc_adj : ∀ x, inF x → idx x < j → H.Adj w (f (idx x + 1)) := fun x hx h =>
    hf.adj _ (by omega) (by omega)
  have hwF : ¬ inF w := fun ⟨i, hi, h⟩ => hfw i hi h
  have hc'w : ∀ x, c' w x = if inF x then nc x else c w x := by
    intro x
    by_cases hx : inF x
    · simp only [c', hx, true_and, if_true]
    · simp only [c', hx, hwF, and_false, if_false]
  have hc'v : ∀ v x, v ≠ w → x ≠ w → c' v x = c v x := by
    intro v x hv hx; simp [c', hv, hx]
  have hc'vw : ∀ v, v ≠ w → c' v w = if inF v then nc v else c v w := by
    intro v hv
    by_cases h : inF v <;> simp [c', hv, h]
  refine ⟨c', ?_, ?_, ?_, ?_⟩
  · intro a b
    by_cases ha : a = w <;> by_cases hb : b = w
    · subst ha; subst hb; rfl
    · subst ha; rw [hc'w, hc'vw b hb, hs a b]
    · subst hb; rw [hc'w, hc'vw a ha, hs a b]
    · rw [hc'v a b ha hb, hc'v b a hb ha, hs]
  · intro v a b ha hb e
    by_cases hv : v = w
    · subst hv
      rw [hc'w, hc'w] at e
      rcases hwnb a ha with ⟨fa, ia⟩ | ⟨fa, ha'⟩ <;> rcases hwnb b hb with ⟨fb, ib⟩ | ⟨fb, hb'⟩
      · rw [if_pos fa, if_pos fb] at e
        have := hp _ _ _ (hnc_adj a fa ia) (hnc_adj b fb ib) e
        have := hf.inj _ _ (by omega) (by omega) this
        rw [← (hfidx a fa).1, ← (hfidx b fb).1]; congr 1; omega
      · rw [if_pos fa, if_neg fb] at e
        have := hp _ _ _ (hnc_adj a fa ia) hb' e
        exact absurd ⟨_, by omega, this⟩ fb
      · rw [if_neg fa, if_pos fb] at e
        have := hp _ _ _ ha' (hnc_adj b fb ib) e
        exact absurd ⟨_, by omega, this.symm⟩ fa
      · rw [if_neg fa, if_neg fb] at e
        exact hp _ _ _ ha' hb' e
    · have hcol : ∀ x, G'.Adj v x → x ≠ w → c' v x = c v x ∧ H.Adj v x := fun x hx hxw =>
        ⟨hc'v v x hv hxw, hHadj v x hx hv hxw⟩
      by_cases haw : a = w <;> by_cases hbw : b = w
      · rw [haw, hbw]
      · -- edge v w and edge v b
        subst haw
        obtain ⟨e1, e2⟩ := hcol b hb hbw
        rw [hc'vw v hv, e1] at e
        by_cases hvF : inF v
        · rw [if_pos hvF] at e
          obtain ⟨hfv, hiv⟩ := hfidx v hvF
          have hlt : idx v < j := by
            rcases lt_or_eq_of_le hiv with h | h
            · exact h
            · exfalso
              have := (hG' v a).1 ha
              exact this.2 (Or.inr ⟨by rw [← hfv, h], rfl⟩)
          have hm := hf.miss (idx v + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel, hfv] at hm
          exact absurd e.symm (hm b e2)
        · rw [if_neg hvF] at e
          have hva : H.Adj v a := by
            rcases ((hG' v a).1 ha).1 with h | ⟨h, -⟩ | ⟨h, -⟩
            · exact h
            · exact absurd h hv
            · exact absurd (h ▸ hyF) hvF
          exact hp _ _ _ hva e2 e
      · subst hbw
        obtain ⟨e1, e2⟩ := hcol a ha haw
        rw [hc'vw v hv, e1] at e
        by_cases hvF : inF v
        · rw [if_pos hvF] at e
          obtain ⟨hfv, hiv⟩ := hfidx v hvF
          have hlt : idx v < j := by
            rcases lt_or_eq_of_le hiv with h | h
            · exact h
            · exfalso
              have := (hG' v b).1 hb
              exact this.2 (Or.inr ⟨by rw [← hfv, h], rfl⟩)
          have hm := hf.miss (idx v + 1) (by omega) (by omega)
          simp only [Nat.add_sub_cancel, hfv] at hm
          exact absurd e (hm a e2)
        · rw [if_neg hvF] at e
          have hvb : H.Adj v b := by
            rcases ((hG' v b).1 hb).1 with h | ⟨h, -⟩ | ⟨h, -⟩
            · exact h
            · exact absurd h hv
            · exact absurd (h ▸ hyF) hvF
          exact hp _ _ _ e2 hvb e
      · obtain ⟨e1, e2⟩ := hcol a ha haw
        obtain ⟨e3, e4⟩ := hcol b hb hbw
        rw [e1, e3] at e
        exact hp _ _ _ e2 e4 e
  · intro γ hγ x hx
    rw [hc'w]
    rcases hwnb x hx with ⟨fx, ix⟩ | ⟨fx, hx'⟩
    · rw [if_pos fx]; exact hγ _ (hnc_adj x fx ix)
    · rw [if_neg fx]; exact hγ _ hx'
  · intro γ hγ x hx
    have hxw : x ≠ w := by
      rintro rfl
      exact ((hG' _ _).1 hx).2 (Or.inr ⟨rfl, rfl⟩)
    rw [hc'v _ _ (hfw j le_rfl) hxw]
    exact hγ x (hHadj _ _ hx (hfw j le_rfl) hxw)

/-- shifting a fan and colouring the last edge with a colour missing at `w` and at `f j` -/
theorem shift_close {V α : Type*} [DecidableEq V] (H : SimpleGraph V) (c : V → V → α)
    (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) {w y : V} (hwy : ¬ H.Adj w y) (hne : w ≠ y)
    {f : ℕ → V} {j : ℕ} (hf : IsFan H c w y f j) (γ : α) (hw : Miss H c w γ)
    (hj : Miss H c (f j) γ) :
    ∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧ ProperOn (H ⊔ edge w y) c' := by
  classical
  obtain ⟨c1, hs1, hp1, hw1, hj1⟩ := shift_open H c hs hp hwy hne hf
  have hfw : f j ≠ w := by
    intro h
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [hf.zero] at h; exact hne h.symm
    · exact H.loopless.irrefl w (h ▸ hf.adj j hpos le_rfl)
  obtain ⟨c2, hs2, hp2, -⟩ := add_edge_coloring _ c1 hs1 hp1 (Ne.symm hfw)
    (by simp [deleteEdges_adj]) γ (hw1 γ hw) (hj1 γ hj)
  refine ⟨c2, hs2, hp2.mono ?_⟩
  intro a b h
  simp only [sup_adj, deleteEdges_adj, edge_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h ⊢
  by_cases hab : (a = w ∧ b = f j) ∨ (a = f j ∧ b = w)
  · right
    refine ⟨hab, ?_⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Ne.symm hfw
    · exact hfw
  · left
    refine ⟨?_, hab⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h

end OMA.H1
-- ===== LemmasVizing.lean =====
-- depends on LemmasKempe.lean, LemmasFan.lean, LemmasDelete.lean; assembled by build_all.sh
/-
Vizing's fan argument (Chetwynd–Hilton 1989, Lemma 1, edge form): if all degrees are `≤ D`,
`wy` is an edge and `w` has at most one neighbour of degree `D`, then a `D`-edge-colouring of
`G - wy` gives a `D`-edge-colouring of `G`.
-/
namespace OMA.H1

open SimpleGraph OMA.R_wp_1_factorization_conjecture_R1

/-- the `a/β`-subgraph of a pair colouring -/
def twoColGraph {V α : Type*} (H : SimpleGraph V) (c : V → V → α) (hs : ∀ x y, c x y = c y x)
    (a b : α) : SimpleGraph V where
  Adj p q := H.Adj p q ∧ (c p q = a ∨ c p q = b)
  symm := ⟨fun p q h => ⟨h.1.symm, by rw [hs]; exact h.2⟩⟩
  loopless := ⟨fun p h => H.loopless.irrefl p h.1⟩

lemma twoColGraph_degree_le_one {V α : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (c : V → V → α) (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) (a b : α)
    [DecidableRel (twoColGraph H c hs a b).Adj] (v : V) (hv : Miss H c v a ∨ Miss H c v b) :
    (twoColGraph H c hs a b).degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro p hp' q hq
  rw [mem_neighborFinset] at hp' hq
  simp only [twoColGraph] at hp' hq
  rcases hv with hv | hv
  · have e1 : c v p = b := hp'.2.resolve_left (hv p hp'.1)
    have e2 : c v q = b := hq.2.resolve_left (hv q hq.1)
    exact hp v p q hp'.1 hq.1 (e1.trans e2.symm)
  · have e1 : c v p = a := hp'.2.resolve_right (hv p hp'.1)
    have e2 : c v q = a := hq.2.resolve_right (hv q hq.1)
    exact hp v p q hp'.1 hq.1 (e1.trans e2.symm)

lemma twoColGraph_degree_le_two {V α : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (c : V → V → α) (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) (a b : α)
    [DecidableRel (twoColGraph H c hs a b).Adj] (v : V) :
    (twoColGraph H c hs a b).degree v ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have hsub : (twoColGraph H c hs a b).neighborFinset v ⊆
      (Finset.univ.filter (fun p => H.Adj v p ∧ c v p = a)) ∪
      (Finset.univ.filter (fun p => H.Adj v p ∧ c v p = b)) := by
    intro p hp'
    rw [mem_neighborFinset] at hp'
    simp only [twoColGraph] at hp'
    rcases hp'.2 with h | h <;> simp [hp'.1, h]
  have h1 : (Finset.univ.filter (fun p => H.Adj v p ∧ c v p = a)).card ≤ 1 := by
    rw [Finset.card_le_one]; intro p hp' q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp' hq
    exact hp v p q hp'.1 hq.1 (hp'.2.trans hq.2.symm)
  have h2 : (Finset.univ.filter (fun p => H.Adj v p ∧ c v p = b)).card ≤ 1 := by
    rw [Finset.card_le_one]; intro p hp' q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp' hq
    exact hp v p q hp'.1 hq.1 (hp'.2.trans hq.2.symm)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma fan_bound {V α : Type*} [Fintype V] {H : SimpleGraph V} {c : V → V → α} {w y : V}
    {f : ℕ → V} {j : ℕ} (hf : IsFan H c w y f j) : j < Fintype.card V := by
  classical
  have : (Finset.range (j + 1)).card ≤ (Finset.univ : Finset V).card :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
      (fun i hi i' hi' e => hf.inj i i' (by simp at hi; omega) (by simp at hi'; omega) e)
  simp at this; omega

/-- Vizing's fan lemma with (at most) one "bad" neighbour `z` of `w` that may miss no colour.
Either the colouring extends to `wy`, or `z` is a neighbour of `w` and after a fan shift the
uncoloured edge is `wz`. -/
theorem fan_lemma {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α] (H : SimpleGraph V)
    (c : V → V → α) (hs : ∀ x y, c x y = c y x) (hp : ProperOn H c) {w y z : V}
    (hwy : ¬ H.Adj w y) (hne : w ≠ y) (a : α) (ha : Miss H c w a)
    (hmiss : ∀ v, (v = y ∨ (H.Adj w v ∧ v ≠ z)) → ∃ γ, Miss H c v γ) :
    (∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧ ProperOn (H ⊔ edge w y) c') ∨
    (H.Adj w z ∧ ∃ c' : V → V → α, (∀ x y, c' x y = c' y x) ∧
      ProperOn ((H ⊔ edge w y).deleteEdges {s(w, z)}) c') := by
  classical
  let P : ℕ → Prop := fun j => ∃ f, IsFan H c w y f j ∧ ∀ i, 1 ≤ i → i ≤ j → f i ≠ z
  have hP0 : P 0 := ⟨fun _ => y, ⟨rfl, fun i h1 h2 => by omega, fun i i' h1 h2 _ => by omega,
    fun i h1 h2 => by omega⟩, fun i h1 h2 => by omega⟩
  let K := Nat.findGreatest P (Fintype.card V)
  have hPK : P K := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ¬ P (K + 1) := by
    intro h
    obtain ⟨f, hf, hfz'⟩ := h
    have hb := fan_bound hf
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self K) (by omega) ⟨f, hf, hfz'⟩
  obtain ⟨f, hf, hfz⟩ := hPK
  have hfw : ∀ i, i ≤ K → f i ≠ w := by
    intro i hi h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hf.zero] at h; exact hne h.symm
    · exact H.loopless.irrefl w (h ▸ hf.adj i hpos hi)
  -- case 1: some fan vertex misses a
  by_cases h1 : ∃ i, i ≤ K ∧ Miss H c (f i) a
  · obtain ⟨i, hi, hm⟩ := h1
    exact Or.inl (shift_close H c hs hp hwy hne (hf.init hi) a ha hm)
  push Not at h1
  obtain ⟨β, hβ⟩ : ∃ β, Miss H c (f K) β := by
    apply hmiss
    rcases Nat.eq_zero_or_pos K with h | h
    · left; rw [h, hf.zero]
    · right; exact ⟨hf.adj K h le_rfl, hfz K h le_rfl⟩
  -- case 2: β missing at w
  by_cases h2 : Miss H c w β
  · exact Or.inl (shift_close H c hs hp hwy hne hf β h2 hβ)
  obtain ⟨u, hu, hcu⟩ : ∃ u, H.Adj w u ∧ c w u = β := by
    by_contra h; push Not at h; exact h2 h
  -- extending the fan by u
  have hext : (∀ i, i ≤ K → f i ≠ u) →
      IsFan H c w y (fun i => if i = K + 1 then u else f i) (K + 1) := by
    intro hfu
    refine ⟨by simp [hf.zero], fun i h1 h2 => ?_, fun i i' h1 h2 e => ?_, fun i h1 h2 => ?_⟩
    · by_cases hi : i = K + 1
      · simp only [hi, if_true]; exact hu
      · simp only [hi, if_false]; exact hf.adj i h1 (by omega)
    · by_cases hi : i = K + 1 <;> by_cases hi' : i' = K + 1
      · omega
      · simp only [hi, hi', if_true, if_false] at e; exact absurd e.symm (hfu i' (by omega))
      · simp only [hi, hi', if_true, if_false] at e; exact absurd e (hfu i (by omega))
      · simp only [hi, hi', if_false] at e; exact hf.inj i i' (by omega) (by omega) e
    · by_cases hi : i = K + 1
      · subst hi
        simp only [if_true, Nat.add_sub_cancel, show K ≠ K + 1 by omega, if_false, hcu]
        exact hβ
      · have : i - 1 ≠ K + 1 := by omega
        simp only [hi, this, if_false]
        exact hf.miss i h1 (by omega)
  by_cases hfu : ∀ i, i ≤ K → f i ≠ u
  · by_cases huz : u = z
    · -- case 3: the bad vertex
      subst huz
      right
      refine ⟨hu, ?_⟩
      obtain ⟨c', hs', hp', -⟩ := shift_open H c hs hp hwy hne (hext hfu)
      exact ⟨c', hs', by simpa using hp'⟩
    · -- case 5: the fan was not maximal
      exfalso
      apply hmax
      refine ⟨_, hext hfu, fun i h1 h2 => ?_⟩
      by_cases hi : i = K + 1
      · simp only [hi, if_true]; exact huz
      · simp only [hi, if_false]; exact hfz i h1 (by omega)
  -- case 4: u = f j is in the fan: Kempe chain
  push Not at hfu
  obtain ⟨j, hjK, hju⟩ := hfu
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, hf.zero] at hju; exact absurd (hju ▸ hu) hwy
    · exact h
  have hab : a ≠ β := fun h => ha u hu (hcu.trans h.symm)
  have hmj : Miss H c (f (j - 1)) β := by rw [← hcu, ← hju]; exact hf.miss j hj1 hjK
  let Kg := twoColGraph H c hs a β
  have hKdeg := twoColGraph_degree_le_two H c hs hp a β
  have hdw : Kg.degree w ≤ 1 := twoColGraph_degree_le_one H c hs hp a β w (Or.inl ha)
  have hdj : Kg.degree (f (j - 1)) ≤ 1 := twoColGraph_degree_le_one H c hs hp a β _ (Or.inr hmj)
  have hdK : Kg.degree (f K) ≤ 1 := twoColGraph_degree_le_one H c hs hp a β _ (Or.inr hβ)
  have hne1 : w ≠ f (j - 1) := fun h => hfw (j - 1) (by omega) h.symm
  have hne2 : w ≠ f K := fun h => hfw K le_rfl h.symm
  have hne3 : f (j - 1) ≠ f K := fun h => by have := hf.inj _ _ (by omega) le_rfl h; omega
  -- closedness of reachability sets
  have hclosed : ∀ x : V, ∀ v u, v ∈ {v | Kg.Reachable x v} → H.Adj v u → (c v u = a ∨ c v u = β) →
      u ∈ {v | Kg.Reachable x v} := by
    intro x v u hv h1 h2
    exact Reachable.trans hv (Adj.reachable (show Kg.Adj v u from ⟨h1, h2⟩))
  -- colours of fan edges other than j avoid a and β
  have hcol : ∀ i, 1 ≤ i → i ≤ K → i ≠ j → c w (f i) ≠ a ∧ c w (f i) ≠ β := by
    intro i h1 h2 hij
    refine ⟨ha _ (hf.adj i h1 h2), fun e => hij ?_⟩
    have := hp w _ _ (hf.adj i h1 h2) hu (e.trans hcu.symm)
    exact hf.inj i j h2 hjK (this.trans hju.symm)
  left
  by_cases hr : Kg.Reachable w (f (j - 1))
  · -- swap the chain at f K
    have hr2 : ¬ Kg.Reachable w (f K) := fun h =>
      three_ends Kg hKdeg hne1 hne2 hne3 hdw hdj hdK hr h
    let S := {v | Kg.Reachable (f K) v}
    obtain ⟨c'', hs'', hp'', hout, hmo, hmi⟩ := kempe_swap H c hs hp a β S (hclosed (f K))
    have hwS : w ∉ S := fun h => hr2 h.symm
    have hjS : f (j - 1) ∉ S := fun h => hr2 (hr.trans h.symm)
    have hKS : f K ∈ S := Reachable.refl _
    have hf'' : IsFan H c'' w y f K := by
      refine ⟨hf.zero, hf.adj, hf.inj, fun i h1 h2 => ?_⟩
      rw [hout w _ hwS]
      by_cases hij : i = j
      · subst hij; exact (hmo _ hjS _).2 (hf.miss i h1 h2)
      · obtain ⟨n1, n2⟩ := hcol i h1 h2 hij
        by_cases hS : f (i - 1) ∈ S
        · rw [hmi _ hS, Equiv.swap_apply_of_ne_of_ne n1 n2]; exact hf.miss i h1 h2
        · exact (hmo _ hS _).2 (hf.miss i h1 h2)
    refine shift_close H c'' hs'' hp'' hwy hne hf'' a ((hmo w hwS a).2 ha) ?_
    rw [hmi _ hKS, Equiv.swap_apply_left]; exact hβ
  · -- swap the chain at f (j - 1)
    let S := {v | Kg.Reachable (f (j - 1)) v}
    obtain ⟨c'', hs'', hp'', hout, hmo, hmi⟩ := kempe_swap H c hs hp a β S (hclosed (f (j - 1)))
    have hwS : w ∉ S := fun h => hr h.symm
    have hjS : f (j - 1) ∈ S := Reachable.refl _
    have hf'' : IsFan H c'' w y f (j - 1) := by
      refine ⟨hf.zero, fun i h1 h2 => hf.adj i h1 (by omega),
        fun i i' h1 h2 e => hf.inj i i' (by omega) (by omega) e, fun i h1 h2 => ?_⟩
      rw [hout w _ hwS]
      obtain ⟨n1, n2⟩ := hcol i h1 (by omega) (by omega)
      by_cases hS : f (i - 1) ∈ S
      · rw [hmi _ hS, Equiv.swap_apply_of_ne_of_ne n1 n2]; exact hf.miss i h1 (by omega)
      · exact (hmo _ hS _).2 (hf.miss i h1 (by omega))
    refine shift_close H c'' hs'' hp'' hwy hne hf'' a ((hmo w hwS a).2 ha) ?_
    rw [hmi _ hjS, Equiv.swap_apply_left]; exact hmj

end OMA.H1
-- ===== LemmasPivot.lean =====
-- depends on LemmasKempe, LemmasFan, LemmasVizing; assembled by build_all.sh
/-
Graph-level forms of the fan lemma (CH Lemma 1) and the sequential edge-adding lemma.
`Colorable D G` : `G` has a proper `D`-edge-colouring, as a symmetric pair function.
-/
namespace OMA.H1

open SimpleGraph OMA.R_wp_1_factorization_conjecture_R1

def Colorable {V : Type*} (D : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ c : V → V → Fin D, (∀ x y, c x y = c y x) ∧ ProperOn G c

lemma Colorable.mono {V : Type*} {D : ℕ} {G G' : SimpleGraph V} (h : Colorable D G)
    (hle : ∀ a b, G'.Adj a b → G.Adj a b) : Colorable D G' :=
  let ⟨c, hs, hp⟩ := h; ⟨c, hs, hp.mono hle⟩

lemma lineGraph_coloring_of_colorable {V : Type*} {D : ℕ} {G : SimpleGraph V}
    (h : Colorable D G) : Nonempty (G.lineGraph.Coloring (Fin D)) :=
  let ⟨c, hs, hp⟩ := h; coloring_of_pair G c hs hp

lemma colorable_of_lineGraph_coloring {V : Type*} {D : ℕ} [NeZero D] {G : SimpleGraph V}
    (C : G.lineGraph.Coloring (Fin D)) : Colorable D G :=
  let ⟨c, hs, hp, _⟩ := pair_of_coloring G C; ⟨c, hs, hp⟩

lemma degree_le_of_sub {V : Type*} [Fintype V] {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (hle : ∀ a b, G'.Adj a b → G.Adj a b) (v : V) :
    G'.degree v ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  exact Finset.card_le_card (fun u hu => by
    rw [mem_neighborFinset] at hu ⊢; exact hle _ _ hu)

lemma degree_lt_of_sub {V : Type*} [Fintype V] {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (hle : ∀ a b, G'.Adj a b → G.Adj a b) {v u : V} (h1 : G.Adj v u)
    (h2 : ¬ G'.Adj v u) : G'.degree v < G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_lt_card ⟨fun x hx => by rw [mem_neighborFinset] at hx ⊢; exact hle _ _ hx,
    fun h => h2 ?_⟩
  have := h ((mem_neighborFinset _ _ _).2 h1)
  rwa [mem_neighborFinset] at this

/-- CH Lemma 1 (edge form) / Vizing fan argument. -/
theorem colorable_of_pivot {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {D : ℕ} (hD : ∀ v, G.degree v ≤ D) {w y : V} (hwy : G.Adj w y)
    (hstar : ∀ a b, G.Adj w a → G.Adj w b → G.degree a = D → G.degree b = D → a = b)
    (hC : Colorable D (G.deleteEdges {s(w, y)})) : Colorable D G := by
  classical
  obtain ⟨c, hs, hp⟩ := hC
  set H := G.deleteEdges {s(w, y)}
  have hHG : ∀ a b, H.Adj a b → G.Adj a b := fun a b h => h.1
  have hne : w ≠ y := G.ne_of_adj hwy
  have hHwy : ¬ H.Adj w y := by simp [H]
  have hback : ∀ (H' : SimpleGraph V) (x : V), (∀ a b, G.Adj a b → ¬ (s(a, b) = s(w, x)) →
      H'.Adj a b) → G.Adj w x → ∀ a b, G.Adj a b → (H' ⊔ edge w x).Adj a b := by
    intro H' x h hx a b hab
    by_cases e : s(a, b) = s(w, x)
    · right
      rw [edge_adj]
      refine ⟨?_, G.ne_of_adj hab⟩
      rcases Sym2.eq_iff.1 e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    · left; exact h a b hab e
  have hdw : H.degree w < D := (degree_lt_of_sub hHG hwy hHwy).trans_le (hD w)
  have hdy : H.degree y < D := (degree_lt_of_sub hHG hwy.symm (fun h => hHwy h.symm)).trans_le (hD y)
  obtain ⟨a, ha⟩ := exists_miss_of_degree_lt H c w hdw
  by_cases hz : ∃ z, G.Adj w z ∧ z ≠ y ∧ G.degree z = D
  · obtain ⟨z, hwz, hzy, hzD⟩ := hz
    have hmiss : ∀ v, (v = y ∨ (H.Adj w v ∧ v ≠ z)) → ∃ γ, Miss H c v γ := by
      rintro v (rfl | ⟨h1, h2⟩)
      · exact exists_miss_of_degree_lt H c v hdy
      · apply exists_miss_of_degree_lt H c v
        have : G.degree v ≠ D := fun e => h2 (hstar v z (hHG _ _ h1) hwz e hzD)
        exact (degree_le_of_sub hHG v).trans_lt (lt_of_le_of_ne (hD v) this)
    rcases fan_lemma H c hs hp hHwy hne a ha hmiss with ⟨c', hs', hp'⟩ | ⟨-, c', hs', hp'⟩
    · exact ⟨c', hs', hp'.mono (hback H y (fun a b h e => ⟨h, fun h' => e (Set.mem_singleton_iff.1 ((fromEdgeSet_adj _).1 h').1)⟩) hwy)⟩
    · -- the uncoloured edge is now wz
      set H' := (H ⊔ edge w y).deleteEdges {s(w, z)}
      let _ : DecidableRel H'.Adj := Classical.decRel _
      have hH'adj : ∀ a b, H'.Adj a b ↔ G.Adj a b ∧ ¬ s(a, b) = s(w, z) := by
        intro a b
        simp only [H', H, deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1 | ⟨h1, h1'⟩, h2⟩
          · exact ⟨h1.1, h2⟩
          · refine ⟨?_, h2⟩
            rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hwy
            · exact hwy.symm
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          by_cases e : s(a, b) = s(w, y)
          · right
            refine ⟨?_, G.ne_of_adj h1⟩
            rcases Sym2.eq_iff.1 e with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact Or.inl ⟨e1, e2⟩
            · exact Or.inr ⟨e1, e2⟩
          · exact Or.inl ⟨h1, e⟩
      have hH'G : ∀ a b, H'.Adj a b → G.Adj a b := fun a b h => ((hH'adj a b).1 h).1
      have hH'wz : ¬ H'.Adj w z := fun h => ((hH'adj w z).1 h).2 rfl
      have hwz' : w ≠ z := G.ne_of_adj hwz
      have hdw' : H'.degree w < D := (degree_lt_of_sub hH'G hwz hH'wz).trans_le (hD w)
      have hdz' : H'.degree z < D :=
        (degree_lt_of_sub hH'G hwz.symm (fun h => hH'wz h.symm)).trans_le (hD z)
      obtain ⟨a', ha'⟩ := exists_miss_of_degree_lt H' c' w hdw'
      have hmiss' : ∀ v, (v = z ∨ (H'.Adj w v ∧ v ≠ z)) → ∃ γ, Miss H' c' v γ := by
        rintro v (rfl | ⟨h1, h2⟩)
        · exact exists_miss_of_degree_lt H' c' v hdz'
        · apply exists_miss_of_degree_lt H' c' v
          have : G.degree v ≠ D := fun e => h2 (hstar v z (hH'G _ _ h1) hwz e hzD)
          exact (degree_le_of_sub hH'G v).trans_lt (lt_of_le_of_ne (hD v) this)
      rcases fan_lemma H' c' hs' hp' hH'wz hwz' a' ha' hmiss' with ⟨c'', hs'', hp''⟩ | ⟨h, -⟩
      · exact ⟨c'', hs'', hp''.mono (hback H' z (fun a b h e => (hH'adj a b).2 ⟨h, e⟩) hwz)⟩
      · exact absurd h hH'wz
  · push Not at hz
    have hmiss : ∀ v, (v = y ∨ (H.Adj w v ∧ v ≠ y)) → ∃ γ, Miss H c v γ := by
      rintro v (rfl | ⟨h1, h2⟩)
      · exact exists_miss_of_degree_lt H c v hdy
      · apply exists_miss_of_degree_lt H c v
        exact (degree_le_of_sub hHG v).trans_lt (lt_of_le_of_ne (hD v) (hz v (hHG _ _ h1) h2))
    rcases fan_lemma H c hs hp hHwy hne a ha hmiss with ⟨c', hs', hp'⟩ | ⟨h, -⟩
    · exact ⟨c', hs', hp'.mono (hback H y (fun a b h e => ⟨h, fun h' => e (Set.mem_singleton_iff.1 ((fromEdgeSet_adj _).1 h').1)⟩) hwy)⟩
    · exact absurd h hHwy

end OMA.H1
-- ===== LemmasSeq.lean =====
-- depends on LemmasPivot.lean; assembled by build_all.sh
/-
* `colorable_of_independent_core` : all degrees `≤ D`, no two vertices of degree `D` adjacent
  ⇒ `D`-edge-colourable (the special case of Fournier's theorem used in CH Theorem 4/5).
* `colorable_addList` : adding edges one at a time, each with a pivot having at most one
  neighbour of degree `D` in the current graph (CH Theorem 4/5 proof scheme).
-/
namespace OMA.H1

open SimpleGraph

/-- degree with the classical instance -/
noncomputable def deg {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  by classical exact G.degree v

lemma deg_eq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    deg G v = G.degree v := by
  unfold deg; congr; exact Subsingleton.elim _ _

theorem colorable_of_independent_core {V : Type*} [Fintype V] [DecidableEq V] {D : ℕ} (hD0 : 0 < D) :
    ∀ (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card = n →
      (∀ v, G.degree v ≤ D) → (∀ a b, G.Adj a b → G.degree a = D → G.degree b = D → False) →
      Colorable D G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ hn hD hind
  classical
  by_cases hE : ∃ a b, G.Adj a b
  · -- choose an edge at a vertex of degree D if possible
    obtain ⟨a, b, hab, hpiv⟩ : ∃ a b, G.Adj a b ∧
        ∀ x, G.Adj a x → G.degree x = D → False := by
      by_cases hM : ∃ a b, G.Adj a b ∧ G.degree a = D
      · obtain ⟨a, b, hab, ha⟩ := hM
        exact ⟨a, b, hab, fun x hx hxD => hind a x hx ha hxD⟩
      · push Not at hM
        obtain ⟨a, b, hab⟩ := hE
        exact ⟨a, b, hab, fun x hx hxD => hM x a hx.symm hxD⟩
    let G' := G.deleteEdges {s(a, b)}
    have hG'G : ∀ p q, G'.Adj p q → G.Adj p q := fun p q h => h.1
    have hlt : G'.edgeFinset.card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun e he => ?_, fun h => ?_⟩
      · rw [mem_edgeFinset] at he ⊢
        exact edgeSet_mono (deleteEdges_le _) he
      · have : s(a, b) ∈ G'.edgeFinset := h (by rw [mem_edgeFinset]; exact hab)
        rw [mem_edgeFinset] at this
        simp [G'] at this
    have hdeg : ∀ v, G'.degree v ≤ G.degree v := degree_le_of_sub hG'G
    have hC : Colorable D G' := ih _ hlt G' rfl (fun v => (hdeg v).trans (hD v))
      (fun p q h hp hq => hind p q (hG'G p q h) (le_antisymm (hD p) (hp ▸ hdeg p))
        (le_antisymm (hD q) (hq ▸ hdeg q)))
    exact colorable_of_pivot G hD hab (fun x y hx _ hxD _ => (hpiv x hx hxD).elim) hC
  · push Not at hE
    exact ⟨fun _ _ => ⟨0, hD0⟩, fun _ _ => rfl, fun v a _ h => absurd h (hE v a)⟩

/-- add a list of edges (pivot, other end) -/
def addList {V : Type*} (Y : SimpleGraph V) : List (V × V) → SimpleGraph V
  | [] => Y
  | e :: L => addList (Y ⊔ edge e.1 e.2) L

/-- each added edge has a pivot with at most one neighbour of degree `D` in the current graph -/
def ValidSeq {V : Type*} [Fintype V] (D : ℕ) : SimpleGraph V → List (V × V) → Prop
  | _, [] => True
  | Y, e :: L => e.1 ≠ e.2 ∧
      (∀ a b, (Y ⊔ edge e.1 e.2).Adj e.1 a → (Y ⊔ edge e.1 e.2).Adj e.1 b →
        deg (Y ⊔ edge e.1 e.2) a = D → deg (Y ⊔ edge e.1 e.2) b = D → a = b) ∧
      ValidSeq D (Y ⊔ edge e.1 e.2) L

lemma le_addList {V : Type*} (Y : SimpleGraph V) (L : List (V × V)) :
    ∀ a b, Y.Adj a b → (addList Y L).Adj a b := by
  induction L generalizing Y with
  | nil => intro a b h; exact h
  | cons e L ih => intro a b h; exact ih _ a b (Or.inl h)

theorem colorable_addList {V : Type*} [Fintype V] [DecidableEq V] (D : ℕ) (L : List (V × V)) :
    ∀ Y : SimpleGraph V, Colorable D Y → (∀ v, deg (addList Y L) v ≤ D) → ValidSeq D Y L →
      Colorable D (addList Y L) := by
  classical
  induction L with
  | nil => intro Y hY _ _; exact hY
  | cons e L ih =>
    intro Y hY hD hV
    obtain ⟨hne, hpiv, hV'⟩ := hV
    apply ih _ _ hD hV'
    -- colour the new edge with the fan lemma
    let Y' := Y ⊔ edge e.1 e.2
    have hle : ∀ a b, Y'.Adj a b → (addList Y' L).Adj a b := le_addList Y' L
    have hdY' : ∀ v, Y'.degree v ≤ D := fun v => by
      have := hD v
      rw [deg_eq] at this
      exact (degree_le_of_sub hle v).trans this
    have hadj : Y'.Adj e.1 e.2 := Or.inr (by rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
    refine colorable_of_pivot Y' hdY' hadj (fun a b ha hb hda hdb => hpiv a b ha hb
      (by rw [deg_eq]; exact hda) (by rw [deg_eq]; exact hdb)) (hY.mono ?_)
    intro a b h
    have h1 := h.1
    have h2 := h.2
    rcases h1 with h1 | h1
    · exact h1
    · exfalso; apply h2
      rw [fromEdgeSet_adj, Set.mem_singleton_iff]
      rw [edge_adj] at h1
      refine ⟨?_, h1.2⟩
      rcases h1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

end OMA.H1

namespace OMA.H1

open SimpleGraph

/-- adding a matching as a new colour class -/
theorem colorable_succ_of_matching {V : Type*} {D : ℕ} {Z M : SimpleGraph V} (hZ : Colorable D Z)
    (hM : ∀ v u u', M.Adj v u → M.Adj v u' → u = u') : Colorable (D + 1) (Z ⊔ M) := by
  classical
  obtain ⟨c, hs, hp⟩ := hZ
  refine ⟨fun a b => if M.Adj a b then Fin.last D else (c a b).castSucc, fun a b => ?_, ?_⟩
  · by_cases h : M.Adj a b
    · simp [h, h.symm]
    · have h' : ¬ M.Adj b a := fun h' => h h'.symm
      simp [h, h', hs a b]
  · intro v a b ha hb e
    by_cases ma : M.Adj v a <;> by_cases mb : M.Adj v b
    · exact hM v a b ma mb
    · simp only [ma, mb, if_true, if_false] at e
      exact absurd e.symm (Fin.castSucc_lt_last _).ne
    · simp only [ma, mb, if_true, if_false] at e
      exact absurd e (Fin.castSucc_lt_last _).ne
    · simp only [ma, mb, if_false, Fin.castSucc_inj] at e
      have ha' : Z.Adj v a := (sup_adj _ _ _ _).1 ha |>.resolve_right ma
      have hb' : Z.Adj v b := (sup_adj _ _ _ _).1 hb |>.resolve_right mb
      exact hp v a b ha' hb' e

end OMA.H1
-- ===== LemmasMatchings.lean =====
-- standalone (Mathlib only); assembled by build_all.sh
/-
PLAN.md item D1: the Chetwynd–Hilton matchings in index form.
A-vertices are `a ∈ [1, m+1]` (`l_a`, with `l_{m+1} = v*`), B-vertices are `j ∈ [t, m]` (`r_j`).
Matching `i` (`1 ≤ i ≤ q`, `σ = i + t`) consists of the pairs `l_a l_b` with `a + b = σ` and the
pairs `l_a r_j` with `a - j = i`.
-/
namespace OMA.H1

/-- `l_a l_b` (a < b) lies in matching `i` -/
def AAin (t m i a b : ℤ) : Prop := 1 ≤ a ∧ a < b ∧ b ≤ m + 1 ∧ a + b = i + t

/-- `l_a r_j` lies in matching `i` -/
def ABin (t m i a j : ℤ) : Prop := t ≤ j ∧ j ≤ m ∧ 1 ≤ a ∧ a ≤ m + 1 ∧ a - j = i

/-- at an A-vertex the three kinds of partner exclude each other and are unique -/
lemma AA_AB_excl {t m i a b j : ℤ} (_hi : 1 ≤ i) (h1 : AAin t m i a b ∨ AAin t m i b a)
    (h2 : ABin t m i a j) : False := by
  unfold AAin ABin at *; omega

lemma AA_unique {t m i a b b' : ℤ} (h : AAin t m i a b ∨ AAin t m i b a)
    (h' : AAin t m i a b' ∨ AAin t m i b' a) : b = b' := by
  unfold AAin at *; omega

lemma AB_unique_left {t m i a j j' : ℤ} (h : ABin t m i a j) (h' : ABin t m i a j') : j = j' := by
  unfold ABin at *; omega

lemma AB_unique_right {t m i a a' j : ℤ} (h : ABin t m i a j) (h' : ABin t m i a' j) : a = a' := by
  unfold ABin at *; omega

/-- coverage of A–A pairs -/
lemma AA_cover {t m a b : ℤ} (ht : t ≤ 1) (hab : 1 ≤ a ∧ a < b ∧ b ≤ m + 1) :
    ∃ i, 1 ≤ i ∧ i ≤ 2 * m - t + 1 ∧ AAin t m i a b :=
  ⟨a + b - t, by omega, by omega, by unfold AAin; omega⟩

/-- coverage of A–B pairs `l_a r_j` with `a > j` -/
lemma AB_cover {t m a j : ℤ} (hm : 0 ≤ m) (h : t ≤ j ∧ j < a ∧ j ≤ m ∧ 1 ≤ a ∧ a ≤ m + 1) :
    ∃ i, 1 ≤ i ∧ i ≤ 2 * m - t + 1 ∧ ABin t m i a j :=
  ⟨a - j, by omega, by omega, by unfold ABin; omega⟩

open Finset Classical in
/-- vertex count of matching `i` is at most `q + 2 - i = 2m + 3 - (i + t)` -/
lemma matching_vertex_count (t m i : ℤ) (ht : t ≤ 1) (hm : 0 ≤ m) (hi : 1 ≤ i)
    (hiq : i ≤ 2 * m - t + 1) :
    (((Icc 1 (m + 1)).filter (fun a => ∃ b, AAin t m i a b ∨ AAin t m i b a)).card : ℤ) +
      2 * ((Icc 1 (m + 1)).filter (fun a => ∃ j, ABin t m i a j)).card ≤ 2 * m + 3 - (i + t) := by
  set σ := i + t with hσ
  have hAA : (Icc 1 (m + 1)).filter (fun a => ∃ b, AAin t m i a b ∨ AAin t m i b a) ⊆
      Icc (max 1 (σ - m - 1)) (min (m + 1) (σ - 1)) := by
    intro a ha
    simp only [mem_filter, mem_Icc] at ha ⊢
    obtain ⟨⟨h1, h2⟩, b, hb⟩ := ha
    unfold AAin at hb
    omega
  have hAB : (Icc 1 (m + 1)).filter (fun a => ∃ j, ABin t m i a j) ⊆ Icc (max 1 σ) (m + 1) := by
    intro a ha
    simp only [mem_filter, mem_Icc] at ha ⊢
    obtain ⟨⟨h1, h2⟩, j, hj⟩ := ha
    unfold ABin at hj
    omega
  have c1 := card_le_card hAA
  have c2 := card_le_card hAB
  rw [Int.card_Icc] at c1 c2
  have e1 : ((min (m + 1) (σ - 1) + 1 - max 1 (σ - m - 1)).toNat : ℤ) =
      max 0 (min (m + 1) (σ - 1) + 1 - max 1 (σ - m - 1)) := by
    rw [Int.toNat_eq_max]; omega
  have e2 : ((m + 1 + 1 - max 1 σ).toNat : ℤ) = max 0 (m + 1 + 1 - max 1 σ) := by
    rw [Int.toNat_eq_max]; omega
  have c1' : (((Icc 1 (m + 1)).filter (fun a => ∃ b, AAin t m i a b ∨ AAin t m i b a)).card : ℤ) ≤
      max 0 (min (m + 1) (σ - 1) + 1 - max 1 (σ - m - 1)) := by rw [← e1]; exact_mod_cast c1
  have c2' : (((Icc 1 (m + 1)).filter (fun a => ∃ j, ABin t m i a j)).card : ℤ) ≤
      max 0 (m + 1 + 1 - max 1 σ) := by rw [← e2]; exact_mod_cast c2
  omega

end OMA.H1
-- ===== LemmasStep.lean =====
-- depends on LemmasPivot.lean, LemmasSeq.lean; assembled by build_all.sh
/-
`colorable_of_steps`: an invariant-driven version of `colorable_addList`.  If from every graph `H`
satisfying `Inv` (and `≠ Yb`) one can add a missing edge of `Yb` whose pivot has at most one
neighbour of degree `D`, keeping `Inv`, then a `D`-colouring of an `Inv` graph extends to `Yb`.
-/
namespace OMA.H1

open SimpleGraph

lemma deg_le_of_le {V : Type*} [Fintype V] {G G' : SimpleGraph V} (hle : G' ≤ G) (v : V) :
    deg G' v ≤ deg G v := by
  classical
  rw [deg_eq, deg_eq]; exact degree_le_of_sub (fun a b h => hle h) v

/-- a vertex of full degree `D` in `H ≤ Y` (with `deg Y ≤ D`) has all its `Y`-edges in `H` -/
lemma adj_of_deg_full {V : Type*} [Fintype V] {H Y : SimpleGraph V} (hle : H ≤ Y) {D : ℕ} {b : V}
    (hY : deg Y b ≤ D) (hH : deg H b = D) {c : V} (hc : Y.Adj b c) : H.Adj b c := by
  classical
  by_contra h
  have := degree_lt_of_sub (G := Y) (G' := H) (fun a b h => hle h) hc h
  rw [deg_eq] at hY hH; omega

lemma deg_lt_of_missing {V : Type*} [Fintype V] {H Y : SimpleGraph V} (hle : H ≤ Y) {D : ℕ} {b c : V}
    (hY : deg Y b ≤ D) (hc : Y.Adj b c) (h : ¬ H.Adj b c) : deg H b ≠ D :=
  fun hH => h (adj_of_deg_full hle hY hH hc)

theorem colorable_of_steps {V : Type*} [Fintype V] [DecidableEq V] (D : ℕ) (Yb : SimpleGraph V)
    (hD : ∀ v, deg Yb v ≤ D) (Inv : SimpleGraph V → Prop) (hle : ∀ H, Inv H → H ≤ Yb)
    (step : ∀ H, Inv H → H ≠ Yb → ∃ p y, Yb.Adj p y ∧ ¬ H.Adj p y ∧ Inv (H ⊔ edge p y) ∧
      ∀ a b, (H ⊔ edge p y).Adj p a → (H ⊔ edge p y).Adj p b → deg (H ⊔ edge p y) a = D →
        deg (H ⊔ edge p y) b = D → a = b) :
    ∀ H, Inv H → Colorable D H → Colorable D Yb := by
  classical
  let μ : SimpleGraph V → ℕ := fun H =>
    ((Finset.univ : Finset (Sym2 V)).filter (fun e => e ∈ Yb.edgeSet ∧ e ∉ H.edgeSet)).card
  suffices ∀ n, ∀ H, μ H = n → Inv H → Colorable D H → Colorable D Yb from
    fun H hI hC => this _ H rfl hI hC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hI hC
  by_cases hEq : H = Yb
  · exact hEq ▸ hC
  obtain ⟨p, y, hpy, hnot, hI', hpiv⟩ := step H hI hEq
  have hne : p ≠ y := hpy.ne
  set H' := H ⊔ edge p y
  have hadj : H'.Adj p y := Or.inr (by rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have hdH' : ∀ v, H'.degree v ≤ D := fun v => by
    have := (deg_le_of_le (hle _ hI') v).trans (hD v); rw [deg_eq] at this; exact this
  have hC' : Colorable D H' := by
    refine colorable_of_pivot H' hdH' hadj (fun a b ha hb hda hdb => hpiv a b ha hb
      (by rw [deg_eq]; exact hda) (by rw [deg_eq]; exact hdb)) (hC.mono ?_)
    intro a b h
    rcases h.1 with h1 | h1
    · exact h1
    · exfalso; apply h.2
      rw [fromEdgeSet_adj, Set.mem_singleton_iff]
      rw [edge_adj] at h1
      refine ⟨?_, h1.2⟩
      rcases h1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  refine ih (μ H') ?_ H' rfl hI' hC'
  rw [← hn]
  apply Finset.card_lt_card
  refine ⟨fun e he => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨he.1, fun h => he.2 (by
      induction e using Sym2.ind with
      | _ a b => exact Or.inl h)⟩
  · have hm : s(p, y) ∈ (Finset.univ : Finset (Sym2 V)).filter
        (fun e => e ∈ Yb.edgeSet ∧ e ∉ H.edgeSet) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_edgeSet]; exact ⟨hpy, hnot⟩
    have := hsub hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_edgeSet] at this
    exact this.2 hadj

end OMA.H1
-- ===== LemmasCore.lean =====
-- depends on LemmasStep.lean, LemmasSeq.lean; assembled by build_all.sh
/-
`colorable_core`: colouring the final graph `Y` of the CH argument.  The vertices of degree `D` lie in
a "core" `C` carrying positions `1..q` (`q = 2m+u`); core edges have position sum `≤ q+1`; the pairs
`(i, q+1-i)`, `i ≤ m`, are edges ("tree edges"); the middle positions `m+1..m+u` are independent.
Proof: Fournier for `Y` minus core edges, then add core edges in rank order (non-tree non-middle,
then middle, then tree edges from the middle outwards), each with a pivot of at most one full neighbour.
-/
namespace OMA.H1

open SimpleGraph

/-- rank of a core pair, from the positions -/
def rkP (m u i j : ℕ) : ℕ :=
  if i + j = 2 * m + u + 1 then 1 + (m + 1 - min i j)
  else if (m < i ∧ i ≤ m + u) ∨ (m < j ∧ j ≤ m + u) then 1 else 0

lemma rkP_comm (m u i j : ℕ) : rkP m u i j = rkP m u j i := by
  unfold rkP; rw [add_comm i j, min_comm]; by_cases h : j + i = 2 * m + u + 1 <;> simp [h, or_comm]

theorem colorable_core {V : Type*} [Fintype V] [DecidableEq V] (D : ℕ) (hD0 : 0 < D)
    (Y : SimpleGraph V) (hY : ∀ v, deg Y v ≤ D) (C : Finset V) (π : V → ℕ) (m u : ℕ)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b)
    (hrange : ∀ a ∈ C, 1 ≤ π a ∧ π a ≤ 2 * m + u)
    (hsurj : ∀ i, 1 ≤ i → i ≤ 2 * m + u → ∃ c ∈ C, π c = i)
    (hnc : ∀ v, v ∉ C → deg Y v < D)
    (hsum : ∀ a ∈ C, ∀ b ∈ C, Y.Adj a b → π a + π b ≤ 2 * m + u + 1)
    (htree : ∀ a ∈ C, ∀ b ∈ C, π a + π b = 2 * m + u + 1 → π a ≤ m → Y.Adj a b)
    (hU : ∀ a ∈ C, ∀ b ∈ C, m < π a → π a ≤ m + u → m < π b → π b ≤ m + u → ¬ Y.Adj a b) :
    Colorable D Y := by
  classical
  set q := 2 * m + u with hq
  let rk : V → V → ℕ := fun a b => rkP m u (π a) (π b)
  have rk_comm : ∀ a b, rk a b = rk b a := fun a b => rkP_comm _ _ _ _
  -- Y minus core edges
  let Y0 : SimpleGraph V :=
    { Adj := fun a b => Y.Adj a b ∧ ¬ (a ∈ C ∧ b ∈ C)
      symm := ⟨fun a b h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2, h'.1⟩⟩⟩
      loopless := ⟨fun a h => h.1.ne rfl⟩ }
  have hY0le : Y0 ≤ Y := fun a b h => h.1
  have hC0 : Colorable D Y0 := by
    refine colorable_of_independent_core hD0 _ Y0 rfl (fun v => ?_) (fun a b hab ha hb => ?_)
    · have := (deg_le_of_le hY0le v).trans (hY v); rw [deg_eq] at this; exact this
    · have ha' : a ∈ C := by
        by_contra h; have := hnc a h; have := deg_le_of_le hY0le a; rw [deg_eq Y0] at this; omega
      have hb' : b ∈ C := by
        by_contra h; have := hnc b h; have := deg_le_of_le hY0le b; rw [deg_eq Y0] at this; omega
      exact hab.2 ⟨ha', hb'⟩
  -- the invariant
  let Inv : SimpleGraph V → Prop := fun H => Y0 ≤ H ∧ H ≤ Y ∧
    ∀ a b c d, a ∈ C → b ∈ C → c ∈ C → d ∈ C → H.Adj a b → Y.Adj c d → rk c d < rk a b → H.Adj c d
  -- tree partner facts
  have tree_rank : ∀ a ∈ C, ∀ b ∈ C, Y.Adj a b → π a + π b = q + 1 →
      min (π a) (π b) ≤ m ∧ rk a b = 1 + (m + 1 - min (π a) (π b)) := by
    intro a ha b hb hab hs
    have hmin : min (π a) (π b) ≤ m := by
      by_contra hcon
      have h1 := hrange a ha; have h2 := hrange b hb
      exact hU a ha b hb (by omega) (by omega) (by omega) (by omega) hab
    refine ⟨hmin, ?_⟩
    show rkP m u (π a) (π b) = _
    unfold rkP; rw [if_pos hs]
  -- every non-middle core vertex has a tree edge
  have has_tree : ∀ a ∈ C, ¬ (m < π a ∧ π a ≤ m + u) → ∃ b ∈ C, Y.Adj a b ∧ π a + π b = q + 1 ∧
      rk a b = 1 + (m + 1 - min (π a) (π b)) := by
    intro a ha hna
    have h1 := hrange a ha
    obtain ⟨b, hb, hbp⟩ := hsurj (q + 1 - π a) (by omega) (by omega)
    have hs : π a + π b = q + 1 := by omega
    have hab : Y.Adj a b := by
      by_cases hle : π a ≤ m
      · exact htree a ha b hb hs hle
      · exact (htree b hb a ha (by omega) (by omega)).symm
    exact ⟨b, hb, hab, hs, (tree_rank a ha b hb hab hs).2⟩
  refine colorable_of_steps D Y hY Inv (fun H h => h.2.1) (fun H hI hne => ?_) Y0
    ⟨le_rfl, hY0le, fun a b c d ha hb _ _ h => absurd ⟨ha, hb⟩ h.2⟩ hC0
  obtain ⟨hY0H, hHY, hcl⟩ := hI
  have hex : ∃ r, ∃ c d, c ∈ C ∧ d ∈ C ∧ Y.Adj c d ∧ ¬ H.Adj c d ∧ rk c d = r := by
    by_contra hcon
    push Not at hcon
    apply hne; ext a b; constructor
    · exact fun h => hHY h
    · intro h; by_contra h'
      by_cases hab : a ∈ C ∧ b ∈ C
      · exact hcon _ a b hab.1 hab.2 h h' rfl
      · exact h' (hY0H ⟨h, hab⟩)
  set ρ := Nat.find hex with hρ
  obtain ⟨c, d, hc, hd, hcd, hncd, hrk⟩ := Nat.find_spec hex
  have habove : ∀ a b, a ∈ C → b ∈ C → H.Adj a b → rk a b ≤ ρ := by
    intro a b ha hb hab; by_contra h; push Not at h
    exact hncd (hcl a b c d ha hb hc hd hab hcd (by rw [hrk]; exact h))
  have hminr : ∀ a b, a ∈ C → b ∈ C → Y.Adj a b → rk a b < ρ → H.Adj a b := by
    intro a b ha hb hab hlt; by_contra h
    exact Nat.find_min hex hlt ⟨a, b, ha, hb, hab, h, rfl⟩
  have key : ∀ p y, ((p = c ∧ y = d) ∨ (p = d ∧ y = c)) →
      (∀ a, a ∈ C → Y.Adj p a → rk p a ≤ ρ → a ≠ y → ∃ e, Y.Adj a e ∧ ¬ (H ⊔ edge p y).Adj a e) →
      ∃ p y, Y.Adj p y ∧ ¬ H.Adj p y ∧ Inv (H ⊔ edge p y) ∧
        ∀ a b, (H ⊔ edge p y).Adj p a → (H ⊔ edge p y).Adj p b → deg (H ⊔ edge p y) a = D →
          deg (H ⊔ edge p y) b = D → a = b := by
    intro p y hpy hcond
    have hpC : p ∈ C := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hyC : y ∈ C := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hYpy : Y.Adj p y := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hcd; exact hcd.symm
    have hHpy : ¬ H.Adj p y := by
      rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hncd; exact fun h => hncd h.symm
    have hrkpy : rk p y = ρ := by
      rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hrk; rw [rk_comm]; exact hrk
    have hle' : H ⊔ edge p y ≤ Y := by
      intro a b h
      rcases h with h | h
      · exact hHY h
      · rw [edge_adj] at h
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hYpy
        · exact hYpy.symm
    have hfull : ∀ a, (H ⊔ edge p y).Adj p a → deg (H ⊔ edge p y) a = D → a = y := by
      intro a ha hda
      by_contra hay
      have haC : a ∈ C := by
        by_contra h; have := hnc a h; have := deg_le_of_le hle' a; omega
      have hYa : Y.Adj p a := hle' ha
      have hrka : rk p a ≤ ρ := by
        rcases ha with ha | ha
        · exact habove p a hpC haC ha
        · rw [edge_adj] at ha
          rcases ha.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first | exact absurd h1 hay | exact absurd h1.symm hay | exact absurd h2 hay | exact absurd h2.symm hay | exact absurd h1 ha.2 | exact absurd h1.symm ha.2 | exact absurd h2 ha.2 | exact absurd h2.symm ha.2
      obtain ⟨e, hYe, hne'⟩ := hcond a haC hYa hrka hay
      exact deg_lt_of_missing hle' (hY a) hYe hne' hda
    refine ⟨p, y, hYpy, hHpy, ⟨le_trans hY0H le_sup_left, hle', ?_⟩, ?_⟩
    · intro a b c' d' ha hb hc' hd' hab hcd' hlt
      rcases hab with hab | hab
      · exact Or.inl (hcl a b c' d' ha hb hc' hd' hab hcd' hlt)
      · rw [edge_adj] at hab
        have : rk a b = ρ := by
          rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hrkpy
          · rw [rk_comm]; exact hrkpy
        exact Or.inl (hminr c' d' hc' hd' hcd' (this ▸ hlt))
    · intro a b ha hb hda hdb
      rw [hfull a ha hda, hfull b hb hdb]
  -- a vertex with a missing tree edge
  have hmiss : ∀ p y a, a ∈ C → ¬ (m < π a ∧ π a ≤ m + u) → a ≠ p → a ≠ y →
      (∀ b ∈ C, π a + π b = q + 1 → ρ < rk a b) → ∃ e, Y.Adj a e ∧ ¬ (H ⊔ edge p y).Adj a e := by
    intro p y a ha hna hap hay hr
    obtain ⟨b, hb, hab, hs, -⟩ := has_tree a ha hna
    refine ⟨b, hab, fun h => ?_⟩
    rcases h with h | h
    · exact absurd (habove a b ha hb h) (not_le.2 (hr b hb hs))
    · rw [edge_adj] at h
      rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> first | exact absurd h1 hap | exact absurd h1.symm hap | exact absurd h2 hap | exact absurd h2.symm hap | exact absurd h1 hay | exact absurd h1.symm hay | exact absurd h2 hay | exact absurd h2.symm hay
  have hrc := hrange c hc
  have hrd := hrange d hd
  by_cases hs : π c + π d = q + 1
  · -- tree edge: pivot = endpoint with larger position
    have hρ' : ρ = 1 + (m + 1 - min (π c) (π d)) := by exact hrk.symm.trans (tree_rank c hc d hd hcd hs).2
    have hmn := (tree_rank c hc d hd hcd hs).1
    have main : ∀ p y, ((p = c ∧ y = d) ∨ (p = d ∧ y = c)) → π y ≤ π p → ∀ a, a ∈ C → Y.Adj p a →
        rk p a ≤ ρ → a ≠ y → ∃ e, Y.Adj a e ∧ ¬ (H ⊔ edge p y).Adj a e := by
      intro p y hpy hyp a ha hpa _ hay
      have hpC : p ∈ C := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hyC : y ∈ C := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hspy : π p + π y = q + 1 := by
        rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      have hminy : min (π c) (π d) = π y := by
        rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      have h1 := hsum p hpC a ha hpa
      have hne : π a ≠ π y := fun h => hay (hinj a ha y hyC h)
      have hra := hrange a ha
      refine hmiss p y a ha (by omega) (fun h => hpa.ne h.symm) hay (fun b hb hab => ?_)
      show ρ < rkP m u (π a) (π b)
      unfold rkP; rw [if_pos hab, hρ', hminy]; omega
    by_cases hdc : π d ≤ π c
    · exact key c d (Or.inl ⟨rfl, rfl⟩) (main c d (Or.inl ⟨rfl, rfl⟩) hdc)
    · exact key d c (Or.inr ⟨rfl, rfl⟩) (main d c (Or.inr ⟨rfl, rfl⟩) (by omega))
  have htreerk : ∀ a b, a ∈ C → ¬ (m < π a ∧ π a ≤ m + u) → π a + π b = q + 1 → 2 ≤ rk a b := by
    intro a b ha hna hab
    have := hrange a ha
    show 2 ≤ rkP m u (π a) (π b)
    unfold rkP; rw [if_pos hab]; omega
  have hmidrk : ∀ a b, (m < π b ∧ π b ≤ m + u) → 1 ≤ rk a b := by
    intro a b hb
    show 1 ≤ rkP m u (π a) (π b)
    unfold rkP; split_ifs <;> omega
  by_cases hm : (m < π c ∧ π c ≤ m + u) ∨ (m < π d ∧ π d ≤ m + u)
  · have hρ1 : ρ = 1 := by
      exact hrk.symm.trans (by show rkP m u (π c) (π d) = 1; unfold rkP; rw [if_neg hs, if_pos hm])
    have mid : ∀ p y, ((p = c ∧ y = d) ∨ (p = d ∧ y = c)) → (m < π p ∧ π p ≤ m + u) →
        ∀ a, a ∈ C → Y.Adj p a → rk p a ≤ ρ → a ≠ y → ∃ e, Y.Adj a e ∧ ¬ (H ⊔ edge p y).Adj a e := by
      intro p y hpy hp a ha hpa _ hay
      have hpC : p ∈ C := by rcases hpy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
      have hna : ¬ (m < π a ∧ π a ≤ m + u) := fun h => hU p hpC a ha hp.1 hp.2 h.1 h.2 hpa
      exact hmiss p y a ha hna (fun h => hpa.ne h.symm) hay
        (fun b _ hab => by have := htreerk a b ha hna hab; omega)
    rcases hm with hm | hm
    · exact key c d (Or.inl ⟨rfl, rfl⟩) (mid c d (Or.inl ⟨rfl, rfl⟩) hm)
    · exact key d c (Or.inr ⟨rfl, rfl⟩) (mid d c (Or.inr ⟨rfl, rfl⟩) hm)
  · have hρ0 : ρ = 0 := by
      exact hrk.symm.trans (by show rkP m u (π c) (π d) = 0; unfold rkP; rw [if_neg hs, if_neg hm])
    refine key c d (Or.inl ⟨rfl, rfl⟩) (fun a ha hca hrka hay => ?_)
    have hna : ¬ (m < π a ∧ π a ≤ m + u) := fun h => by have := hmidrk c a h; omega
    exact hmiss c d a ha hna (fun h => hca.ne h.symm) hay
      (fun b _ hab => by have := htreerk a b ha hna hab; omega)

end OMA.H1
-- ===== LemmasDeg.lean =====
-- depends on LemmasSeq.lean (deg), LemmasExtend.lean (EDisj); assembled by build_all.sh
namespace OMA.H1

open SimpleGraph

/-- removing edge-disjoint subgraphs, `|S|` of which meet `v`, lowers the degree of `v` by `|S|` -/
theorem deg_remove_bound {V : Type*} [Fintype V] [DecidableEq V] (X Z : SimpleGraph V)
    (F : ℕ → SimpleGraph V) (S : Finset ℕ)
    (hZ : ∀ a b, Z.Adj a b → X.Adj a b ∧ ∀ k ∈ S, ¬ (F k).Adj a b) (hF : ∀ k ∈ S, F k ≤ X)
    (hdisj : ∀ k ∈ S, ∀ j ∈ S, k ≠ j → EDisj (F k) (F j)) (v : V)
    (hcov : ∀ k ∈ S, ∃ u, (F k).Adj v u) : deg Z v + S.card ≤ deg X v := by
  classical
  let f : ℕ → V := fun k => if h : k ∈ S then (hcov k h).choose else v
  have hf : ∀ k ∈ S, (F k).Adj v (f k) := by
    intro k hk; simp only [f, dif_pos hk]; exact (hcov k hk).choose_spec
  have hinj : Set.InjOn f S := by
    intro k hk j hj h
    by_contra hne
    exact hdisj k hk j hj hne v (f k) (hf k hk) (h ▸ hf j hj)
  rw [deg_eq, deg_eq, ← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro u hu
    rw [Finset.mem_union, mem_neighborFinset, Finset.mem_image] at hu
    rw [mem_neighborFinset]
    rcases hu with hu | ⟨k, hk, rfl⟩
    · exact (hZ _ _ hu).1
    · exact hF k hk (hf k hk)
  · rw [Finset.disjoint_left]
    intro u hu hu'
    rw [mem_neighborFinset] at hu
    rw [Finset.mem_image] at hu'
    obtain ⟨k, hk, rfl⟩ := hu'
    exact (hZ _ _ hu).2 k hk (hf k hk)

end OMA.H1

namespace OMA.H1

open SimpleGraph

/-- the degree bound in the form used for `Y` and `Q` -/
theorem deg_bound_xi {V : Type*} [Fintype V] [DecidableEq V] (X Z : SimpleGraph V)
    (F : ℕ → SimpleGraph V) (ξ : ℕ → V) (S : Finset ℕ) (d : ℕ)
    (hZ : ∀ a b, Z.Adj a b → X.Adj a b ∧ ∀ k ∈ S, ¬ (F k).Adj a b) (hF : ∀ k ∈ S, F k ≤ X)
    (hdisj : ∀ k ∈ S, ∀ j ∈ S, k ≠ j → EDisj (F k) (F j))
    (hcov : ∀ k ∈ S, ∀ v, v ≠ ξ k → ∃ u, (F k).Adj v u) (v : V)
    (hle1 : ∀ i ∈ S, ∀ j ∈ S, ξ i = v → ξ j = v → i = j)
    (hdv : (∃ i ∈ S, ξ i = v) → deg X v + 1 ≤ d) (hd : deg X v ≤ d) : deg Z v + S.card ≤ d := by
  classical
  have h := deg_remove_bound X Z F (S.filter (fun i => ξ i ≠ v))
    (fun a b hab => ⟨(hZ a b hab).1, fun k hk => (hZ a b hab).2 k (Finset.mem_filter.1 hk).1⟩)
    (fun k hk => hF k (Finset.mem_filter.1 hk).1)
    (fun k hk j hj => hdisj k (Finset.mem_filter.1 hk).1 j (Finset.mem_filter.1 hj).1) v
    (fun k hk => hcov k (Finset.mem_filter.1 hk).1 v (Finset.mem_filter.1 hk).2.symm)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun i => ξ i ≠ v)
  have hone : (S.filter (fun i => ¬ ξ i ≠ v)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro i hi j hj
    simp only [Finset.mem_filter, not_not] at hi hj
    exact hle1 i hi.1 j hj.1 hi.2 hj.2
  by_cases hex : ∃ i ∈ S, ξ i = v
  · have := hdv hex; omega
  · push Not at hex
    have : (S.filter (fun i => ¬ ξ i ≠ v)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi; simp only [not_not]; exact hex i hi
    omega

end OMA.H1
-- ===== LemmasPos.lean =====
-- self-contained; assembled by build_all.sh
/-
Positions for the core: a maximal matching laid out as pairs `(i, q+1-i)`, `i ≤ m`, around a middle
block `m+1..m+u` of pairwise non-adjacent vertices; left ends have smaller rank `ρ`, middle sorted by `ρ`.
-/
namespace OMA.H1

open SimpleGraph

theorem exists_sorted_pos {V : Type*} [DecidableEq V] (ρ : V → ℕ) (C : Finset V) :
    ∃ π : V → ℕ, (∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b) ∧ (∀ a ∈ C, 1 ≤ π a ∧ π a ≤ C.card) ∧
      (∀ a ∈ C, ∀ b ∈ C, π a < π b → ρ a ≤ ρ b) := by
  induction C using Finset.strongInduction with
  | H C ih =>
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  obtain ⟨c, hc, hmax⟩ := C.exists_max_image ρ hne
  obtain ⟨π', hinj, hr, hs⟩ := ih (C.erase c) (Finset.erase_ssubset hc)
  have hcard : (C.erase c).card + 1 = C.card := Finset.card_erase_add_one hc
  refine ⟨fun v => if v = c then C.card else π' v, ?_, ?_, ?_⟩
  · intro a ha b hb h
    by_cases hac : a = c <;> by_cases hbc : b = c <;> simp only [hac, hbc, if_true, if_false] at h
    · rw [hac, hbc]
    · have := hr b (Finset.mem_erase.2 ⟨hbc, hb⟩); omega
    · have := hr a (Finset.mem_erase.2 ⟨hac, ha⟩); omega
    · exact hinj a (Finset.mem_erase.2 ⟨hac, ha⟩) b (Finset.mem_erase.2 ⟨hbc, hb⟩) h
  · intro a ha
    by_cases hac : a = c <;> simp only [hac, if_true, if_false]
    · have := Finset.card_pos.2 hne; omega
    · have := hr a (Finset.mem_erase.2 ⟨hac, ha⟩); omega
  · intro a ha b hb h
    by_cases hac : a = c <;> by_cases hbc : b = c <;> simp only [hac, hbc, if_true, if_false] at h
    · omega
    · have := hr b (Finset.mem_erase.2 ⟨hbc, hb⟩); omega
    · rw [hbc]; exact hmax a ha
    · exact hs a (Finset.mem_erase.2 ⟨hac, ha⟩) b (Finset.mem_erase.2 ⟨hbc, hb⟩) h

theorem exists_positions {V : Type*} [DecidableEq V] (H : SimpleGraph V) (ρ : V → ℕ) (C : Finset V) :
    ∃ (π : V → ℕ) (m u : ℕ), 2 * m + u = C.card ∧
      (∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b) ∧
      (∀ a ∈ C, 1 ≤ π a ∧ π a ≤ 2 * m + u) ∧
      (∀ a ∈ C, ∀ b ∈ C, π a + π b = 2 * m + u + 1 → π a ≤ m → H.Adj a b ∧ ρ a ≤ ρ b) ∧
      (∀ a ∈ C, ∀ b ∈ C, m < π a → π a ≤ m + u → m < π b → π b ≤ m + u →
        ¬ H.Adj a b ∧ (π a < π b → ρ a ≤ ρ b)) := by
  induction C using Finset.strongInduction with
  | H C ih =>
  by_cases hE : ∃ a ∈ C, ∃ b ∈ C, H.Adj a b ∧ ρ a ≤ ρ b
  · obtain ⟨a, ha, b, hb, hab, hρ⟩ := hE
    have hb' : b ∈ C.erase a := Finset.mem_erase.2 ⟨hab.ne.symm, hb⟩
    obtain ⟨π', m', u', hq, hinj, hr, ht, hU⟩ :=
      ih ((C.erase a).erase b) ((Finset.erase_ssubset hb').trans (Finset.erase_ssubset ha))
    have hcard : ((C.erase a).erase b).card + 2 = C.card := by
      rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
      have : 2 ≤ C.card := by
        have := Finset.card_le_card (show ({a, b} : Finset V) ⊆ C by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
        rw [Finset.card_pair hab.ne] at this; exact this
      omega
    have mem : ∀ x ∈ C, x ≠ a → x ≠ b → x ∈ (C.erase a).erase b := fun x hx h1 h2 =>
      Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hx⟩⟩
    refine ⟨fun v => if v = a then 1 else if v = b then 2 * m' + u' + 2 else π' v + 1, m' + 1, u',
      by omega, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy h
      dsimp only at h; split_ifs at h <;>
        first
        | (subst_vars; rfl)
        | (exfalso; subst_vars; exact hab.ne rfl)
        | omega
        | (have := hr y (mem y hy (by assumption) (by assumption)); omega)
        | (have := hr x (mem x hx (by assumption) (by assumption)); omega)
        | exact hinj x (mem x hx (by assumption) (by assumption)) y (mem y hy (by assumption) (by assumption)) (by omega)
    · intro x hx
      dsimp only; split_ifs <;>
        first | omega | (have := hr x (mem x hx (by assumption) (by assumption)); omega)
    · intro x hx y hy h hle
      dsimp only at h hle; split_ifs at h hle <;>
        first
        | (subst_vars; exact ⟨hab, hρ⟩)
        | (exfalso; subst_vars; exact hab.ne rfl)
        | omega
        | (have := hr y (mem y hy (by assumption) (by assumption)); omega)
        | (have := hr x (mem x hx (by assumption) (by assumption)); omega)
        | exact ht x (mem x hx (by assumption) (by assumption)) y (mem y hy (by assumption) (by assumption)) (by omega) (by omega)
    · intro x hx y hy h1 h2 h3 h4
      dsimp only at h1 h2 h3 h4 ⊢; split_ifs at h1 h2 h3 h4 ⊢ <;>
        first
        | omega
        | (have := hU x (mem x hx (by assumption) (by assumption)) y (mem y hy (by assumption) (by assumption)) (by omega) (by omega) (by omega) (by omega)
           exact ⟨this.1, fun h => this.2 (by omega)⟩)
  · obtain ⟨π, hinj, hr, hs⟩ := exists_sorted_pos ρ C
    refine ⟨π, 0, C.card, by omega, hinj, fun a ha => by have := hr a ha; omega,
      fun a ha b hb _ hle => by have := hr a ha; omega, fun a ha b hb _ _ _ _ => ⟨fun hab => ?_, hs a ha b hb⟩⟩
    push Not at hE
    rcases le_total (ρ a) (ρ b) with h | h
    · exact absurd h (not_le.2 (hE a ha b hb hab))
    · exact absurd h (not_le.2 (hE b hb a ha hab.symm))

end OMA.H1
-- ===== LemmasAssemble.lean =====
-- depends on LemmasCore, LemmasDeg, LemmasStep, LemmasSeq; assembled by build_all.sh
/- Step 5–6 of the plan: from the factors `F i` (i < r) and the core positions, colour `X`. -/
namespace OMA.H1

open SimpleGraph

/-- union of the graphs `F i`, `i ∈ S` -/
def unionG {V : Type*} (F : ℕ → SimpleGraph V) (S : Finset ℕ) : SimpleGraph V where
  Adj a b := ∃ i ∈ S, (F i).Adj a b
  symm := ⟨fun _ _ ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, h⟩ => h.ne rfl⟩

theorem colorable_add_matchings {V : Type*} {D : ℕ} (Y : SimpleGraph V) (F : ℕ → SimpleGraph V)
    (hY : Colorable D Y) (S : Finset ℕ)
    (hM : ∀ i ∈ S, ∀ v u u', (F i).Adj v u → (F i).Adj v u' → u = u') :
    Colorable (D + S.card) (Y ⊔ unionG F S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine hY.mono (fun a b h => ?_)
    rcases h with h | ⟨i, hi, _⟩
    · exact h
    · simp at hi
  | insert i S hi ih =>
    have h1 := colorable_succ_of_matching (ih (fun j hj => hM j (Finset.mem_insert_of_mem hj)))
      (hM i (Finset.mem_insert_self i S))
    rw [Finset.card_insert_of_notMem hi, ← add_assoc]
    refine h1.mono (fun a b h => ?_)
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl (Or.inl h)
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨j, hj, h⟩)

lemma deg_zero_of_noAdj {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) (h : ∀ w, ¬ G.Adj v w) :
    deg G v = 0 := by
  classical
  rw [deg_eq, ← card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw; rw [mem_neighborFinset] at hw; exact h w hw

end OMA.H1

namespace OMA.H1

open SimpleGraph

theorem colorable_assemble {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V) (d r : ℕ)
    (vs : V) (F : ℕ → SimpleGraph V) (ξ : ℕ → V) (C : Finset V) (π : V → ℕ) (m u : ℕ)
    (hrd : r < d)
    (hF : ∀ i < r, F i ≤ X)
    (hcov : ∀ i < r, ∀ v, v ≠ ξ i → ∃ w, (F i).Adj v w)
    (hmiss : ∀ i < r, ∀ w, ¬ (F i).Adj (ξ i) w)
    (hmat : ∀ i < r, ∀ v w w', (F i).Adj v w → (F i).Adj v w' → w = w')
    (hdisj : ∀ i < r, ∀ j < r, i ≠ j → EDisj (F i) (F j))
    (hξinj : ∀ i < r, ∀ j < r, ξ i ≠ vs → ξ i = ξ j → i = j)
    (hdeg : ∀ v, deg X v ≤ d)
    (hξdeg : ∀ i < r, ξ i ≠ vs → deg X (ξ i) + 1 ≤ d ∧ ξ i ∈ C ∧ ¬ X.Adj vs (ξ i))
    (hnc : ∀ v, v ≠ vs → v ∉ C → deg X v + 1 ≤ d)
    (hvsW : ∀ w, X.Adj vs w → deg X w = d → ∃ i < r, (F i).Adj vs w)
    (hvsC : vs ∉ C) (hCcard : C.card = 2 * m + u)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b)
    (hrange : ∀ a ∈ C, 1 ≤ π a ∧ π a ≤ 2 * m + u)
    (hsum : ∀ a ∈ C, ∀ b ∈ C, 2 * m + u + 2 ≤ π a + π b → X.Adj a b → ∃ i < r, (F i).Adj a b)
    (htree : ∀ a ∈ C, ∀ b ∈ C, π a + π b = 2 * m + u + 1 → π a ≤ m →
      X.Adj a b ∧ ∀ i < r, ¬ (F i).Adj a b)
    (hU : ∀ a ∈ C, ∀ b ∈ C, m < π a → π a ≤ m + u → m < π b → π b ≤ m + u → ¬ X.Adj a b) :
    Colorable d X := by
  classical
  set D := d - r with hD
  have hD0 : 0 < D := by omega
  -- Z = X minus all factors, Y = Z minus the edges at vs
  let Z : SimpleGraph V :=
    { Adj := fun a b => X.Adj a b ∧ ∀ i < r, ¬ (F i).Adj a b
      symm := ⟨fun a b h => ⟨h.1.symm, fun i hi h' => h.2 i hi h'.symm⟩⟩
      loopless := ⟨fun a h => h.1.ne rfl⟩ }
  let Y : SimpleGraph V :=
    { Adj := fun a b => Z.Adj a b ∧ a ≠ vs ∧ b ≠ vs
      symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun a h => h.1.1.ne rfl⟩ }
  have hR : ∀ k ∈ Finset.range r, k < r := fun k hk => Finset.mem_range.1 hk
  -- degree bound for Z
  have hZdeg : ∀ v, v ≠ vs → deg Z v + r ≤ d ∧ (v ∉ C → deg Z v + r + 1 ≤ d) := by
    intro v hv
    have base := fun b (hdv : (∃ i ∈ Finset.range r, ξ i = v) → deg X v + 1 ≤ b) (hd : deg X v ≤ b) =>
      deg_bound_xi X Z F ξ (Finset.range r) b
        (fun a b hab => ⟨hab.1, fun k hk => hab.2 k (hR k hk)⟩) (fun k hk => hF k (hR k hk))
        (fun k hk j hj => hdisj k (hR k hk) j (hR j hj))
        (fun k hk => hcov k (hR k hk)) v
        (fun i hi j hj h1 h2 => hξinj i (hR i hi) j (hR j hj) (h1 ▸ hv) (h1.trans h2.symm)) hdv hd
    refine ⟨?_, fun hvC => ?_⟩
    · have := base d (fun ⟨i, hi, h⟩ => h ▸ (hξdeg i (hR i hi) (h ▸ hv)).1) (hdeg v)
      rw [Finset.card_range] at this; exact this
    · have := base (d - 1) (fun ⟨i, hi, h⟩ => absurd (h ▸ (hξdeg i (hR i hi) (h ▸ hv)).2.1) hvC)
        (by have := hnc v hv hvC; omega)
      rw [Finset.card_range] at this; omega
  have hYZ : Y ≤ Z := fun a b h => h.1
  have hYdeg : ∀ v, deg Y v ≤ D ∧ (v ∉ C → deg Y v < D) := by
    intro v
    by_cases hv : v = vs
    · subst hv
      have := deg_zero_of_noAdj Y v (fun w h => h.2.1 rfl)
      exact ⟨by omega, fun _ => by omega⟩
    · have h1 := hZdeg v hv
      have h2 := deg_le_of_le hYZ v
      exact ⟨by omega, fun hvC => by have := h1.2 hvC; omega⟩
  have hsurj : ∀ i, 1 ≤ i → i ≤ 2 * m + u → ∃ c ∈ C, π c = i := by
    intro i h1 h2
    obtain ⟨c, hc, he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := C) (t := Finset.Icc 1 (2 * m + u))
      (fun a _ => π a) (fun a ha => Finset.mem_Icc.2 (hrange a ha))
      (fun a b ha hb h => hinj a ha b hb h) (by rw [Nat.card_Icc, hCcard]; omega) i
      (Finset.mem_Icc.2 ⟨h1, h2⟩)
    exact ⟨c, hc, he.symm⟩
  have hYcol : Colorable D Y := by
    refine colorable_core D hD0 Y (fun v => (hYdeg v).1) C π m u hinj hrange hsurj
      (fun v hv => (hYdeg v).2 hv) (fun a ha b hb hab => ?_) (fun a ha b hb h1 h2 => ?_)
      (fun a ha b hb h1 h2 h3 h4 hab => hU a ha b hb h1 h2 h3 h4 hab.1.1)
    · by_contra hcon
      obtain ⟨i, hi, hFi⟩ := hsum a ha b hb (by omega) hab.1.1
      exact hab.1.2 i hi hFi
    · obtain ⟨hX, hnF⟩ := htree a ha b hb h1 h2
      exact ⟨⟨hX, hnF⟩, fun h => hvsC (h ▸ ha), fun h => hvsC (h ▸ hb)⟩
  -- the factors missing vs (NS) and the special ones (SP)
  set NS := (Finset.range r).filter (fun i => ξ i = vs) with hNS
  set SP := (Finset.range r).filter (fun i => ¬ ξ i = vs) with hSP
  have hNSP : NS.card + SP.card = r := by
    rw [hNS, hSP, Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hNSr : ∀ i ∈ NS, i < r := fun i hi => hR i (Finset.mem_filter.1 hi).1
  have hSPr : ∀ i ∈ SP, i < r := fun i hi => hR i (Finset.mem_filter.1 hi).1
  have h1 := colorable_add_matchings Y F hYcol NS (fun i hi => hmat i (hNSr i hi))
  let Q : SimpleGraph V :=
    { Adj := fun a b => X.Adj a b ∧ ∀ i ∈ SP, ¬ (F i).Adj a b
      symm := ⟨fun a b h => ⟨h.1.symm, fun i hi h' => h.2 i hi h'.symm⟩⟩
      loopless := ⟨fun a h => h.1.ne rfl⟩ }
  have baseQ := fun b v (hdv : (∃ i ∈ SP, ξ i = v) → deg X v + 1 ≤ b) (hd : deg X v ≤ b) =>
    deg_bound_xi X Q F ξ SP b (fun a b hab => hab) (fun k hk => hF k (hSPr k hk))
      (fun k hk j hj => hdisj k (hSPr k hk) j (hSPr j hj)) (fun k hk => hcov k (hSPr k hk)) v
      (fun i hi j hj h1 h2 => hξinj i (hSPr i hi) j (hSPr j hj) (Finset.mem_filter.1 hi).2
        (h1.trans h2.symm)) hdv hd
  have hQdeg : ∀ v, deg Q v + SP.card ≤ d := fun v => baseQ d v
    (fun ⟨i, hi, h⟩ => h ▸ (hξdeg i (hSPr i hi) (Finset.mem_filter.1 hi).2).1) (hdeg v)
  have hQvs : ∀ a, Q.Adj vs a → deg Q a + SP.card + 1 ≤ d := by
    intro a ha
    have hnd : deg X a ≠ d := by
      intro hda
      obtain ⟨i, hi, hFi⟩ := hvsW a ha.1 hda
      have hξ : ξ i ≠ vs := fun h => hmiss i hi a (h ▸ hFi)
      exact ha.2 i (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hξ⟩) hFi
    have := baseQ (d - 1) a (fun ⟨i, hi, h⟩ => absurd (h ▸ ha.1)
      (hξdeg i (hSPr i hi) (Finset.mem_filter.1 hi).2).2.2) (by have := hdeg a; omega)
    omega
  let H0 := Y ⊔ unionG F NS
  have hH0Q : H0 ≤ Q := by
    intro a b h
    rcases h with h | ⟨i, hi, h⟩
    · exact ⟨h.1.1, fun j hj => h.1.2 j (hSPr j hj)⟩
    · refine ⟨hF i (hNSr i hi) h, fun j hj hj' => ?_⟩
      have hij : i ≠ j := fun e => (Finset.mem_filter.1 hj).2 (e ▸ (Finset.mem_filter.1 hi).2)
      exact hdisj i (hNSr i hi) j (hSPr j hj) hij a b h hj'
  have hQcol : Colorable (D + NS.card) Q := by
    refine colorable_of_steps (D + NS.card) Q (fun v => by have := hQdeg v; omega)
      (fun H => H0 ≤ H ∧ H ≤ Q) (fun H h => h.2) (fun H hI hne => ?_) H0 ⟨le_rfl, hH0Q⟩ h1
    obtain ⟨hH0, hHQ⟩ := hI
    have hex : ∃ a b, Q.Adj a b ∧ ¬ H.Adj a b := by
      by_contra hcon; push Not at hcon
      exact hne (le_antisymm hHQ (fun a b h => hcon a b h))
    obtain ⟨a, b, hab, hnab⟩ := hex
    have hvs : a = vs ∨ b = vs := by
      by_contra hcon; push Not at hcon
      apply hnab; apply hH0
      by_cases hF' : ∃ i < r, (F i).Adj a b
      · obtain ⟨i, hi, hFi⟩ := hF'
        by_cases hξ : ξ i = vs
        · exact Or.inr ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hξ⟩, hFi⟩
        · exact absurd hFi (hab.2 i (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hξ⟩))
      · push Not at hF'
        exact Or.inl ⟨⟨hab.1, hF'⟩, hcon.1, hcon.2⟩
    have piv : ∀ y, Q.Adj vs y → ¬ H.Adj vs y → ∃ p y', Q.Adj p y' ∧ ¬ H.Adj p y' ∧
        (H0 ≤ H ⊔ edge p y' ∧ H ⊔ edge p y' ≤ Q) ∧
        ∀ a b, (H ⊔ edge p y').Adj p a → (H ⊔ edge p y').Adj p b → deg (H ⊔ edge p y') a = D + NS.card →
          deg (H ⊔ edge p y') b = D + NS.card → a = b := by
      intro y hy hny
      have hle : H ⊔ edge vs y ≤ Q := by
        intro a b h
        rcases h with h | h
        · exact hHQ h
        · rw [edge_adj] at h
          rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hy
          · exact hy.symm
      refine ⟨vs, y, hy, hny, ⟨le_trans hH0 le_sup_left, hle⟩, fun a b ha _ hda _ => ?_⟩
      have := hQvs a (hle ha)
      have := deg_le_of_le hle a
      omega
    rcases hvs with rfl | rfl
    · exact piv b hab hnab
    · exact piv a hab.symm (fun h => hnab h.symm)
  have h3 := colorable_add_matchings Q F hQcol SP (fun i hi => hmat i (hSPr i hi))
  have hcnt : D + NS.card + SP.card = d := by omega
  rw [hcnt] at h3
  refine h3.mono (fun a b h => ?_)
  by_cases hF' : ∃ i ∈ SP, (F i).Adj a b
  · exact Or.inr hF'
  · push Not at hF'
    exact Or.inl ⟨h, hF'⟩

end OMA.H1
-- ===== LemmasConstr.lean =====
-- depends on all previous lemma files; assembled by build_all.sh
namespace OMA.H1

open SimpleGraph

/-- `|Xs| = |Ws| + (|V| - d - |W|)` -/
lemma card_Xs {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj] (d : ℕ) (vs : V)
    (hvs : deg X vs = d) :
    (Finset.univ.filter (fun x => x ≠ vs ∧ ¬ X.Adj vs x ∧ deg X x ≠ d)).card +
      (Finset.univ.filter (fun v => deg X v = d)).card + d =
    (Finset.univ.filter (fun w => deg X w = d ∧ X.Adj vs w)).card + Fintype.card V := by
  have hN : (Finset.univ.filter (fun x => X.Adj vs x)).card = d := by
    rw [← hvs, deg_eq, ← card_neighborFinset_eq_degree]; congr 1; ext x; simp
  have s1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => X.Adj vs x)
  have s2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun x => ¬ X.Adj vs x)) (fun x => x = vs)
  have s3 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ.filter (fun x => ¬ X.Adj vs x)).filter (fun x => ¬ x = vs)) (fun x => deg X x = d)
  have s4 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun v => deg X v = d)) (fun x => x = vs)
  have s5 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ.filter (fun v => deg X v = d)).filter (fun x => ¬ x = vs)) (fun x => X.Adj vs x)
  have e1 : (Finset.univ.filter (fun x => ¬ X.Adj vs x)).filter (fun x => x = vs) = {vs} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨X.loopless.irrefl _, rfl⟩
  have e4 : (Finset.univ.filter (fun v => deg X v = d)).filter (fun x => x = vs) = {vs} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hvs, rfl⟩
  have e3 : ((Finset.univ.filter (fun x => ¬ X.Adj vs x)).filter (fun x => ¬ x = vs)).filter
      (fun x => ¬ deg X x = d) = Finset.univ.filter (fun x => x ≠ vs ∧ ¬ X.Adj vs x ∧ deg X x ≠ d) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have e5 : ((Finset.univ.filter (fun v => deg X v = d)).filter (fun x => ¬ x = vs)).filter
      (fun x => X.Adj vs x) = Finset.univ.filter (fun w => deg X w = d ∧ X.Adj vs w) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, fun e => X.loopless.irrefl vs (e ▸ h.2)⟩, h.2⟩
  have e35 : ((Finset.univ.filter (fun x => ¬ X.Adj vs x)).filter (fun x => ¬ x = vs)).filter
      (fun x => deg X x = d) =
      ((Finset.univ.filter (fun v => deg X v = d)).filter (fun x => ¬ x = vs)).filter
      (fun x => ¬ X.Adj vs x) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [e1, Finset.card_singleton] at s2
  rw [e4, Finset.card_singleton] at s4
  rw [e3, e35] at s3
  rw [e5] at s5
  rw [Finset.card_univ] at s1
  omega

end OMA.H1

namespace OMA.H1

open SimpleGraph

/-- the good X's (left half or middle) precede the good W_s's (middle or right half), and each set
contains at least half of its kind -/
lemma pairing_bound {V : Type*} [DecidableEq V] (C Xs Ws : Finset V) (π ρ : V → ℕ) (m u : ℕ)
    (hXC : Xs ⊆ C) (hWC : Ws ⊆ C) (hXW : Disjoint Xs Ws)
    (hρ0 : ∀ x ∈ C, ρ x = 0 → x ∈ Xs) (hρX : ∀ x ∈ Xs, ρ x = 0)
    (hρ2 : ∀ x ∈ C, 2 ≤ ρ x → x ∈ Ws) (hρW : ∀ x ∈ Ws, ρ x = 2)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b)
    (hrange : ∀ a ∈ C, 1 ≤ π a ∧ π a ≤ 2 * m + u)
    (hsurj : ∀ i, 1 ≤ i → i ≤ 2 * m + u → ∃ c ∈ C, π c = i)
    (htree : ∀ a ∈ C, ∀ b ∈ C, π a + π b = 2 * m + u + 1 → π a ≤ m → ρ a ≤ ρ b)
    (hmid : ∀ a ∈ C, ∀ b ∈ C, m < π a → π a ≤ m + u → m < π b → π b ≤ m + u → π a < π b → ρ a ≤ ρ b) :
    (∀ x ∈ Xs.filter (fun x => π x ≤ m + u), ∀ w ∈ Ws.filter (fun w => m < π w), π x < π w) ∧
    Xs.card ≤ 2 * (Xs.filter (fun x => π x ≤ m + u)).card ∧
    Ws.card ≤ 2 * (Ws.filter (fun w => m < π w)).card := by
  classical
  set q := 2 * m + u
  let pt : V → V := fun x => if h : ∃ c ∈ C, π c = q + 1 - π x then h.choose else x
  have hpt : ∀ x ∈ C, pt x ∈ C ∧ π (pt x) + π x = q + 1 := by
    intro x hx
    have hr := hrange x hx
    have h : ∃ c ∈ C, π c = q + 1 - π x := hsurj _ (by omega) (by omega)
    simp only [pt, dif_pos h]
    exact ⟨h.choose_spec.1, by have := h.choose_spec.2; omega⟩
  have hptinj : ∀ S ⊆ C, Set.InjOn pt S := by
    intro S hS x hx y hy h
    have h1 := hpt x (hS hx); have h2 := hpt y (hS hy)
    rw [h] at h1
    exact hinj x (hS hx) y (hS hy) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx w hw
    rw [Finset.mem_filter] at hx hw
    have hxC := hXC hx.1; have hwC := hWC hw.1
    by_contra hcon
    rcases Nat.lt_or_ge (π w) (π x) with hlt | hle
    · have := hmid w hwC x hxC hw.2 (by omega) (by omega) hx.2 hlt
      rw [hρW w hw.1, hρX x hx.1] at this; omega
    · have := hinj x hxC w hwC (by omega)
      exact Finset.disjoint_left.1 hXW hx.1 (this ▸ hw.1)
  · have hs := Finset.card_filter_add_card_filter_not (s := Xs) (fun x => π x ≤ m + u)
    have hle : (Xs.filter (fun x => ¬ π x ≤ m + u)).card ≤ (Xs.filter (fun x => π x ≤ m + u)).card := by
      refine Finset.card_le_card_of_injOn pt (fun x hx => ?_) (hptinj _ (fun x hx => hXC (Finset.mem_filter.1 hx).1))
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      have hxC := hXC hx.1
      obtain ⟨hpC, hps⟩ := hpt x hxC
      have hr := hrange x hxC
      have := htree (pt x) hpC x hxC hps (by omega)
      rw [hρX x hx.1] at this
      exact ⟨hρ0 _ hpC (by omega), by omega⟩
    omega
  · have hs := Finset.card_filter_add_card_filter_not (s := Ws) (fun w => m < π w)
    have hle : (Ws.filter (fun w => ¬ m < π w)).card ≤ (Ws.filter (fun w => m < π w)).card := by
      refine Finset.card_le_card_of_injOn pt (fun x hx => ?_) (hptinj _ (fun x hx => hWC (Finset.mem_filter.1 hx).1))
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      have hxC := hWC hx.1
      obtain ⟨hpC, hps⟩ := hpt x hxC
      have hr := hrange x hxC
      have := htree x hxC (pt x) hpC (by omega) (by omega)
      rw [hρW x hx.1] at this
      exact ⟨hρ2 _ hpC this, by omega⟩
    omega

end OMA.H1

namespace OMA.H1

open SimpleGraph

lemma exists_enum {V : Type*} (S : Finset V) (v0 : V) :
    ∃ f : ℕ → V, (∀ j < S.card, f j ∈ S) ∧ (∀ i < S.card, ∀ j < S.card, f i = f j → i = j) ∧
      (∀ v ∈ S, ∃ j < S.card, f j = v) := by
  classical
  refine ⟨fun j => if h : j < S.card then (S.equivFin.symm ⟨j, h⟩).1 else v0, fun j hj => ?_,
    fun i hi j hj h => ?_, fun v hv => ?_⟩
  · simp only [dif_pos hj]; exact (S.equivFin.symm ⟨j, hj⟩).2
  · simp only [dif_pos hi, dif_pos hj] at h
    have := S.equivFin.symm.injective (Subtype.ext h)
    simpa using this
  · refine ⟨(S.equivFin ⟨v, hv⟩).1, (S.equivFin ⟨v, hv⟩).2, ?_⟩
    simp only [dif_pos (S.equivFin ⟨v, hv⟩).2]
    simp

lemma coverCard_le_of {V : Type*} [Fintype V] (M : SimpleGraph V) (T : Finset V)
    (h : ∀ v u, M.Adj v u → v ∈ T) : coverCard M ≤ T.card := by
  classical
  unfold coverCard
  apply Finset.card_le_card
  intro v hv
  rw [Finset.mem_filter] at hv
  obtain ⟨u, hu⟩ := hv.2
  exact h v u hu

lemma card_pos_ge {V : Type*} [DecidableEq V] (C : Finset V) (π : V → ℕ) (Q k : ℕ)
    (hinj : ∀ a ∈ C, ∀ b ∈ C, π a = π b → a = b) (hr : ∀ a ∈ C, π a ≤ Q) :
    (C.filter (fun v => k ≤ π v)).card ≤ Q + 1 - k := by
  have := Finset.card_le_card_of_injOn π (s := C.filter (fun v => k ≤ π v)) (t := Finset.Icc k Q) (fun v hv => by
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Finset.mem_Icc]; exact ⟨hv.2, hr v hv.1⟩)
    (fun a ha b hb h => hinj a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 h)
  rw [Nat.card_Icc] at this; exact this

lemma coverCard_edge {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    coverCard (edge a b) ≤ 2 := by
  classical
  refine (coverCard_le_of _ {a, b} (fun v u h => ?_)).trans Finset.card_le_two
  rw [edge_adj] at h
  rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

end OMA.H1
-- ===== LemmasMain.lean =====
-- depends on all previous lemma files; assembled by build_all.sh
namespace OMA.H1

open SimpleGraph

theorem colorable_X {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj]
    (n d : ℕ) (hV : Fintype.card V + 1 = 2 * n) (h7 : 12 * n ≤ 7 * d) (h3 : d + 3 ≤ 2 * n)
    (hdeg : ∀ v, deg X v = d ∨ deg X v + 1 = d)
    (hW : (Finset.univ.filter (fun v => deg X v = d)).card + d = Fintype.card V) :
    Colorable d X := by
  -- step 0: the vertex vs, its W-neighbours Ws, the set Xs, the core C
  obtain ⟨vs, hvs⟩ : ∃ vs, vs ∈ Finset.univ.filter (fun v => deg X v = d) :=
    Finset.card_pos.1 (by omega)
  rw [Finset.mem_filter] at hvs
  replace hvs := hvs.2
  have hcX := card_Xs X d vs hvs
  set Ws := Finset.univ.filter (fun w => deg X w = d ∧ X.Adj vs w) with hWs
  set Xs := Finset.univ.filter (fun x => x ≠ vs ∧ ¬ X.Adj vs x ∧ deg X x ≠ d) with hXs
  set W' := Finset.univ.filter (fun v => deg X v = d ∧ v ≠ vs) with hW'
  set C := W' ∪ Xs with hC
  have hXsWs : Xs.card = Ws.card := by omega
  classical
  have hW'card : W'.card + 1 = (Finset.univ.filter (fun v => deg X v = d)).card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun v => deg X v = d))
      (fun v => v = vs)
    have e1 : (Finset.univ.filter (fun v => deg X v = d)).filter (fun v => v = vs) = {vs} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hvs, h⟩⟩
    have e2 : (Finset.univ.filter (fun v => deg X v = d)).filter (fun v => ¬ v = vs) = W' := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hW']
    rw [e1, e2, Finset.card_singleton] at this; omega
  have hdisjWX : Disjoint W' Xs := by
    rw [Finset.disjoint_left]; intro x h1 h2
    rw [Finset.mem_filter] at h1 h2; exact h2.2.2.2 h1.2.1
  have hCcard : C.card = W'.card + Xs.card := Finset.card_union_of_disjoint hdisjWX
  have hWsW' : Ws ⊆ W' := by
    intro x hx; rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1, fun h => X.loopless.irrefl vs (h ▸ hx.2.2)⟩
  have hWsC : Ws ⊆ C := hWsW'.trans Finset.subset_union_left
  have hXsC : Xs ⊆ C := Finset.subset_union_right
  have hvsC : vs ∉ C := by
    intro h; rcases Finset.mem_union.1 h with h | h <;> rw [Finset.mem_filter] at h
    · exact h.2.2 rfl
    · exact h.2.1 rfl
  have hXWs : Disjoint Xs Ws := by
    rw [Finset.disjoint_left]; intro x h1 h2
    rw [Finset.mem_filter] at h1 h2; exact h1.2.2.2 h2.2.1
  set s := Ws.card with hs
  -- step 1: positions
  let ρ : V → ℕ := fun v => if v ∈ Xs then 0 else if v ∈ Ws then 2 else 1
  obtain ⟨π, m, u, hq, hinj, hrange, htree, hU⟩ := exists_positions X ρ C
  set q := 2 * m + u with hqdef
  have hsurj : ∀ i, 1 ≤ i → i ≤ q → ∃ c ∈ C, π c = i := by
    intro i h1 h2
    obtain ⟨c, hc, he⟩ := Finset.surj_on_of_inj_on_of_card_le (s := C) (t := Finset.Icc 1 q)
      (fun a _ => π a) (fun a ha => Finset.mem_Icc.2 (hrange a ha))
      (fun a b ha hb h => hinj a ha b hb h) (by rw [Nat.card_Icc]; omega) i
      (Finset.mem_Icc.2 ⟨h1, h2⟩)
    exact ⟨c, hc, he.symm⟩
  -- step 2: good X's and W_s's
  obtain ⟨hord, hAc, hBc⟩ := pairing_bound C Xs Ws π ρ m u hXsC hWsC hXWs
    (fun x _ h => by simp only [ρ] at h; split_ifs at h with h1 <;> first | exact h1 | omega)
    (fun x hx => by simp only [ρ, if_pos hx])
    (fun x _ h => by simp only [ρ] at h; split_ifs at h with h1 h2 <;> first | exact h2 | omega)
    (fun x hx => by simp only [ρ, if_neg (Finset.disjoint_right.1 hXWs hx), if_pos hx])
    hinj hrange hsurj (fun a ha b hb h1 h2 => (htree a ha b hb h1 h2).2)
    (fun a ha b hb h1 h2 h3 h4 h5 => (hU a ha b hb h1 h2 h3 h4).2 h5)
  set A := Xs.filter (fun x => π x ≤ m + u)
  set B := Ws.filter (fun w => m < π w)
  set k := min A.card B.card with hk
  obtain ⟨A', hA'A, hA'k⟩ := Finset.exists_subset_card_eq (show k ≤ A.card from min_le_left _ _)
  obtain ⟨B', hB'B, hB'k⟩ := Finset.exists_subset_card_eq (show k ≤ B.card from min_le_right _ _)
  have hA'Xs : A' ⊆ Xs := hA'A.trans (Finset.filter_subset _ _)
  have hB'Ws : B' ⊆ Ws := hB'B.trans (Finset.filter_subset _ _)
  set e := (Ws \ B').card with he
  have heX : (Xs \ A').card = e := by
    rw [he, Finset.card_sdiff_of_subset hA'Xs, Finset.card_sdiff_of_subset hB'Ws]; omega
  have h2e : 2 * e ≤ s := by
    rw [he, Finset.card_sdiff_of_subset hB'Ws]; omega
  obtain ⟨ea, hea1, hea2, hea3⟩ := exists_enum A' vs
  obtain ⟨eb, heb1, heb2, heb3⟩ := exists_enum B' vs
  obtain ⟨ea', hea'1, hea'2, hea'3⟩ := exists_enum (Xs \ A') vs
  obtain ⟨eb', heb'1, heb'2, heb'3⟩ := exists_enum (Ws \ B') vs
  -- step 3: vs at position q+1; tree pairs; X0 = X minus tree pairs
  let π' : V → ℕ := fun v => if v = vs then q + 1 else π v
  have hπ'C : ∀ v ∈ C, π' v = π v := fun v hv => if_neg (fun h : v = vs => hvsC (h ▸ hv))
  have hπ'vs : π' vs = q + 1 := if_pos rfl
  have hinj' : ∀ a, (a = vs ∨ a ∈ C) → ∀ b, (b = vs ∨ b ∈ C) → π' a = π' b → a = b := by
    intro a ha b hb h
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · rw [hπ'vs, hπ'C b hb] at h; have := hrange b hb; omega
    · rw [hπ'vs, hπ'C a ha] at h; have := hrange a ha; omega
    · rw [hπ'C a ha, hπ'C b hb] at h; exact hinj a ha b hb h
  let T : V → V → Prop := fun a b => a ∈ C ∧ b ∈ C ∧ π a + π b = q + 1
  let X0 : SimpleGraph V :=
    { Adj := fun a b => X.Adj a b ∧ ¬ T a b
      symm := ⟨fun a b h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2.1, h'.1, by have := h'.2.2; omega⟩⟩⟩
      loopless := ⟨fun a h => h.1.ne rfl⟩ }
  have hX0deg : ∀ v, d - 2 ≤ X0.degree v := by
    intro v
    have hXv : d ≤ deg X v + 1 := by rcases hdeg v with h | h <;> omega
    have : deg X v ≤ deg X0 v + 1 := by
      rw [deg_eq, deg_eq, ← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      by_cases hex : ∃ c, T v c
      · obtain ⟨c, hc⟩ := hex
        refine (Finset.card_le_card (t := insert c (X0.neighborFinset v)) (fun y hy => ?_)).trans
          (Finset.card_insert_le _ _)
        rw [mem_neighborFinset] at hy
        by_cases hT : T v y
        · rw [hinj y hT.2.1 c hc.2.1 (by have := hT.2.2; have := hc.2.2; omega)]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem ((mem_neighborFinset _ _ _).2 ⟨hy, hT⟩)
      · push Not at hex
        refine (Finset.card_le_card (fun y hy => ?_)).trans (Nat.le_succ _)
        rw [mem_neighborFinset] at hy ⊢; exact ⟨hy, hex y⟩
    have h0 := deg_eq X0 v; omega
  -- step 4: the matchings
  let pr : V → V := fun w => if h : ∃ j < k, eb j = w then ea h.choose else vs
  have hpr : ∀ j < k, pr (eb j) = ea j := by
    intro j hj
    have h : ∃ j' < k, eb j' = eb j := ⟨j, hj, rfl⟩
    simp only [pr, dif_pos h]
    congr 1
    exact heb2 _ (by rw [hB'k]; exact h.choose_spec.1) j (by rw [hB'k]; exact hj) h.choose_spec.2
  let SC : ℕ → SimpleGraph V := fun i =>
    { Adj := fun x y => X.Adj x y ∧ (x = vs ∨ x ∈ C) ∧ (y = vs ∨ y ∈ C) ∧ π' x + π' y = i + q + 2 ∧
        ¬ (x = vs ∧ y ∈ Ws \ B') ∧ ¬ (y = vs ∧ x ∈ Ws \ B')
      symm := ⟨fun x y h => ⟨h.1.symm, h.2.2.1, h.2.1, by have := h.2.2.2.1; omega, h.2.2.2.2.2,
        h.2.2.2.2.1⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  let M : ℕ → SimpleGraph V := fun i =>
    if i < q then SC i else if i < q + e then edge vs (eb' (i - q)) else ⊥
  let ξ : ℕ → V := fun i =>
    if i < q then (if h : ∃ w ∈ B', π w = i + 1 then pr h.choose else vs) else ea' (i - q)
  have hSC_X0 : ∀ i, SC i ≤ X0 := by
    intro i x y h
    refine ⟨h.1, fun hT => ?_⟩
    have h1 := h.2.2.2.1
    rw [hπ'C x hT.1, hπ'C y hT.2.1] at h1
    have := hT.2.2; omega
  have hedge_X0 : ∀ j < e, edge vs (eb' j) ≤ X0 := by
    intro j hj x y h
    rw [edge_adj] at h
    have hw := heb'1 j hj
    rw [Finset.mem_sdiff, Finset.mem_filter] at hw
    have hX : X.Adj vs (eb' j) := hw.1.2.2
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hX, fun hT => hvsC hT.1⟩
    · exact ⟨hX.symm, fun hT => hvsC hT.2.1⟩
  have hMX : ∀ i, M i ≤ X0 := by
    intro i
    simp only [M]
    split_ifs with h1 h2
    · exact hSC_X0 i
    · exact hedge_X0 (i - q) (by omega)
    · exact bot_le
  have hedge_m : ∀ a b : V, ∀ v u u', (edge a b).Adj v u → (edge a b).Adj v u' → u = u' := by
    intro a b v u u' h h'
    rw [edge_adj] at h h'
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first | exact h2.symm | exact h2 | exact absurd h1 h'.2 | exact absurd h1.symm h'.2 |
        exact absurd h2 h'.2 | exact absurd h2.symm h'.2 | (subst_vars; rfl)
  have hSC_m : ∀ i v x x', (SC i).Adj v x → (SC i).Adj v x' → x = x' := by
    intro i v x x' h h'
    exact hinj' x h.2.2.1 x' h'.2.2.1 (by have := h.2.2.2.1; have := h'.2.2.2.1; omega)
  have hMm : ∀ i v x x', (M i).Adj v x → (M i).Adj v x' → x = x' := by
    intro i
    simp only [M]
    split_ifs with h1 h2
    · exact hSC_m i
    · exact hedge_m _ _
    · intro v x x' h; exact absurd h (by simp)
  have hrange' : ∀ v, (v = vs ∨ v ∈ C) → 1 ≤ π' v ∧ π' v ≤ q + 1 := by
    intro v hv
    rcases hv with rfl | hv
    · rw [hπ'vs]; omega
    · rw [hπ'C v hv]; have := hrange v hv; omega
  have hvsW : ∀ y ∈ C, X.Adj vs y → y ∈ Ws := by
    intro y hy hXy
    rcases Finset.mem_union.1 hy with h | h
    · rw [Finset.mem_filter] at h ⊢; exact ⟨Finset.mem_univ _, h.2.1, hXy⟩
    · rw [Finset.mem_filter] at h; exact absurd hXy h.2.2.1
  have hξ : ∀ i u, ¬ (M i).Adj (ξ i) u := by
    intro i y hy
    by_cases hiq : i < q
    · simp only [M, ξ, if_pos hiq] at hy
      by_cases h : ∃ w ∈ B', π w = i + 1
      · rw [dif_pos h] at hy
        obtain ⟨hwB, hwπ⟩ := h.choose_spec
        obtain ⟨j, hj, hjw⟩ := heb3 _ hwB
        rw [← hjw, hpr j (by omega)] at hy
        have hjA : ea j ∈ A := hA'A (hea1 j (by omega))
        have hlt := hord (ea j) hjA (eb j) (hB'B (heb1 j hj))
        have hC1 : ea j ∈ C := hXsC (hA'Xs (hea1 j (by omega)))
        have := hy.2.2.2.1
        have := (hrange' y hy.2.2.1).2
        rw [hπ'C _ hC1] at *
        rw [hjw] at hlt
        omega
      · rw [dif_neg h] at hy
        have h1 := hy.2.2.2.1
        rw [hπ'vs] at h1
        rcases hy.2.2.1 with rfl | hyC
        · rw [hπ'vs] at h1; omega
        · rw [hπ'C y hyC] at h1
          have hyW := hvsW y hyC hy.1
          have hyB : y ∈ B' := by
            by_contra hn; exact hy.2.2.2.2.1 ⟨rfl, Finset.mem_sdiff.2 ⟨hyW, hn⟩⟩
          exact h ⟨y, hyB, by omega⟩
    · by_cases hie : i < q + e
      · simp only [M, ξ, if_neg hiq, if_pos hie] at hy
        rw [edge_adj] at hy
        have hx := hea'1 (i - q) (by omega)
        have hw := heb'1 (i - q) (by omega)
        rw [Finset.mem_sdiff] at hx hw
        have hne := (Finset.mem_filter.1 hx.1).2.1
        rcases hy.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hne h1 | exact hne h1.symm | exact hne h2 | exact hne h2.symm |
            exact Finset.disjoint_left.1 hXWs hx.1 (h2 ▸ hw.1) |
            exact Finset.disjoint_left.1 hXWs hx.1 (h2.symm ▸ hw.1) |
            exact Finset.disjoint_left.1 hXWs hx.1 (h1 ▸ hw.1) |
            exact Finset.disjoint_left.1 hXWs hx.1 (h1.symm ▸ hw.1)
      · simp only [M, if_neg hiq, if_neg hie] at hy; exact hy
  have hqe : q + e ≤ d - n - 2 := by
    have : s ≤ W'.card := Finset.card_le_card hWsW'
    omega
  have hsize : ∀ i < q + e, Fintype.card V - 1 - coverCard (M i) + 2 * (i + 1 + coverCard (M i)) ≤
      2 * (d - 2) := by
    intro i hi
    by_cases hiq : i < q
    · have hc : coverCard (M i) ≤ q + 1 - i := by
        simp only [M, if_pos hiq]
        refine (coverCard_le_of _ ((insert vs C).filter (fun v => i + 1 ≤ π' v)) (fun v y h => ?_)).trans
          ((card_pos_ge (insert vs C) π' (q + 1) (i + 1) (fun a ha b hb hab => hinj' a
            (Finset.mem_insert.1 ha) b (Finset.mem_insert.1 hb) hab)
            (fun a ha => (hrange' a (Finset.mem_insert.1 ha)).2)).trans (by omega))
        rw [Finset.mem_filter, Finset.mem_insert]
        have := h.2.2.2.1; have := (hrange' y h.2.2.1).2
        exact ⟨h.2.1, by omega⟩
      omega
    · have hc : coverCard (M i) ≤ 2 := by
        simp only [M, if_neg hiq, if_pos hi]; exact coverCard_edge _ _
      omega
  have hodd : Odd (Fintype.card V) := ⟨n - 1, by omega⟩
  obtain ⟨F, hF⟩ := exists_near_factors_CH X0 (q + e) (d - 2) hX0deg hodd M ξ hMX hMm hξ hsize
  have hξform : ∀ i < q + e, ξ i ≠ vs →
      (i < q ∧ ∃ j < k, ξ i = ea j ∧ π (eb j) = i + 1) ∨ (q ≤ i ∧ ξ i = ea' (i - q)) := by
    intro i hi hne
    by_cases hiq : i < q
    · left
      refine ⟨hiq, ?_⟩
      have hne' := hne
      simp only [ξ, if_pos hiq] at hne' ⊢
      by_cases h : ∃ w ∈ B', π w = i + 1
      · rw [dif_pos h]
        obtain ⟨hwB, hwπ⟩ := h.choose_spec
        obtain ⟨j, hj, hjw⟩ := heb3 _ hwB
        refine ⟨j, by omega, ?_, by rw [hjw]; exact hwπ⟩
        rw [← hjw, hpr j (by omega)]
      · rw [dif_neg h] at hne'; exact absurd rfl hne'
    · right
      refine ⟨by omega, ?_⟩
      simp only [ξ, if_neg hiq]
  have hξXs : ∀ i < q + e, ξ i ≠ vs → ξ i ∈ Xs := by
    intro i hi hne
    rcases hξform i hi hne with ⟨_, j, hj, h, _⟩ | ⟨_, h⟩
    · rw [h]; exact hA'Xs (hea1 j (by omega))
    · rw [h]; exact (Finset.mem_sdiff.1 (hea'1 (i - q) (by omega))).1
  have hcovM : ∀ i < q + e, ∀ a b, (M i).Adj a b → ∃ j < q + e, (F j).Adj a b := by
    intro i hi a b h
    obtain ⟨j, hj, hFj⟩ := (hF i hi).2.1 a b h
    exact ⟨j, by omega, hFj⟩
  refine colorable_assemble X d (q + e) vs F ξ C π m u (by omega)
    (fun i hi => le_trans (hF i hi).1 (fun a b h => h.1))
    (fun i hi v hv => ((hF i hi).2.2.2.1 v hv).exists)
    (fun i hi => (hF i hi).2.2.1)
    (fun i hi v x x' h h' => by
      have hv : v ≠ ξ i := fun e => (hF i hi).2.2.1 x (e ▸ h)
      exact ((hF i hi).2.2.2.1 v hv).unique h h')
    (fun i hi j hj hij => (hF i hi).2.2.2.2 j hj hij)
    ?_ (fun v => by rcases hdeg v with h | h <;> omega)
    (fun i hi hne => ?_) (fun v hv hvC => ?_) (fun w hw hdw => ?_) hvsC hq.symm hinj hrange
    (fun a ha b hb hs hab => ?_)
    (fun a ha b hb h1 h2 => ⟨(htree a ha b hb h1 h2).1, fun i hi hFi =>
      ((hF i hi).1 hFi).2 ⟨ha, hb, h1⟩⟩)
    (fun a ha b hb h1 h2 h3 h4 => (hU a ha b hb h1 h2 h3 h4).1)
  · -- injectivity of ξ on the special indices
    intro i hi j hj hne hij
    have hne' : ξ j ≠ vs := hij ▸ hne
    rcases hξform i hi hne with ⟨hiq, a, ha, h1, h2⟩ | ⟨hiq, h1⟩ <;>
      rcases hξform j hj hne' with ⟨hjq, b, hb, h3, h4⟩ | ⟨hjq, h3⟩
    · have hab := hea2 a (by omega) b (by omega) (by rw [← h1, ← h3]; exact hij)
      subst hab; omega
    · exfalso
      have := (Finset.mem_sdiff.1 (hea'1 (j - q) (by omega))).2
      rw [← h3, ← hij, h1] at this; exact this (hea1 a (by omega))
    · exfalso
      have := (Finset.mem_sdiff.1 (hea'1 (i - q) (by omega))).2
      rw [← h1, hij, h3] at this; exact this (hea1 b (by omega))
    · have := hea'2 (i - q) (by omega) (j - q) (by omega) (by rw [← h1, ← h3]; exact hij)
      omega
  · have hx := hξXs i hi hne
    rw [Finset.mem_filter] at hx
    exact ⟨by rcases hdeg (ξ i) with h | h; exact absurd h hx.2.2.2; omega, hXsC (hξXs i hi hne), hx.2.2.1⟩
  · have hnd : deg X v ≠ d := fun h => hvC (Finset.mem_union_left _ (Finset.mem_filter.2
      ⟨Finset.mem_univ _, h, hv⟩))
    rcases hdeg v with h | h; exact absurd h hnd; omega
  · have hwC : w ∈ C := Finset.mem_union_left _ (Finset.mem_filter.2
      ⟨Finset.mem_univ _, hdw, fun h => hw.ne h.symm⟩)
    have hwWs := hvsW w hwC hw
    have hr := hrange w hwC
    by_cases hwB : w ∈ B'
    · refine hcovM (π w - 1) (by omega) vs w ?_
      simp only [M, if_pos (show π w - 1 < q by omega)]
      refine ⟨hw, Or.inl rfl, Or.inr hwC, ?_, fun h => (Finset.mem_sdiff.1 h.2).2 hwB,
        fun h => hw.ne h.1.symm⟩
      rw [hπ'vs, hπ'C w hwC]; omega
    · obtain ⟨j, hj, hjw⟩ := heb'3 w (Finset.mem_sdiff.2 ⟨hwWs, hwB⟩)
      refine hcovM (q + j) (by omega) vs w ?_
      simp only [M, if_neg (show ¬ q + j < q by omega), if_pos (show q + j < q + e by omega),
        Nat.add_sub_cancel_left, hjw]
      rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hw.ne⟩
  · have hne : π a ≠ π b := fun h => hab.ne (hinj a ha b hb h)
    have h1 := hrange a ha; have h2 := hrange b hb
    refine hcovM (π a + π b - q - 2) (by omega) a b ?_
    simp only [M, if_pos (show π a + π b - q - 2 < q by omega)]
    refine ⟨hab, Or.inr ha, Or.inr hb, ?_, fun h => hvsC (h.1 ▸ ha), fun h => hvsC (h.1 ▸ hb)⟩
    rw [hπ'C a ha, hπ'C b hb]; omega

end OMA.H1
-- ===== LemmasFinal.lean =====
-- depends on all previous lemma files; assembled by build_all.sh
namespace OMA.H1

open SimpleGraph

lemma induce_neighborFinset_map {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V) (v : {x // x ≠ w}) :
    ((G.induce {x | x ≠ w}).neighborFinset v).map (Function.Embedding.subtype _) =
      (G.neighborFinset v.1).erase w := by
  ext y
  simp only [Finset.mem_map, mem_neighborFinset, Function.Embedding.coe_subtype, Finset.mem_erase,
    comap_adj, Function.Embedding.subtype]
  constructor
  · rintro ⟨y', hy', rfl⟩; exact ⟨y'.2, hy'⟩
  · rintro ⟨hyw, hy⟩; exact ⟨⟨y, hyw⟩, hy, rfl⟩

theorem solution_H1 : OMA.R_wp_1_factorization_conjecture_R1.H1 := by
  intro n k h7 h3 G _ hreg
  classical
  have hn : 0 < 2 * n := by omega
  let w : Fin (2 * n) := ⟨0, hn⟩
  let X := G.induce {x | x ≠ w}
  have hcard : Fintype.card {x : Fin (2 * n) // x ≠ w} + 1 = 2 * n := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]; omega
  have hdegv : ∀ v : {x : Fin (2 * n) // x ≠ w},
      deg X v + (if G.Adj v.1 w then 1 else 0) = k := by
    intro v
    rw [deg_eq, ← card_neighborFinset_eq_degree, ← Finset.card_map (Function.Embedding.subtype _),
      induce_neighborFinset_map]
    have hk := hreg v.1
    rw [← card_neighborFinset_eq_degree] at hk
    split_ifs with h
    · rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 h)]
      have := Finset.card_pos.2 ⟨w, (mem_neighborFinset _ _ _).2 h⟩; omega
    · rw [Finset.erase_eq_of_notMem (fun hm => h ((mem_neighborFinset _ _ _).1 hm))]; omega
  have hW : (Finset.univ.filter (fun v => deg X v = k)).card + k =
      Fintype.card {x : Fin (2 * n) // x ≠ w} := by
    have e1 : Finset.univ.filter (fun v => deg X v = k) =
        Finset.univ.filter (fun v : {x : Fin (2 * n) // x ≠ w} => ¬ G.Adj v.1 w) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hdegv v; split_ifs at this with h <;> simp [h] <;> omega
    have e2 : (Finset.univ.filter (fun v : {x : Fin (2 * n) // x ≠ w} => G.Adj v.1 w)).card = k := by
      rw [← hreg w, ← card_neighborFinset_eq_degree,
        ← Finset.card_map (Function.Embedding.subtype (fun x : Fin (2 * n) => x ≠ w))]
      congr 1; ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨y', hy', rfl⟩; exact hy'.symm
      · intro hy; exact ⟨⟨y, fun e => hy.ne e.symm⟩, hy.symm, rfl⟩
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset {x : Fin (2 * n) // x ≠ w}))
      (fun v => G.Adj v.1 w)
    rw [e1, Finset.card_univ] at *
    omega
  have hcol : Colorable k X := colorable_X X n k hcard h7 h3 (fun v => by
    have := hdegv v; split_ifs at this <;> omega) hW
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨C⟩ := lineGraph_coloring_of_colorable hcol
  exact coloring_of_deleteVertex G hreg (by rw [Fintype.card_fin]; exact even_two_mul n) w C

end OMA.H1

theorem OMA.solution : OMA.R_wp_1_factorization_conjecture_R1.H1 := OMA.H1.solution_H1
