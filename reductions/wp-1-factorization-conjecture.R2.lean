import OMAStatements.S_wp_1_factorization_conjecture

-- Reduction wp-1-factorization-conjecture.R2 of 1-factorization conjecture
-- Credit: @PandaWill
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The whole conjecture follows from its threshold degree k₀(n) (= n for odd n, n - 1 for even n):
--   if k ≥ k₀(n), a (k+1)-regular graph on 2n vertices has minimum degree ≥ n, hence a perfect matching
--   (proved here from Mathlib's Tutte theorem); removing it leaves a k-regular graph, and the matching
--   becomes one more colour class. Induction on k from k₀(n) gives every degree k ≥ k₀(n).
-- Proved here: that staircase, the class-1 ⇔ 1-factorization link, and the threshold for n ≤ 2 (k₀ = 1).
-- What is left, exactly the threshold case for n ≥ 3, split by parity:
--   H1: odd n ≥ 3, every n-regular graph on 2n vertices is class 1;
--   H2: even n ≥ 4, every (n - 1)-regular graph on 2n vertices is class 1.
-- Both are open in general (Csaba–Kühn–Lo–Osthus–Treglown, Mem. AMS 2016: all sufficiently large n); an
-- exhaustive computer search (nauty + exact edge-colouring) finds no counterexample for n ≤ 7.

namespace OMA.R_wp_1_factorization_conjecture_R2

open SimpleGraph

def H1 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree n → Nonempty (G.lineGraph.Coloring (Fin n))

def H2 : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n →
    ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
      G.IsRegularOfDegree (n - 1) → Nonempty (G.lineGraph.Coloring (Fin (n - 1)))

lemma factorable_of_coloring {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hG : G.IsRegularOfDegree k) (c : G.lineGraph.Coloring (Fin k)) :
    OMA.S_wp_1_factorization_conjecture.IsOneFactorable G := by
  classical
  let col : ∀ v w, G.Adj v w → Fin k := fun v w h => c ⟨s(v, w), h⟩
  have colsymm : ∀ v w (h : G.Adj v w), col w v h.symm = col v w h := by
    intro v w h; simp only [col, Sym2.eq_swap]
  let M : Fin k → G.Subgraph := fun i =>
    { verts := Set.univ
      Adj := fun v w => ∃ h : G.Adj v w, col v w h = i
      adj_sub := fun ⟨h, _⟩ => h
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun v w ⟨h, e⟩ => ⟨h.symm, (colsymm v w h).trans e⟩⟩ }
  -- the colours at a vertex are distinct
  have inj : ∀ v w w' (h : G.Adj v w) (h' : G.Adj v w'), col v w h = col v w' h' → w = w' := by
    intro v w w' h h' e
    by_contra hne
    have hadj : G.lineGraph.Adj ⟨s(v, w), h⟩ ⟨s(v, w'), h'⟩ := by
      rw [lineGraph_adj_iff_exists]
      refine ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      intro heq
      have := congrArg Subtype.val heq
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at this
      rcases this with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hne h2
      · exact hne (h2.trans h1)
    exact c.valid hadj e
  refine ⟨Fin k, M, ?_, ?_, ?_⟩
  · intro i
    rw [Subgraph.isPerfectMatching_iff]
    intro v
    let f : ∀ w, w ∈ G.neighborFinset v → Fin k := fun w hw => col v w ((mem_neighborFinset _ _ _).1 hw)
    obtain ⟨w, hw, e⟩ := Finset.surj_on_of_inj_on_of_card_le f (fun _ _ => Finset.mem_univ _)
      (fun a b ha hb hab => inj v a b _ _ hab) (by simp [card_neighborFinset_eq_degree, hG v]) i
      (Finset.mem_univ _)
    refine ⟨w, ⟨(mem_neighborFinset _ _ _).1 hw, e.symm⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    exact inj v y w hy _ (ey.trans e)
  · intro i j hij
    rw [Set.disjoint_left]
    intro e
    induction e using Sym2.ind with
    | _ v w =>
      simp only [Subgraph.mem_edgeSet]
      rintro ⟨h, hi⟩ ⟨h', hj⟩
      exact hij (hi.symm.trans hj)
  · intro e he
    induction e using Sym2.ind with
    | _ v w => exact ⟨col v w he, by simp only [Subgraph.mem_edgeSet]; exact ⟨he, rfl⟩⟩

lemma coloring_of_pair {V α : Type*} (G : SimpleGraph V) (c : V → V → α) (hs : ∀ x y, c x y = c y x)
    (hc : ∀ v y z, G.Adj v y → G.Adj v z → c v y = c v z → y = z) :
    Nonempty (G.lineGraph.Coloring α) := by
  refine ⟨Coloring.mk (fun e => Sym2.lift ⟨c, hs⟩ e.val) ?_⟩
  rintro ⟨e1, h1⟩ ⟨e2, h2⟩ hadj heq
  rw [lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hv1, hv2⟩ := hadj
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hv1
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 hv2
  simp only [Sym2.lift_mk] at heq
  obtain rfl := hc v y z h1 h2 heq
  exact hne rfl

lemma one_case {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 1) : Nonempty (G.lineGraph.Coloring (Fin 1)) :=
  coloring_of_pair G (fun _ _ => 0) (fun _ _ => rfl) fun v y z hy hz _ =>
    Finset.card_le_one.1 (by rw [card_neighborFinset_eq_degree, hG v]) y
      ((G.mem_neighborFinset _ _).2 hy) z ((G.mem_neighborFinset _ _).2 hz)



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


lemma stair {V : Type*} [Fintype V] [DecidableEq V] (N k0 : ℕ) (hV : Fintype.card V = 2 * N)
    (hk0 : N ≤ k0 + 1)
    (base : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree k0 →
      Nonempty (G.lineGraph.Coloring (Fin k0))) :
    ∀ k, k0 ≤ k → ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree k →
      Nonempty (G.lineGraph.Coloring (Fin k)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact base
  | succ k hk ih =>
    intro G _ hG
    classical
    obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_minDegree G (by rw [hV]; exact even_two_mul N)
      (fun v => by rw [hV, hG v]; omega)
    have hG' := isRegularOfDegree_sdiff G M hM hG
    simp only [Nat.add_sub_cancel] at hG'
    exact coloring_succ_of_perfectMatching G M hM (ih _ hG').some

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_factorization_conjecture.main := by
  intro h1 h2 n k hk G _ hG
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Empty, Empty.elim, fun i => i.elim, fun i => i.elim,
      fun e _ => by induction e using Sym2.ind with | _ x _ => exact x.elim0⟩
  have hV : Fintype.card (Fin (2 * n)) = 2 * n := Fintype.card_fin _
  suffices h : Nonempty (G.lineGraph.Coloring (Fin k)) from factorable_of_coloring G k hG h.some
  rcases hk with ⟨ho, hk⟩ | ⟨he, hk⟩
  · refine stair n n hV (by omega) (fun G' _ hG' => ?_) k hk G hG
    rcases (show n = 1 ∨ 3 ≤ n by rcases ho with ⟨j, rfl⟩; omega) with rfl | h3
    · exact one_case G' hG'
    · exact h1 n ho h3 G' hG'
  · refine stair n (n - 1) hV (by omega) (fun G' _ hG' => ?_) k hk G hG
    rcases (show n = 2 ∨ 4 ≤ n by rcases he with ⟨j, rfl⟩; omega) with rfl | h4
    · exact one_case G' hG'
    · exact h2 n he h4 G' hG'

end OMA.R_wp_1_factorization_conjecture_R2
