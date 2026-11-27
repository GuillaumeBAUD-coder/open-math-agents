import FormalConjectures.ErdosProblems.«619»

/-!
# A diameter-five extension of a connected triangle-free graph

Choose the smaller of a maximum independent set and its complement. Each
dominates the graph. It suffices to connect the chosen centers within distance
three. For this we use the pivot construction of Erdős, Gyárfás and Ruszinkó,
Theorem 4.2, keeping track of the one pivot that costs no edge. The related
diameter-three formalization in open-math-agents PR 799 is by @amp2600.
Source: https://users.renyi.hu/~gyarfas/Cikkek/90_howtodecrease.pdf

Lean statement and proof of the diameter-five bound: @Halldon
-/

open SimpleGraph

namespace Erdos619Five

variable {V : Type*}

-- Adding one edge whose endpoints have no common neighbor preserves triangle-freeness.
private lemma far_edge (G : SimpleGraph V) (hG : G.CliqueFree 3) {p q : V}
    (hfar : 2 < G.edist p q) : (G ⊔ edge p q).CliqueFree 3 := by
  classical
  have noCommon (w : V) (hp : G.Adj p w) (hq : G.Adj q w) : False := by
    apply hfar.not_ge
    calc
      G.edist p q ≤ G.edist p w + G.edist w q := G.edist_triangle
      _ = 2 := by rw [edist_eq_one_iff_adj.mpr hp, edist_eq_one_iff_adj.mpr hq.symm]; decide
  have old {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False :=
    hG {a,b,c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := is3Clique_iff.mp ht
  have hn1 := hab.ne
  have hn2 := hac.ne
  have hn3 := hbc.ne
  simp only [sup_adj, edge_adj] at hab hac hbc
  grind [Adj.symm]

variable [Fintype V]

-- An edge added at the pivot can always be charged to its other endpoint.
-- Choose a maximal permissible extension using only edges from p into U.
private lemma pivot (G : SimpleGraph V) (hG : G.CliqueFree 3) (p : V) (U : Finset V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ K.CliqueFree 3 ∧
      (∀ y ∈ U, K.edist p y ≤ 2) ∧
      (∀ e ∈ (K \ G).edgeSet, ∃ y ∈ U, e = s(p,y)) := by
  classical
  let allowed (K : SimpleGraph V) :=
    G ≤ K ∧ K.CliqueFree 3 ∧ ∀ e ∈ (K \ G).edgeSet, ∃ y ∈ U, e = s(p,y)
  have hg : allowed G := ⟨le_rfl, hG, by simp⟩
  obtain ⟨K, -, hmax⟩ := (Set.toFinite {K | allowed K}).exists_le_maximal hg
  obtain ⟨hgk, hk, hedge⟩ := hmax.1
  refine ⟨K, hgk, hk, ?_, hedge⟩
  intro q hq
  by_contra! hfar
  let J := K ⊔ edge p q
  have hKJ : K ≤ J := le_sup_left
  have hJ : allowed J := by
    refine ⟨hgk.trans hKJ, far_edge K hk hfar, ?_⟩
    intro e he
    rw [edgeSet_sdiff] at he
    rcases he with ⟨he, hne⟩
    rw [show J = K ⊔ edge p q from rfl, edgeSet_sup] at he
    rcases he with h | h
    · exact hedge e (by rw [edgeSet_sdiff]; exact ⟨h,hne⟩)
    · exact ⟨q, hq, Set.mem_singleton_iff.mp (edgeSet_edge_subset h)⟩
  have hne : p ≠ q := by rintro rfl; simp at hfar
  have hn : ¬ K.Adj p q := fun hp => by
    rw [edist_eq_one_iff_adj.mpr hp] at hfar
    exact (by decide : ¬ (2 : ℕ∞) < 1) hfar
  have hlt : K < K ⊔ edge p q := by apply lt_sup_edge <;> assumption
  exact hlt.not_ge (hmax.2 hJ hKJ)

private lemma extension (U : Finset V) (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      (H \ G).edgeSet.ncard ≤ U.card - 1 ∧ ∀ x ∈ U, ∀ y ∈ U, H.edist x y ≤ 3 := by
  classical
  induction U using Finset.strongInductionOn generalizing G with
  | _ U ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨p, hp⟩ := hU
      obtain ⟨K,hGK,hK,hnear,hstar⟩ := pivot G hG p U
      let T := U.filter (K.Adj p)
      have hpT : p ∉ T := by simp [T]
      let R := U \ insert p T
      have hblock : insert p T ⊆ U := Finset.insert_subset hp (Finset.filter_subset _ _)
      have hsmaller : R ⊂ U := Finset.sdiff_ssubset hblock ⟨p, Finset.mem_insert_self _ _⟩
      obtain ⟨H,hKH,hH,hrest,hclose⟩ := ih R hsmaller K hK
      have hpaid : (K \ G).edgeSet ⊆ (fun y : V => s(p,y)) '' (T : Set V) := by
        intro e he
        obtain ⟨y,hy,rfl⟩ := hstar e he
        rw [edgeSet_sdiff] at he
        exact ⟨y,Finset.mem_filter.mpr ⟨hy, he.1⟩,rfl⟩
      have hcost : (K \ G).edgeSet.ncard ≤ T.card := by
        calc
          _ ≤ ((fun y : V => s(p,y)) '' (T : Set V)).ncard := Set.ncard_le_ncard hpaid
          _ ≤ T.card := by simpa only [Set.ncard_coe_finset] using
              Set.ncard_image_le (s := (T : Set V)) (f := fun y : V => s(p,y))
      have hdecomp : (H \ G).edgeSet ⊆ (H \ K).edgeSet ∪ (K \ G).edgeSet := by
        simp only [edgeSet_sdiff]
        intro e he
        by_cases h : e ∈ K.edgeSet
        · exact Or.inr ⟨h,he.2⟩
        · exact Or.inl ⟨he.1,h⟩
      have nearBlock (x) (hx : x ∈ insert p T) (y) (hy : y ∈ U) : H.edist x y ≤ 3 := by
        have hx' : K.edist x p ≤ 1 := by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · simp
          · exact edist_le_one_iff_adj_or_eq.mpr (Or.inl (Finset.mem_filter.mp hx).2.symm)
        calc
          H.edist x y ≤ K.edist x y := edist_anti hKH
          _ ≤ K.edist x p + K.edist p y := K.edist_triangle
          _ ≤ 1 + 2 := add_le_add hx' (hnear y hy)
          _ = 3 := by decide
      refine ⟨H,hGK.trans hKH,hH,?_,?_⟩
      · have hcount := Finset.card_sdiff_add_card_eq_card hblock
        change R.card + (insert p T).card = U.card at hcount
        rw [Finset.card_insert_of_notMem hpT] at hcount
        calc
          _ ≤ ((H \ K).edgeSet ∪ (K \ G).edgeSet).ncard := Set.ncard_le_ncard hdecomp
          _ ≤ (H \ K).edgeSet.ncard + (K \ G).edgeSet.ncard := Set.ncard_union_le _ _
          _ ≤ (R.card - 1) + T.card := Nat.add_le_add hrest hcost
          _ ≤ U.card - 1 := by omega
      · intro x hx y hy
        by_cases hx' : x ∈ insert p T
        · exact nearBlock x hx' y hy
        by_cases hy' : y ∈ insert p T
        · rw [SimpleGraph.edist_comm]; exact nearBlock y hy' x hx
        exact hclose x (Finset.mem_sdiff.mpr ⟨hx,hx'⟩) y (Finset.mem_sdiff.mpr ⟨hy,hy'⟩)
    · exact ⟨G,le_rfl,hG,by simp,fun x hx => (hU ⟨x,hx⟩).elim⟩

-- Either side of a maximum independent set dominates a graph without isolated vertices.
private lemma small_centers [Nontrivial V] (G : SimpleGraph V) (hc : G.Connected) :
    ∃ C : Finset V, 2 * C.card ≤ Fintype.card V ∧
      ∀ v : V, ∃ w ∈ C, G.edist v w ≤ 1 := by
  classical
  obtain ⟨S,hS⟩ := G.exists_isNIndepSet_indepNum
  have independent := hS.isIndepSet
  have cover (v : V) : ∃ w ∈ S, G.edist v w ≤ 1 := by
    by_cases h : v ∈ S
    · exact ⟨v,h,by simp⟩
    by_contra! hn
    have hnew : G.IsIndepSet (↑(insert v S : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      change (insert v (S : Set V)).Pairwise _
      rw [Set.pairwise_insert]
      refine ⟨independent, ?_⟩
      intro w hw _
      have hnot : ¬ G.Adj v w := fun ha => (hn w hw).not_ge
        (edist_le_one_iff_adj_or_eq.mpr (Or.inl ha))
      exact ⟨hnot, fun ha => hnot ha.symm⟩
    have hcard := hnew.card_le_indepNum
    rw [Finset.card_insert_of_notMem h, hS.card_eq] at hcard
    omega
  have other (v : V) : ∃ w ∈ Sᶜ, G.edist v w ≤ 1 := by
    by_cases h : v ∈ S
    · obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
      have hout : w ∉ S := fun hs => independent h hs hw.ne hw
      exact ⟨w, Finset.mem_compl.mpr hout, edist_le_one_iff_adj_or_eq.mpr (Or.inl hw)⟩
    · exact ⟨v, Finset.mem_compl.mpr h, by simp⟩
  have count := Finset.card_compl_add_card S
  by_cases hs : 2*S.card ≤ Fintype.card V
  · exact ⟨S,hs,cover⟩
  · exact ⟨Sᶜ,by omega,other⟩

end Erdos619Five

theorem OMA.solution : type_of% @Erdos619.erdos_619.variants.h_five_le := by
  classical
  intro V _ G hc hG
  letI := hc.nonempty
  rcases subsingleton_or_nontrivial V with hs | hs
  · letI := hs
    rw [Erdos619.erdos_619.test.minNewEdges_eq_zero hG (by simp [ediam_eq_zero_of_subsingleton])]
    have hn : (1 : ℝ) ≤ Fintype.card V := by
      exact_mod_cast (show 1 ≤ Fintype.card V from Fintype.card_pos)
    simp only [Nat.cast_zero]
    linarith
  · letI := hs
    obtain ⟨C, hsize, hdom⟩ := Erdos619Five.small_centers G hc
    obtain ⟨H, hGH, hH, hcost, hclose⟩ := Erdos619Five.extension C G hG
    have hdiam : H.ediam ≤ 5 := by
      rw [ediam_le_iff]
      intro x y
      obtain ⟨a,ha,hxa⟩ := hdom x
      obtain ⟨b,hb,hyb⟩ := hdom y
      calc
        H.edist x y ≤ H.edist x a + H.edist a y := H.edist_triangle
        _ ≤ H.edist x a + (H.edist a b + H.edist b y) := add_le_add le_rfl H.edist_triangle
        _ ≤ 1 + (3 + 1) := add_le_add ((edist_anti hGH).trans hxa)
            (add_le_add (hclose a ha b hb) (by rw [SimpleGraph.edist_comm]; exact (edist_anti hGH).trans hyb))
        _ = 5 := by decide
    have hmin : Erdos619.minNewEdges 5 G ≤ (H \ G).edgeSet.ncard :=
      Nat.sInf_le ⟨H, hGH, hH, hdiam, rfl⟩
    obtain ⟨w,hw,-⟩ := hdom (Classical.choice hc.nonempty)
    have hpos := Finset.card_pos.mpr (show C.Nonempty from ⟨w,hw⟩)
    have htwo : 2 * Erdos619.minNewEdges 5 G + 1 ≤ Fintype.card V := by omega
    have hr : 2 * (Erdos619.minNewEdges 5 G : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast htwo
    linarith
