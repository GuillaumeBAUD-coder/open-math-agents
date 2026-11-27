import FormalConjectures.WrittenOnTheWallII.GraphConjecture16

-- Problem: Written on the Wall II - Conjecture 16
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture16.lean:45 (declaration WrittenOnTheWallII.GraphConjecture16.conjecture16)
-- Credit: @ronak14p (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open SimpleGraph

namespace OMA.WOWII16

universe u

section Helpers

variable {V : Type u} {G : SimpleGraph V}

private lemma two_sets [Fintype V] [DecidableEq V] {A B : Finset V} (hA : G.IsIndepSet (A : Set V))
    (hB : G.IsIndepSet (B : Set V)) (hd : Disjoint A B) :
    A.card + B.card ≤ G.largestInducedBipartiteSubgraphSize := by
  classical
  have hb : (G.induce (↑(A ∪ B) : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring G _).mpr
    refine ⟨fun v => if v ∈ A then 0 else 1, ?_⟩
    intro v hv w hw h
    by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A
    · exact False.elim (hA hvA hwA h.ne h)
    · simp [hvA, hwA]
    · simp [hvA, hwA]
    · exact False.elim (hB ((Finset.mem_union.mp hv).resolve_left hvA)
        ((Finset.mem_union.mp hw).resolve_left hwA) h.ne h)
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨z, _, hz⟩ => hz ▸ z.card_le_univ⟩
  · exact ⟨A ∪ B, hb, Finset.card_union_of_disjoint hd⟩

private lemma adj_dist_eq_one {x y : V} (h : G.Adj x y) : G.dist x y = 1 := by
  have hle : G.dist x y ≤ 1 := by
    simpa using SimpleGraph.dist_le (Walk.cons h Walk.nil)
  have hne : G.dist x y ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := h.reachable.exists_walk_length_eq_dist
    rw [h0] at hp
    cases p with
    | nil => exact h.ne rfl
    | cons _ _ => simp at hp
  omega

private lemma dist_tri_reach {a b c : V} (hab : G.Reachable a b) (hbc : G.Reachable b c) :
    G.dist a c ≤ G.dist a b + G.dist b c := by
  obtain ⟨p, hp⟩ := hab.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hbc.exists_walk_length_eq_dist
  have h := SimpleGraph.dist_le (p.append q)
  simp only [Walk.length_append] at h
  omega

private lemma dist_pred (hc : G.Connected) {a x : V} (hx : 1 ≤ G.dist a x) :
    ∃ y : V, G.Adj y x ∧ G.dist a y + 1 = G.dist a x := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a x
  have hpos : 0 < p.length := by omega
  let i := p.length - 1
  have hi : i + 1 = p.length := by dsimp [i]; omega
  have he := p.adj_getVert_succ (show i < p.length by omega)
  rw [hi, p.getVert_length] at he
  refine ⟨p.getVert i, he, ?_⟩
  have hv := length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  rw [Walk.take_length, Nat.min_eq_left (by omega)] at hv
  omega

private lemma dist_succ (hc : G.Connected) {a x : V} (hx : 1 ≤ G.dist a x) :
    ∃ y : V, G.Adj a y ∧ G.dist y x + 1 = G.dist a x := by
  rw [SimpleGraph.dist_comm] at hx ⊢
  obtain ⟨y, hy, hd⟩ := dist_pred hc hx
  exact ⟨y, hy.symm, by rw [SimpleGraph.dist_comm]; exact hd⟩

private lemma dist_triangle_adj (hc : G.Connected) (a : V) {x y : V} (h : G.Adj x y) :
    G.dist a y ≤ G.dist a x + 1 := by
  have h1 := dist_tri_reach (hc a x) (hc x y)
  rw [adj_dist_eq_one h] at h1
  exact h1

/-- Vertices of the contraction of `N_G[v]` to `v`. -/
private abbrev ContractV (G : SimpleGraph V) (v : V) :=
  { u : V // u = v ∨ 2 ≤ G.dist v u }

private def contractV0 (G : SimpleGraph V) (v : V) : ContractV G v :=
  ⟨v, Or.inl rfl⟩

/-- The graph obtained by contracting `N_G[v]` into a single vertex `v`. -/
private def contractGraph (G : SimpleGraph V) (v : V) : SimpleGraph (ContractV G v) where
  Adj x y :=
    (x.val = v ∧ G.dist v y.val = 2) ∨
    (y.val = v ∧ G.dist v x.val = 2) ∨
    (x.val ≠ v ∧ y.val ≠ v ∧ G.Adj x.val y.val)
  symm := ⟨by
    intro x y h
    rcases h with h | h | ⟨hx, hy, hadj⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hy, hx, hadj.symm⟩)⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨hx, hd⟩ | ⟨hx, hd⟩ | ⟨_, _, hadj⟩
    · rw [hx, SimpleGraph.dist_self] at hd; omega
    · rw [hx, SimpleGraph.dist_self] at hd; omega
    · exact hadj.ne rfl⟩

private lemma contract_reach_and_dist_le (hc : G.Connected) (v : V) :
    ∀ k : ℕ, ∀ x : ContractV G v, G.dist v x.val = k →
      (contractGraph G v).Reachable (contractV0 G v) x ∧
      (x ≠ contractV0 G v → (contractGraph G v).dist (contractV0 G v) x + 1 ≤ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hxk
    by_cases hxv : x.val = v
    · have hx0 : x = contractV0 G v := Subtype.ext hxv
      subst hx0
      exact ⟨Reachable.refl _, fun h => (h rfl).elim⟩
    · have hge2 : 2 ≤ k := by
        rcases x.prop with h | h
        · exact (hxv h).elim
        · omega
      by_cases hk2 : k = 2
      · have hadj : (contractGraph G v).Adj (contractV0 G v) x :=
          Or.inl ⟨rfl, by omega⟩
        refine ⟨hadj.reachable, fun _ => ?_⟩
        rw [adj_dist_eq_one hadj]
        omega
      · obtain ⟨y, hyx, hyd⟩ := dist_pred hc (show 1 ≤ G.dist v x.val by omega)
        have hy2 : 2 ≤ G.dist v y := by omega
        have hyv : y ≠ v := by
          intro h; subst h; rw [SimpleGraph.dist_self] at hy2; omega
        let y' : ContractV G v := ⟨y, Or.inr hy2⟩
        have hy_ne : y' ≠ contractV0 G v := fun h => hyv (congrArg Subtype.val h)
        obtain ⟨hry, hdy⟩ := ih (G.dist v y) (by omega) y' rfl
        have hadj : (contractGraph G v).Adj y' x := Or.inr (Or.inr ⟨hyv, hxv, hyx⟩)
        refine ⟨hry.trans hadj.reachable, fun _ => ?_⟩
        have htri := dist_tri_reach hry hadj.reachable
        have hle := hdy hy_ne
        rw [adj_dist_eq_one hadj] at htri
        omega

private lemma contract_connected (hc : G.Connected) (v : V) :
    (contractGraph G v).Connected := by
  have : Nonempty (ContractV G v) := ⟨contractV0 G v⟩
  refine ⟨fun x y => ?_⟩
  have hx := (contract_reach_and_dist_le hc v (G.dist v x.val) x rfl).1
  have hy := (contract_reach_and_dist_le hc v (G.dist v y.val) y rfl).1
  exact hx.symm.trans hy

private lemma contract_dist_ge_aux (hc : G.Connected) (v : V) :
    ∀ {b a : ContractV G v} (p : (contractGraph G v).Walk b a),
      a = contractV0 G v → b ≠ contractV0 G v → G.dist v b.val ≤ p.length + 1 := by
  intro b a p
  induction p with
  | nil =>
    intro ha hb
    exact (hb ha).elim
  | @cons b c a hadj q ih =>
    intro ha hb
    by_cases hc0 : c = contractV0 G v
    · have h2 : G.dist v b.val = 2 := by
        rcases hadj with ⟨hbv, _⟩ | ⟨_, h2⟩ | ⟨_, hcv, _⟩
        · exact (hb (Subtype.ext hbv)).elim
        · exact h2
        · exact (hcv (congrArg Subtype.val hc0)).elim
      simp only [Walk.length_cons]
      omega
    · have hbv : b.val ≠ v := fun h => hb (Subtype.ext h)
      have hcv : c.val ≠ v := fun h => hc0 (Subtype.ext h)
      have hgad : G.Adj c.val b.val := by
        rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h⟩
        · exact (hbv h1).elim
        · exact (hcv h1).elim
        · exact h.symm
      have hq := ih ha hc0
      have htri := dist_triangle_adj hc v hgad
      simp only [Walk.length_cons]
      omega

private lemma contract_dist_v0 (hc : G.Connected) (v : V) {x : ContractV G v}
    (hx : x ≠ contractV0 G v) :
    (contractGraph G v).dist (contractV0 G v) x + 1 = G.dist v x.val := by
  have h1 := (contract_reach_and_dist_le hc v (G.dist v x.val) x rfl).2 hx
  obtain ⟨p, hp⟩ := (contract_connected hc v).exists_walk_length_eq_dist x (contractV0 G v)
  have h2 := contract_dist_ge_aux hc v p rfl hx
  rw [SimpleGraph.dist_comm] at hp
  omega

private lemma contract_walk_avoid_v0 (hc : G.Connected) (v : V) :
    ∀ {a b : ContractV G v} (p : (contractGraph G v).Walk a b),
      contractV0 G v ∉ p.support → G.dist a.val b.val ≤ p.length := by
  intro a b p
  induction p with
  | nil =>
    intro _; simp
  | @cons a c b hadj q ih =>
    intro hnot
    have ha0 : a ≠ contractV0 G v := fun h => hnot (by simp [h])
    have hc0 : c ≠ contractV0 G v := fun h =>
      hnot (by rw [Walk.support_cons, List.mem_cons]; exact Or.inr (h ▸ q.start_mem_support))
    have hq0 : contractV0 G v ∉ q.support := fun h => hnot (by simp [h])
    have hav : a.val ≠ v := fun h => ha0 (Subtype.ext h)
    have hcv : c.val ≠ v := fun h => hc0 (Subtype.ext h)
    have hgad : G.Adj a.val c.val := by
      rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h⟩
      · exact (hav h1).elim
      · exact (hcv h1).elim
      · exact h
    have hih := ih hq0
    have htri := dist_tri_reach (hc a.val c.val) (hc c.val b.val)
    rw [adj_dist_eq_one hgad] at htri
    simp only [Walk.length_cons]
    omega

private lemma contract_radius (hc : G.Connected) {s : ℕ} (hs : 2 ≤ s)
    (hr : ∀ u : V, ∃ w : V, s ≤ G.dist u w) (v : V) :
    ∀ c : ContractV G v, ∃ u : ContractV G v, s - 1 ≤ (contractGraph G v).dist c u := by
  classical
  intro c
  by_contra hcon
  push Not at hcon
  have hle : ∀ u : ContractV G v, (contractGraph G v).dist c u ≤ s - 2 := fun u => by
    have := hcon u; omega
  by_cases hc0 : c = contractV0 G v
  · subst hc0
    obtain ⟨w, hw⟩ := hr v
    let w' : ContractV G v := ⟨w, Or.inr (by omega)⟩
    have hw_ne : w' ≠ contractV0 G v := by
      intro h
      have : w = v := congrArg Subtype.val h
      subst this; rw [SimpleGraph.dist_self] at hw; omega
    have hd := contract_dist_v0 hc v hw_ne
    change (contractGraph G v).dist (contractV0 G v) w' + 1 = G.dist v w at hd
    have := hle w'
    omega
  · have hc2 : 2 ≤ G.dist v c.val := by
      rcases c.prop with h | h
      · exact (hc0 (Subtype.ext h)).elim
      · exact h
    obtain ⟨z, hzc, hzd⟩ := dist_pred hc (show 1 ≤ G.dist v c.val by omega)
    have hcd0 : (contractGraph G v).dist (contractV0 G v) c = G.dist v z := by
      have := contract_dist_v0 hc v hc0
      omega
    obtain ⟨w, hw⟩ := hr z
    have hzw : G.dist z w ≤ s - 1 := by
      by_cases hwv : w = v
      · rw [hwv, SimpleGraph.dist_comm, ← hcd0, SimpleGraph.dist_comm]
        have := hle (contractV0 G v)
        omega
      · by_cases hw1 : G.dist v w = 1
        · have htri := dist_tri_reach (hc z v) (hc v w)
          rw [SimpleGraph.dist_comm (u := z) (v := v), ← hcd0,
            SimpleGraph.dist_comm (u := contractV0 G v) (v := c)] at htri
          have := hle (contractV0 G v)
          omega
        · have hw_pos : 1 ≤ G.dist v w := by
            by_contra h0
            have : G.dist v w = 0 := by omega
            exact hwv ((hc.dist_eq_zero_iff.mp this).symm)
          have hw2 : 2 ≤ G.dist v w := by omega
          let w' : ContractV G v := ⟨w, Or.inr hw2⟩
          have hw_ne : w' ≠ contractV0 G v := fun h => hwv (congrArg Subtype.val h)
          obtain ⟨p, hp⟩ := (contract_connected hc v).exists_walk_length_eq_dist c w'
          have hplen : p.length ≤ s - 2 := by rw [hp]; exact hle w'
          by_cases hmem : contractV0 G v ∈ p.support
          · let p1 := p.takeUntil (contractV0 G v) hmem
            let p2 := p.dropUntil (contractV0 G v) hmem
            have hsum : p1.length + p2.length = p.length := by
              rw [← Walk.length_append, Walk.take_spec]
            have h1 : (contractGraph G v).dist c (contractV0 G v) ≤ p1.length :=
              SimpleGraph.dist_le p1
            have h2 : (contractGraph G v).dist (contractV0 G v) w' ≤ p2.length :=
              SimpleGraph.dist_le p2
            have hd2 := contract_dist_v0 hc v hw_ne
            change (contractGraph G v).dist (contractV0 G v) w' + 1 = G.dist v w at hd2
            have htri := dist_tri_reach (hc z v) (hc v w)
            rw [SimpleGraph.dist_comm (u := z) (v := v), ← hcd0,
              SimpleGraph.dist_comm (u := contractV0 G v) (v := c)] at htri
            omega
          · have hcw := contract_walk_avoid_v0 hc v p hmem
            change G.dist c.val w ≤ p.length at hcw
            have htri := dist_tri_reach (hc z c.val) (hc c.val w)
            rw [adj_dist_eq_one hzc] at htri
            omega
    omega

private lemma contract_card_lt [Fintype V] (hc : G.Connected) {s : ℕ} (hs : 2 ≤ s)
    (hr : ∃ w : V, s ≤ G.dist v w)
    [DecidablePred fun u : V => u = v ∨ 2 ≤ G.dist v u] :
    Fintype.card (ContractV G v) < Fintype.card V := by
  obtain ⟨w, hw⟩ := hr
  obtain ⟨u, hvu, _⟩ := dist_succ hc (show 1 ≤ G.dist v w by omega)
  have hu_not : ¬ (u = v ∨ 2 ≤ G.dist v u) := by
    rintro (rfl | h2)
    · exact hvu.ne rfl
    · rw [adj_dist_eq_one hvu] at h2; omega
  exact Fintype.card_subtype_lt hu_not

private lemma lift_from_contraction [DecidableEq V] (hc : G.Connected) (v : V)
    {I : Finset V} (hI_ind : G.IsIndepSet (I : Set V)) (hI_adj : ∀ x ∈ I, G.Adj v x)
    {X Y : Finset (ContractV G v)}
    (hvY : contractV0 G v ∈ Y) (hdisj : Disjoint X Y)
    (hX : (contractGraph G v).IsIndepSet (X : Set (ContractV G v)))
    (hY : (contractGraph G v).IsIndepSet (Y : Set (ContractV G v))) :
    ∃ A B : Finset V, v ∈ A ∧ Disjoint A B ∧
      G.IsIndepSet (A : Set V) ∧ G.IsIndepSet (B : Set V) ∧
      A.card + B.card = I.card + X.card + Y.card := by
  classical
  let emb : ContractV G v ↪ V := Function.Embedding.subtype _
  let Y' : Finset (ContractV G v) := Y.erase (contractV0 G v)
  let A : Finset V := insert v (X.map emb)
  let B : Finset V := I ∪ (Y'.map emb)
  have hX_ge2 : ∀ x ∈ X, 2 ≤ G.dist v x.val := by
    intro x hx
    rcases x.prop with hxv | h2
    · exfalso
      have : x = contractV0 G v := Subtype.ext hxv
      subst this
      exact Finset.disjoint_left.mp hdisj hx hvY
    · exact h2
  have hY'_ge3 : ∀ y ∈ Y', 3 ≤ G.dist v y.val := by
    intro y hy
    have hne : y ≠ contractV0 G v := (Finset.mem_erase.mp hy).1
    have hyY : y ∈ Y := (Finset.mem_erase.mp hy).2
    have h2 : 2 ≤ G.dist v y.val := by
      rcases y.prop with hyv | h2
      · exact (hne (Subtype.ext hyv)).elim
      · exact h2
    have hne2 : G.dist v y.val ≠ 2 := by
      intro heq
      have hadj : (contractGraph G v).Adj (contractV0 G v) y := Or.inl ⟨rfl, heq⟩
      exact hY hvY hyY hne.symm hadj
    omega
  have hv_not_X : v ∉ X.map emb := by
    intro h
    obtain ⟨x, hx, hxv⟩ := Finset.mem_map.mp h
    have h2 := hX_ge2 x hx
    change x.val = v at hxv
    rw [hxv, SimpleGraph.dist_self] at h2
    omega
  have hI_disj_Y' : Disjoint I (Y'.map emb) := by
    apply Finset.disjoint_left.mpr
    intro u huI huY
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp huY
    dsimp only [emb, Function.Embedding.subtype_apply] at huI
    have h3 := hY'_ge3 y hy
    have h1 := adj_dist_eq_one (hI_adj y.val huI)
    omega
  refine ⟨A, B, Finset.mem_insert_self v _, ?_, ?_, ?_, ?_⟩
  · -- Disjoint A B
    apply Finset.disjoint_left.mpr
    intro u huA huB
    rcases Finset.mem_insert.mp huA with huv | huX
    · rw [huv] at huB
      rcases Finset.mem_union.mp huB with hvI | hvY'
      · exact (hI_adj v hvI).ne rfl
      · obtain ⟨y, hy, hyv⟩ := Finset.mem_map.mp hvY'
        have h3 := hY'_ge3 y hy
        change y.val = v at hyv
        rw [hyv, SimpleGraph.dist_self] at h3
        omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp huX
      rcases Finset.mem_union.mp huB with hxI | hxY'
      · dsimp only [emb, Function.Embedding.subtype_apply] at hxI
        have h2 := hX_ge2 x hx
        have h1 := adj_dist_eq_one (hI_adj x.val hxI)
        omega
      · obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hxY'
        have : y = x := Subtype.ext hyx
        subst this
        exact Finset.disjoint_left.mp hdisj hx (Finset.mem_erase.mp hy).2
  · -- G.IsIndepSet A
    intro a ha b hb hne hadj
    rcases Finset.mem_insert.mp ha with rfl | haX <;>
    rcases Finset.mem_insert.mp hb with rfl | hbX
    · exact hne rfl
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hbX
      dsimp only [emb, Function.Embedding.subtype_apply] at hadj
      have h2 := hX_ge2 y hy
      have h1 := adj_dist_eq_one hadj
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haX
      dsimp only [emb, Function.Embedding.subtype_apply] at hadj
      have h2 := hX_ge2 x hx
      have h1 := adj_dist_eq_one hadj.symm
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haX
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hbX
      dsimp only [emb, Function.Embedding.subtype_apply] at hne hadj
      have hxne : x.val ≠ v := by
        intro h; have h2 := hX_ge2 x hx; rw [h, SimpleGraph.dist_self] at h2; omega
      have hyne : y.val ≠ v := by
        intro h; have h2 := hX_ge2 y hy; rw [h, SimpleGraph.dist_self] at h2; omega
      have hadjH : (contractGraph G v).Adj x y := Or.inr (Or.inr ⟨hxne, hyne, hadj⟩)
      exact hX hx hy (fun h => hne (congrArg Subtype.val h)) hadjH
  · -- G.IsIndepSet B
    intro a ha b hb hne hadj
    rcases Finset.mem_union.mp ha with haI | haY <;>
    rcases Finset.mem_union.mp hb with hbI | hbY
    · exact hI_ind haI hbI hne hadj
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hbY
      dsimp only [emb, Function.Embedding.subtype_apply] at hadj
      have h3 := hY'_ge3 y hy
      have h1 := adj_dist_eq_one (hI_adj a haI)
      have htri := dist_triangle_adj hc v hadj
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haY
      dsimp only [emb, Function.Embedding.subtype_apply] at hadj
      have h3 := hY'_ge3 x hx
      have h1 := adj_dist_eq_one (hI_adj b hbI)
      have htri := dist_triangle_adj hc v hadj.symm
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp haY
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hbY
      dsimp only [emb, Function.Embedding.subtype_apply] at hne hadj
      have hxne : x.val ≠ v := by
        intro h; have h3 := hY'_ge3 x hx; rw [h, SimpleGraph.dist_self] at h3; omega
      have hyne : y.val ≠ v := by
        intro h; have h3 := hY'_ge3 y hy; rw [h, SimpleGraph.dist_self] at h3; omega
      have hadjH : (contractGraph G v).Adj x y := Or.inr (Or.inr ⟨hxne, hyne, hadj⟩)
      exact hY (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hy).2
        (fun h => hne (congrArg Subtype.val h)) hadjH
  · -- Cardinality
    have hAcard : A.card = X.card + 1 := by
      rw [Finset.card_insert_of_notMem hv_not_X, Finset.card_map]
    have hBcard : B.card = I.card + Y'.card := by
      rw [Finset.card_union_of_disjoint hI_disj_Y', Finset.card_map]
    have hY'card : Y'.card + 1 = Y.card := Finset.card_erase_add_one hvY
    omega

private lemma swap_simplicial [DecidableEq V] {v : V}
    (hclique : ∀ x y : V, G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y)
    {A B : Finset V} (hdisj : Disjoint A B)
    (hA : G.IsIndepSet (A : Set V)) (hB : G.IsIndepSet (B : Set V)) :
    ∃ A' B' : Finset V, v ∈ A' ∧ Disjoint A' B' ∧
      G.IsIndepSet (A' : Set V) ∧ G.IsIndepSet (B' : Set V) ∧
      A.card + B.card ≤ A'.card + B'.card := by
  classical
  by_cases hvA : v ∈ A
  · exact ⟨A, B, hvA, hdisj, hA, hB, le_rfl⟩
  by_cases hvB : v ∈ B
  · exact ⟨B, A, hvB, hdisj.symm, hB, hA, by omega⟩
  let AN : Finset V := A.filter (fun x => G.Adj v x)
  have hAN_le : AN.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hA hx'.1 hy'.1 hne (hclique x y hx'.2 hy'.2 hne)
  let A' : Finset V := insert v (A \ AN)
  have hv_not : v ∉ A \ AN := fun h => hvA (Finset.mem_sdiff.mp h).1
  refine ⟨A', B, Finset.mem_insert_self v _, ?_, ?_, hB, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro u huA' huB
    rcases Finset.mem_insert.mp huA' with rfl | hu
    · exact hvB huB
    · exact Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mp hu).1 huB
  · intro x hx y hy hne hadj
    rcases Finset.mem_insert.mp hx with rfl | hx' <;>
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact hne rfl
    · have := Finset.mem_sdiff.mp hy'
      exact this.2 (Finset.mem_filter.mpr ⟨this.1, hadj⟩)
    · have := Finset.mem_sdiff.mp hx'
      exact this.2 (Finset.mem_filter.mpr ⟨this.1, hadj.symm⟩)
    · exact hA (Finset.mem_sdiff.mp hx').1 (Finset.mem_sdiff.mp hy').1 hne hadj
  · have hA'card : A'.card = (A \ AN).card + 1 := Finset.card_insert_of_notMem hv_not
    have hsub : AN ⊆ A := Finset.filter_subset _ _
    have hsdiff : (A \ AN).card + AN.card = A.card := Finset.card_sdiff_add_card_eq_card hsub
    omega

private lemma shortest_walk_avoids_simplicial {v : V}
    (hclique : ∀ x y : V, G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y)
    {a b : V} (ha : a ≠ v) (hb : b ≠ v)
    (p : G.Walk a b) (hp : p.length = G.dist a b) :
    v ∉ p.support := by
  classical
  intro hv
  let p1 := p.takeUntil v hv
  let p2 := p.dropUntil v hv
  have hsum : p1.length + p2.length = p.length := by
    rw [← Walk.length_append, Walk.take_spec]
  cases hp1 : p1.reverse with
  | nil =>
    exact ha rfl
  | @cons _ a1 _ hva1 q1 =>
    cases hp2 : p2 with
    | nil =>
      exact hb rfl
    | @cons _ b1 _ hvb1 q2 =>
      have hlen1 : p1.length = q1.length + 1 := by
        have := congrArg Walk.length hp1
        simp only [Walk.length_reverse, Walk.length_cons] at this
        exact this
      have hlen2 : p2.length = q2.length + 1 := by
        have := congrArg Walk.length hp2
        simp only [Walk.length_cons] at this
        exact this
      by_cases hab1 : a1 = b1
      · subst hab1
        let q : G.Walk a b := q1.reverse.append q2
        have hq : G.dist a b ≤ q.length := SimpleGraph.dist_le q
        have hqlen : q.length = q1.length + q2.length := by
          simp [q]
        omega
      · have hadj12 : G.Adj a1 b1 := hclique a1 b1 hva1 hvb1 hab1
        let q : G.Walk a b := q1.reverse.append (Walk.cons hadj12 q2)
        have hq : G.dist a b ≤ q.length := SimpleGraph.dist_le q
        have hqlen : q.length = q1.length + (q2.length + 1) := by
          simp [q]
        omega

private lemma lift_walk_induce_ne (v : V) :
    ∀ {x y : V} (p : G.Walk x y) (hx : x ≠ v) (hy : y ≠ v),
      v ∉ p.support →
      ∃ q : (G.induce { u : V | u ≠ v }).Walk ⟨x, hx⟩ ⟨y, hy⟩, q.length = p.length := by
  intro x y p
  induction p with
  | nil =>
    intro hx hy _
    exact ⟨Walk.nil, rfl⟩
  | @cons x y z hxy r ih =>
    intro hx hz hnot
    have hy : y ≠ v := fun h =>
      hnot (by rw [Walk.support_cons, List.mem_cons]; exact Or.inr (h ▸ r.start_mem_support))
    have hr : v ∉ r.support := fun h => hnot (by simp [h])
    obtain ⟨q, hq⟩ := ih hy hz hr
    refine ⟨Walk.cons (show (G.induce { u : V | u ≠ v }).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy) q, ?_⟩
    simp [hq]

private lemma proj_walk_induce_ne (hc : G.Connected) (v : V) :
    ∀ {a b : { u : V // u ≠ v }} (q : (G.induce { u : V | u ≠ v }).Walk a b),
      G.dist a.val b.val ≤ q.length := by
  intro a b q
  induction q with
  | nil => simp [SimpleGraph.dist_self]
  | @cons x y z hxy r ih =>
    have htri := dist_tri_reach (hc x.val y.val) (hc y.val z.val)
    rw [adj_dist_eq_one (show G.Adj x.val y.val from hxy)] at htri
    simp only [Walk.length_cons]
    omega

private lemma delete_simplicial_connected_dist (hc : G.Connected) {v : V}
    (hclique : ∀ x y : V, G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y)
    (hne : Nonempty { u : V // u ≠ v }) :
    let G' := G.induce { u : V | u ≠ v }
    G'.Connected ∧ ∀ x y : { u : V // u ≠ v }, G'.dist x y = G.dist x.val y.val := by
  intro G'
  have : Nonempty { u : V | u ≠ v } := hne
  have hreach : ∀ x y : { u : V // u ≠ v },
      ∃ q : G'.Walk x y, q.length = G.dist x.val y.val := by
    intro x y
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x.val y.val
    have hv := shortest_walk_avoids_simplicial hclique x.prop y.prop p hp
    obtain ⟨q, hq⟩ := lift_walk_induce_ne v p x.prop y.prop hv
    exact ⟨q, hq.trans hp⟩
  have hc' : G'.Connected := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨q, _⟩ := hreach x y
    exact q.reachable
  refine ⟨hc', fun x y => ?_⟩
  apply le_antisymm
  · obtain ⟨q, hq⟩ := hreach x y
    exact hq ▸ SimpleGraph.dist_le q
  · obtain ⟨q, hq⟩ := hc'.exists_walk_length_eq_dist x y
    exact hq ▸ proj_walk_induce_ne hc v q

private lemma master_aux :
    ∀ n : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), G.Connected → ∀ (s : ℕ), 1 ≤ s →
      (∀ u : V, ∃ w : V, s ≤ G.dist u w) → ∀ (v : V),
      Fintype.card V = n →
      ∃ A B : Finset V, v ∈ A ∧ Disjoint A B ∧
        G.IsIndepSet (A : Set V) ∧ G.IsIndepSet (B : Set V) ∧
        2 * s ≤ A.card + B.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hc s hs hr v hcard
    classical
    by_cases hs1 : s = 1
    · subst hs1
      obtain ⟨w, hw⟩ := hr v
      obtain ⟨u, hvu, _⟩ := dist_succ hc hw
      refine ⟨{v}, {u}, Finset.mem_singleton_self v, ?_, ?_, ?_, ?_⟩
      · exact Finset.disjoint_singleton.mpr hvu.ne
      · intro a ha b hb hne; simp at ha hb; subst ha; subst hb; exact (hne rfl).elim
      · intro a ha b hb hne; simp at ha hb; subst ha; subst hb; exact (hne rfl).elim
      · simp
    · have hs2 : 2 ≤ s := by omega
      -- Helper: if some vertex `z` has two nonadjacent neighbors, build `(A, B)` of size ≥ 2*s.
      have from_nonclique : ∀ z : V,
          (∃ w1 w2 : V, G.Adj z w1 ∧ G.Adj z w2 ∧ w1 ≠ w2 ∧ ¬ G.Adj w1 w2) →
          ∃ A B : Finset V, z ∈ A ∧ Disjoint A B ∧
            G.IsIndepSet (A : Set V) ∧ G.IsIndepSet (B : Set V) ∧
            2 * s ≤ A.card + B.card := by
        intro z ⟨w1, w2, hzw1, hzw2, hne12, hnadj12⟩
        let H := contractGraph G z
        have hHc := contract_connected hc z
        have hHr := contract_radius hc hs2 hr z
        have hlt : Fintype.card (ContractV G z) < n := hcard ▸ contract_card_lt hc hs2 (hr z)
        obtain ⟨Y_H, X_H, hzY, hdisjH, hY_H, hX_H, hszH⟩ :=
          ih (Fintype.card (ContractV G z)) hlt H hHc (s - 1) (by omega) hHr (contractV0 G z) rfl
        let I : Finset V := {w1, w2}
        have hI_ind : G.IsIndepSet (I : Set V) := by
          intro a ha b hb hne hadj
          simp only [I, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact hne rfl
          · exact hnadj12 hadj
          · exact hnadj12 hadj.symm
          · exact hne rfl
        have hI_adj : ∀ x ∈ I, G.Adj z x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hzw1
          · rw [Finset.mem_singleton.mp hx]; exact hzw2
        have hI_card : I.card = 2 := Finset.card_pair hne12
        obtain ⟨A, B, hzA, hdisj, hA, hB, hsz⟩ :=
          lift_from_contraction hc z hI_ind hI_adj hzY hdisjH.symm hX_H hY_H
        refine ⟨A, B, hzA, hdisj, hA, hB, ?_⟩
        omega
      by_cases hcl : ∀ x y : V, G.Adj v x → G.Adj v y → x ≠ y → G.Adj x y
      · -- Case 2: N_G(v) is a clique (v is simplicial)
        let V' := { u : V // u ≠ v }
        have hV'_nonempty : Nonempty V' := by
          obtain ⟨w, hw⟩ := hr v
          refine ⟨⟨w, ?_⟩⟩
          intro h; subst h; rw [SimpleGraph.dist_self] at hw; omega
        obtain ⟨hc', hdist'⟩ := delete_simplicial_connected_dist hc hcl hV'_nonempty
        let G' := G.induce { u : V | u ≠ v }
        by_cases hrad' : ∀ x : V', ∃ y : V', s ≤ G'.dist x y
        · -- Subcase 2a: rad(G - v) ≥ s
          obtain ⟨x0⟩ := hV'_nonempty
          have hlt : Fintype.card V' < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (show ¬ (v ≠ v) by simp)
          obtain ⟨A', B', _, hdisj', hA', hB', hsz'⟩ :=
            ih (Fintype.card V') hlt G' hc' s hs hrad' x0 rfl
          let emb : V' ↪ V := Function.Embedding.subtype _
          let A : Finset V := A'.map emb
          let B : Finset V := B'.map emb
          have hdisj : Disjoint A B := Finset.disjoint_map emb |>.mpr hdisj'
          have hA : G.IsIndepSet (A : Set V) := by
            intro a ha b hb hne hadj
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
            obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
            exact hA' hx hy (fun h => hne (congrArg Subtype.val h)) hadj
          have hB : G.IsIndepSet (B : Set V) := by
            intro a ha b hb hne hadj
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
            obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
            exact hB' hx hy (fun h => hne (congrArg Subtype.val h)) hadj
          obtain ⟨A'', B'', hvA'', hdisj'', hA'', hB'', hsz''⟩ :=
            swap_simplicial hcl hdisj hA hB
          refine ⟨A'', B'', hvA'', hdisj'', hA'', hB'', ?_⟩
          simp only [A, B, Finset.card_map] at hsz''
          omega
        · -- Subcase 2b: rad(G - v) < s, so some c ≠ v has dist(c, v) = s and dist(c, u) ≤ s - 1 for u ≠ v
          push Not at hrad'
          obtain ⟨c, hc_lt⟩ := hrad'
          have hc_other : ∀ u : V, u ≠ v → G.dist c.val u ≤ s - 1 := by
            intro u hu
            have h := hc_lt ⟨u, hu⟩
            rw [hdist' c ⟨u, hu⟩] at h
            dsimp only at h
            omega
          have hcv_ge : s ≤ G.dist c.val v := by
            obtain ⟨w, hw⟩ := hr c.val
            by_cases hwv : w = v
            · subst hwv; exact hw
            · have := hc_other w hwv; omega
          have hcv_eq : G.dist c.val v = s := by
            obtain ⟨w0, hw0⟩ := hr v
            obtain ⟨x0, hvx0, _⟩ := dist_succ hc (show 1 ≤ G.dist v w0 by omega)
            have hcx0 := hc_other x0 hvx0.ne.symm
            have htri := dist_triangle_adj hc c.val hvx0.symm
            omega
          -- N_G(c) cannot be a clique
          have hc_nonclique : ∃ w1 w2 : V,
              G.Adj c.val w1 ∧ G.Adj c.val w2 ∧ w1 ≠ w2 ∧ ¬ G.Adj w1 w2 := by
            by_contra hnc
            have hcc : ∀ x y : V, G.Adj c.val x → G.Adj c.val y → x ≠ y → G.Adj x y := by
              intro x y hx hy hne
              by_contra hnadj
              exact hnc ⟨x, y, hx, hy, hne, hnadj⟩
            obtain ⟨w, hcw, hwd⟩ := dist_succ hc (show 1 ≤ G.dist c.val v by omega)
            obtain ⟨u, hu⟩ := hr w
            have hwu : G.dist w u ≤ s - 1 := by
              by_cases huv : u = v
              · subst huv; omega
              · by_cases huc : u = c.val
                · subst huc; rw [adj_dist_eq_one hcw.symm]; omega
                · have hcu_pos : 1 ≤ G.dist c.val u := by
                    by_contra h0
                    have : G.dist c.val u = 0 := by omega
                    exact huc ((hc.dist_eq_zero_iff.mp this).symm)
                  have hcu_le : G.dist c.val u ≤ s - 1 := hc_other u huv
                  obtain ⟨x1, hcx1, hx1d⟩ := dist_succ hc hcu_pos
                  by_cases hwx1 : w = x1
                  · subst hwx1; omega
                  · have hadj := hcc w x1 hcw hcx1 hwx1
                    have htri := dist_tri_reach (hc w x1) (hc x1 u)
                    rw [adj_dist_eq_one hadj] at htri
                    omega
            omega
          obtain ⟨A, B, _, hdisj, hA, hB, hsz⟩ := from_nonclique c.val hc_nonclique
          obtain ⟨A', B', hvA', hdisj', hA', hB', hsz'⟩ :=
            swap_simplicial hcl hdisj hA hB
          exact ⟨A', B', hvA', hdisj', hA', hB', le_trans hsz hsz'⟩
      · -- Case 1: N_G(v) is not a clique
        have hv_nonclique : ∃ w1 w2 : V, G.Adj v w1 ∧ G.Adj v w2 ∧ w1 ≠ w2 ∧ ¬ G.Adj w1 w2 := by
          push Not at hcl
          exact hcl
        exact from_nonclique v hv_nonclique

end Helpers

end OMA.WOWII16

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture16.conjecture16 := by
  intro V _ _ _ G hc
  classical
  let vals := Finset.univ.image (fun v => indepNeighborsCard G v)
  have hvals : vals.Nonempty := by simp [vals]
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp (vals.max'_mem hvals)
  let r := G.radius.toNat
  have htop : G.radius ≠ ⊤ := G.radius_ne_top_iff.mpr hc
  have hr_pos : 1 ≤ r := by
    obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
    have hne0 : G.radius ≠ 0 := hu ▸ G.eccent_ne_zero u
    have : r ≠ 0 := by
      simp only [r, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨hne0, htop⟩
    omega
  have hr_dist : ∀ u : V, ∃ w : V, r ≤ G.dist u w := by
    intro u
    by_contra hcon
    push Not at hcon
    have hecc : G.eccent u ≤ ((r - 1 : ℕ) : ℕ∞) := by
      rw [G.eccent_le_iff]
      intro w
      have hw : G.dist u w ≤ r - 1 := by have := hcon w; omega
      obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u w
      have hed : G.edist u w ≤ (p.length : ℕ∞) := SimpleGraph.edist_le p
      calc G.edist u w ≤ (p.length : ℕ∞) := hed
        _ = (G.dist u w : ℕ∞) := by rw [hp]
        _ ≤ ((r - 1 : ℕ) : ℕ∞) := by exact_mod_cast hw
    have hrad_le : G.radius ≤ ((r - 1 : ℕ) : ℕ∞) := le_trans G.radius_le_eccent hecc
    have hto := ENat.toNat_le_toNat hrad_le (ENat.natCast_ne_top (r - 1))
    simp only [ENat.toNat_natCast] at hto
    change r ≤ r - 1 at hto
    omega
  -- Extract a maximum independent set in N_G(v)
  obtain ⟨N, hN⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  let I : Finset V := N.map (Function.Embedding.subtype _)
  have hI_card : I.card = indepNeighborsCard G v := by
    simpa [I, indepNeighborsCard] using hN.card_eq
  have hI_adj : ∀ x ∈ I, G.Adj v x := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact y.prop
  have hI_ind : G.IsIndepSet (I : Set V) := by
    intro a ha b hb hne hadj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    exact hN.isIndepSet hx hy (fun h => hne (congrArg Subtype.val h)) hadj
  have hnat : 2 * (r - 1) + indepNeighborsCard G v ≤ G.largestInducedBipartiteSubgraphSize := by
    by_cases hr1 : r = 1
    · rw [hr1]
      have hdisj : Disjoint ({v} : Finset V) I := by
        apply Finset.disjoint_singleton_left.mpr
        intro hvI
        exact (hI_adj v hvI).ne rfl
      have hv_ind : G.IsIndepSet (({v} : Finset V) : Set V) := by
        intro a ha b hb hne; simp at ha hb; subst ha; subst hb; exact (hne rfl).elim
      have h := OMA.WOWII16.two_sets hv_ind hI_ind hdisj
      rw [Finset.card_singleton, hI_card] at h
      omega
    · have hr2 : 2 ≤ r := by omega
      let H := OMA.WOWII16.contractGraph G v
      have hHc := OMA.WOWII16.contract_connected hc v
      have hHr := OMA.WOWII16.contract_radius hc hr2 hr_dist v
      obtain ⟨Y_H, X_H, hvY, hdisjH, hY_H, hX_H, hszH⟩ :=
        OMA.WOWII16.master_aux (Fintype.card (OMA.WOWII16.ContractV G v))
          H hHc (r - 1) (by omega) hHr (OMA.WOWII16.contractV0 G v) rfl
      obtain ⟨A, B, _, hdisj, hA, hB, hsz⟩ :=
        OMA.WOWII16.lift_from_contraction hc v hI_ind hI_adj hvY hdisjH.symm hX_H hY_H
      have hbip := OMA.WOWII16.two_sets hA hB hdisj
      omega
  change 2 * ((r : ℝ) - 1) + (vals.max' hvals : ℝ) ≤ b G
  unfold b
  rw [← hv]
  have hcast : ((2 * (r - 1) + indepNeighborsCard G v : ℕ) : ℝ) ≤
      (G.largestInducedBipartiteSubgraphSize : ℝ) := by
    exact_mod_cast hnat
  push_cast [hr_pos] at hcast
  exact hcast
