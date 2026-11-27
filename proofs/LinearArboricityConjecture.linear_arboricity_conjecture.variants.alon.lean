import FormalConjectures.Wikipedia.LinearArboricityConjecture
import Mathlib

/-!
# Alon (1988): asymptotic linear arboricity

For every `ε > 0` there exists `Δ₀` such that every finite graph `G` with
`G.maxDegree ≤ Δ` (`Δ ≥ Δ₀`) satisfies `(linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ`.

Proof outline:
1. Balanced orientation: orient `G` with `deg⁺ ≤ d`, `deg⁻ ≤ d`, `d = (Δ + 1) / 2`,
   by extracting maximal trails from odd-degree vertices (then closed trails).
2. Prime coloring via finite Chernoff + Symmetric LLL: for prime `p > 32 / δ`
   (`δ = min ε (1 / 2)`), there exists `c : V → ZMod p` such that every vertex has
   `≤ k` out-neighbors and `≤ k` in-neighbors in each residue class mod `p`.
3. König bipartite edge-coloring (via Hall's theorem on regularized multiplicity tables):
   for each `r ≠ 0` in `ZMod p`, partition `H_r` into `k` directed 1-factors `F_{r, j}`.
4. Residue-shifted cycle breaking: removing `E_{r, j} = {(u, v) ∈ F_{r, j} | c u = j}`
   leaves `(p - 1) * k` directed acyclic subgraphs of degree `≤ 2` (linear forests).
5. Greedy `2 * D_L`-edge coloring decomposes the leftover graph `H_0 ∪ ⋃ E_{r, j}`
   (max degree `≤ D_L = 4 * k + 2 * p`) into `2 * D_L` matchings (linear forests).
-/

open Finset SimpleGraph LinearArboricityConjecture
open scoped Classical

namespace AlonLinearArboricity

section BalancedOrientation

private def orientWalk {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V}, G.Walk u v → V → V → Prop
  | _, _, .nil, _, _ => False
  | u, _, .cons (v := w) _ p, x, y => (x = u ∧ y = w) ∨ orientWalk p x y

private lemma orientWalk_mem_edges {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) {x y : V}, orientWalk p x y → s(x, y) ∈ p.edges
  | _, _, .nil, _, _, h => False.elim h
  | u, _, .cons (v := w) _ p, x, y, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · exact List.mem_cons_of_mem _ (orientWalk_mem_edges p h)

private lemma orientWalk_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) {x y : V} (h : orientWalk p x y) : G.Adj x y :=
  p.edges_subset_edgeSet (orientWalk_mem_edges p h)

private lemma orientWalk_antisymm {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} {p : G.Walk u v}, p.IsTrail → ∀ {x y : V}, orientWalk p x y → ¬ orientWalk p y x
  | _, _, .nil, _, _, _, h, _ => False.elim h
  | u, _, .cons (v := w) hadj p, hp, x, y, h1, h2 => by
    rw [Walk.isTrail_cons] at hp
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨h2a, h2b⟩ | h2
    · exact hadj.ne h2a.symm
    · have hm := orientWalk_mem_edges p h2
      rw [Sym2.eq_swap] at hm
      exact hp.2 hm
    · have hm := orientWalk_mem_edges p h1
      rw [h2a, h2b, Sym2.eq_swap] at hm
      exact hp.2 hm
    · exact orientWalk_antisymm hp.1 h1 h2

private lemma mem_edges_iff_orientWalk {V : Type*} [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) {e : Sym2 V},
      e ∈ p.edges ↔ ∃ x y, s(x, y) = e ∧ orientWalk p x y
  | _, _, .nil, e => by simp [orientWalk]
  | u, _, .cons (v := w) _ p, e => by
    simp only [Walk.edges_cons, List.mem_cons, orientWalk]
    constructor
    · rintro (rfl | h)
      · exact ⟨u, w, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨x, y, hxy, ho⟩ := (mem_edges_iff_orientWalk p).mp h
        exact ⟨x, y, hxy, Or.inr ho⟩
    · rintro ⟨x, y, rfl, ⟨rfl, rfl⟩ | ho⟩
      · exact Or.inl rfl
      · exact Or.inr ((mem_edges_iff_orientWalk p).mpr ⟨x, y, rfl, ho⟩)

private lemma orientWalk_balance {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} :
    ∀ {u v : V} {p : G.Walk u v}, p.IsTrail → ∀ x : V,
      ((Finset.univ.filter fun y => orientWalk p x y).card : ℤ) -
        ((Finset.univ.filter fun y => orientWalk p y x).card : ℤ) =
        (if x = u then 1 else 0) - (if x = v then 1 else 0)
  | u, _, .nil, _, x => by
    have h0 : ∀ {inst : DecidablePred fun y => orientWalk (Walk.nil : G.Walk u u) x y},
        (Finset.univ.filter fun y => orientWalk (Walk.nil : G.Walk u u) x y).card = 0 := fun {_} => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _
      simp [orientWalk]
    have h1 : ∀ {inst : DecidablePred fun y => orientWalk (Walk.nil : G.Walk u u) y x},
        (Finset.univ.filter fun y => orientWalk (Walk.nil : G.Walk u u) y x).card = 0 := fun {_} => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _
      simp [orientWalk]
    rw [h0, h1]
    simp
  | u, v, .cons (v := w) hadj p, hp, x => by
    have hp' := (Walk.isTrail_cons hadj p).mp hp
    have ih := orientWalk_balance hp'.1 x
    have hnot_out : ¬ orientWalk p u w := fun h => hp'.2 (orientWalk_mem_edges p h)
    have hout_eq : Finset.univ.filter (fun y => orientWalk (.cons hadj p) x y) =
        if x = u then insert w (Finset.univ.filter (fun y => orientWalk p x y))
        else Finset.univ.filter (fun y => orientWalk p x y) := by
      ext y
      by_cases hxu : x = u <;> simp [orientWalk, hxu, eq_comm]
    have hin_eq : Finset.univ.filter (fun y => orientWalk (.cons hadj p) y x) =
        if x = w then insert u (Finset.univ.filter (fun y => orientWalk p y x))
        else Finset.univ.filter (fun y => orientWalk p y x) := by
      ext y
      by_cases hxw : x = w <;> simp [orientWalk, hxw, eq_comm]
    rw [hout_eq, hin_eq]
    have hcard_out : (if x = u then insert w (Finset.univ.filter fun y => orientWalk p x y)
        else Finset.univ.filter fun y => orientWalk p x y).card =
        (Finset.univ.filter fun y => orientWalk p x y).card + if x = u then 1 else 0 := by
      split_ifs with hxu
      · subst hxu
        rw [Finset.card_insert_of_notMem (by simpa using hnot_out)]
      · simp
    have hcard_in : (if x = w then insert u (Finset.univ.filter fun y => orientWalk p y x)
        else Finset.univ.filter fun y => orientWalk p y x).card =
        (Finset.univ.filter fun y => orientWalk p y x).card + if x = w then 1 else 0 := by
      split_ifs with hxw
      · subst hxw
        rw [Finset.card_insert_of_notMem (by simpa using hnot_out)]
      · simp
    rw [hcard_out, hcard_in]
    push_cast
    omega

private lemma extend_trail_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ k : ℕ, ∀ {u v : V} (p : G.Walk u v), p.IsTrail →
      G.edgeFinset.card - p.edges.length ≤ k →
      ∃ (w : V) (q : G.Walk u w), q.IsTrail ∧ p.length ≤ q.length ∧
        ∀ z : V, G.Adj w z → s(w, z) ∈ q.edges
  | 0, u, v, p, hp, hk => by
    by_cases hex : ∃ z : V, G.Adj v z ∧ s(v, z) ∉ p.edges
    · obtain ⟨z, hvz, hnot⟩ := hex
      have hsub : hp.edgesFinset ⊆ G.edgeFinset := fun e he =>
        G.mem_edgeFinset.mpr (p.edges_subset_edgeSet he)
      have hsub' : insert s(v, z) hp.edgesFinset ⊆ G.edgeFinset := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact G.mem_edgeFinset.mpr hvz
        · exact hsub he
      have hc := Finset.card_le_card hsub'
      rw [Finset.card_insert_of_notMem (show s(v, z) ∉ hp.edgesFinset from hnot)] at hc
      have hcard_p : hp.edgesFinset.card = p.edges.length := rfl
      omega
    · push Not at hex
      exact ⟨v, p, hp, le_rfl, hex⟩
  | k + 1, u, v, p, hp, hk => by
    by_cases hex : ∃ z : V, G.Adj v z ∧ s(v, z) ∉ p.edges
    · obtain ⟨z, hvz, hnot⟩ := hex
      let p' : G.Walk u z := p.concat hvz
      have hp' : p'.IsTrail := by
        rw [Walk.isTrail_def, Walk.edges_concat, List.nodup_concat]
        exact ⟨by simpa [Sym2.eq_swap] using hnot, hp.edges_nodup⟩
      have hp'_len : p'.edges.length = p.edges.length + 1 := by
        simp [p', Walk.edges_concat]
      have hdrop : G.edgeFinset.card - p'.edges.length ≤ k := by omega
      obtain ⟨w, q, hq, hqlen, hmax⟩ := extend_trail_aux G k p' hp' hdrop
      refine ⟨w, q, hq, ?_, hmax⟩
      have : p.length ≤ p'.length := by simp [p']
      exact this.trans hqlen
    · push Not at hex
      exact ⟨v, p, hp, le_rfl, hex⟩

private lemma trail_countP_eq_degree_of_max {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u w : V} {q : G.Walk u w} (hq : q.IsTrail)
    (hmax : ∀ z : V, G.Adj w z → s(w, z) ∈ q.edges) :
    q.edges.countP (fun e => decide (w ∈ e)) = G.degree w := by
  have h1 : q.edges.countP (fun e => decide (w ∈ e)) =
      (hq.edgesFinset.filter (fun e => w ∈ e)).card := by
    rw [List.countP_eq_length_filter]
    have hnd : (q.edges.filter (fun e => decide (w ∈ e))).Nodup := hq.edges_nodup.filter _
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1; ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
    rfl
  rw [h1, ← G.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun e he => Sym2.Mem.other (Finset.mem_filter.mp he).2) ?_ ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp he
    have hadj : G.Adj w (Sym2.Mem.other he'.2) := by
      have hed : e ∈ G.edgeSet := q.edges_subset_edgeSet he'.1
      rw [← Sym2.other_spec he'.2] at hed
      exact hed
    exact (G.mem_neighborFinset w _).mpr hadj
  · intro e₁ he₁ e₂ he₂ heq
    have h₁ := (Finset.mem_filter.mp he₁).2
    have h₂ := (Finset.mem_filter.mp he₂).2
    rw [← Sym2.other_spec h₁, ← Sym2.other_spec h₂, heq]
  · intro z hz
    have hadj : G.Adj w z := (G.mem_neighborFinset w z).mp hz
    refine ⟨s(w, z), Finset.mem_filter.mpr ⟨hmax z hadj, by simp⟩, ?_⟩
    have hspec := @Sym2.other_spec _ w s(w, z) (by simp)
    rcases Sym2.eq_iff.mp hspec with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact False.elim (hadj.ne h1)

private lemma exists_balanced_orientation_aux {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ m : ℕ, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card ≤ m →
      ∃ dir : V → V → Prop,
        (∀ u v, G.Adj u v ↔ dir u v ∨ dir v u) ∧
        (∀ u v, dir u v → ¬ dir v u) ∧
        (∀ v : V,
          ((Finset.univ.filter fun w => dir v w).card : ℤ) -
            ((Finset.univ.filter fun w => dir w v).card : ℤ) ≤ 1 ∧
          ((Finset.univ.filter fun w => dir w v).card : ℤ) -
            ((Finset.univ.filter fun w => dir v w).card : ℤ) ≤ 1)
  | m, G, _, hm => by
    by_cases hempty : G.edgeFinset = ∅
    · refine ⟨fun _ _ => False, ?_, fun _ _ h => h.elim, fun _ => by simp⟩
      intro u v
      constructor
      · intro h
        have hm' : s(u, v) ∈ G.edgeFinset := G.mem_edgeFinset.mpr h
        rw [hempty] at hm'
        simp at hm'
      · rintro (h | h) <;> exact h.elim
    · have hne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      have hq_exists : ∃ (u w : V) (q : G.Walk u w),
          q.IsTrail ∧ 1 ≤ q.length ∧
          (u ≠ w → Odd (G.degree u) ∧ Odd (G.degree w)) ∧
          (u = w → ∀ z : V, Even (G.degree z)) := by
        by_cases hodd : ∃ u : V, Odd (G.degree u)
        · obtain ⟨u, hu⟩ := hodd
          obtain ⟨w, q, hq, _, hmax⟩ :=
            extend_trail_aux G G.edgeFinset.card (.nil : G.Walk u u) Walk.IsTrail.nil (by simp)
          have huw : u ≠ w := by
            rintro rfl
            have hev := (hq.even_countP_edges_iff u).mpr (fun h => (h rfl).elim)
            have hcnt := trail_countP_eq_degree_of_max hq hmax
            have : Even (G.degree u) := by simpa [hcnt] using hev
            exact (Nat.not_even_iff_odd.mpr hu) this
          have hqlen : 1 ≤ q.length := by
            by_contra h0
            have hq0 : q.length = 0 := by omega
            exact huw (Walk.eq_of_length_eq_zero hq0)
          have hw : Odd (G.degree w) := by
            have hcnt := trail_countP_eq_degree_of_max hq hmax
            have hne_ev := hq.even_countP_edges_iff w
            rw [← Nat.not_even_iff_odd]
            intro hev
            have h1 := hne_ev.mp (by simpa [hcnt] using hev) huw
            exact h1.2 rfl
          exact ⟨u, w, q, hq, hqlen, fun _ => ⟨hu, hw⟩, fun h => (huw h).elim⟩
        · push Not at hodd
          have hev_all : ∀ v : V, Even (G.degree v) := fun v =>
            Nat.not_odd_iff_even.mp (hodd v)
          obtain ⟨e, he⟩ := hne
          induction e using Sym2.ind with
          | _ u v =>
            have hadj : G.Adj u v := G.mem_edgeFinset.mp he
            let p0 : G.Walk u v := Walk.cons hadj .nil
            have hp0 : p0.IsTrail := by
              rw [Walk.isTrail_cons]
              exact ⟨Walk.IsTrail.nil, by simp⟩
            obtain ⟨w, q, hq, hqlen, hmax⟩ :=
              extend_trail_aux G G.edgeFinset.card p0 hp0 (by simp [p0])
            have huw : u = w := by
              by_contra hne_uw
              have hcnt := trail_countP_eq_degree_of_max hq hmax
              have h1 := (hq.even_countP_edges_iff w).mp (by simpa [hcnt] using hev_all w) hne_uw
              exact h1.2 rfl
            exact ⟨u, w, q, hq, by simpa [p0] using hqlen, fun h => (h huw).elim,
              fun _ => hev_all⟩
      obtain ⟨u, w, q, hq, hqlen, hpar_ne, hpar_eq⟩ := hq_exists
      let G' : SimpleGraph V := G.deleteEdges hq.edgesFinset
      have hG'_card : G'.edgeFinset.card < G.edgeFinset.card := by
        have hss : G'.edgeFinset ⊂ G.edgeFinset := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro e he
            have he' := G'.mem_edgeFinset.mp he
            induction e using Sym2.ind with
            | _ a b =>
              simp only [G', mem_edgeSet, deleteEdges_adj] at he'
              exact G.mem_edgeFinset.mpr he'.1
          · intro heq
            have hnon : q.edges ≠ [] := by
              rw [← List.length_pos_iff_ne_nil, Walk.length_edges]
              omega
            obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil q.edges hnon
            have heG : e ∈ G.edgeFinset := G.mem_edgeFinset.mpr (q.edges_subset_edgeSet he)
            rw [← heq] at heG
            have heG' : e ∈ G'.edgeSet := G'.mem_edgeFinset.mp heG
            induction e using Sym2.ind with
            | _ a b =>
              simp only [G', mem_edgeSet, deleteEdges_adj] at heG'
              exact heG'.2 he
        exact Finset.card_lt_card hss
      obtain ⟨dir', hdir'_adj, hdir'_anti, hdir'_bal⟩ :=
        exists_balanced_orientation_aux (m - 1) G' (by omega)
      let dir (x y : V) : Prop := dir' x y ∨ orientWalk q x y
      have hdisj_dir : ∀ x y, dir' x y → ¬ orientWalk q x y := by
        intro x y hd ho
        have hadj' : G'.Adj x y := (hdir'_adj x y).mpr (Or.inl hd)
        simp only [G', deleteEdges_adj] at hadj'
        exact hadj'.2 (orientWalk_mem_edges q ho)
      refine ⟨dir, ?_, ?_, ?_⟩
      · intro x y
        constructor
        · intro hxy
          by_cases hmem : s(x, y) ∈ q.edges
          · obtain ⟨a, b, hab, ho⟩ := (mem_edges_iff_orientWalk q).mp hmem
            rcases (Sym2.eq_iff.mp hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl (Or.inr ho)
            · exact Or.inr (Or.inr ho)
          · have hxy' : G'.Adj x y := deleteEdges_adj.mpr
              ⟨hxy, fun h => hmem (Multiset.mem_coe.mp (Finset.mem_coe.mp h))⟩
            rcases (hdir'_adj x y).mp hxy' with hd | hd
            · exact Or.inl (Or.inl hd)
            · exact Or.inr (Or.inl hd)
        · rintro ((hd | ho) | (hd | ho))
          · exact ((hdir'_adj x y).mpr (Or.inl hd)).1
          · exact orientWalk_adj q ho
          · exact ((hdir'_adj x y).mpr (Or.inr hd)).1
          · exact (orientWalk_adj q ho).symm
      · intro x y h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact hdir'_anti x y h1 h2
        · have hadj' : G'.Adj x y := (hdir'_adj x y).mpr (Or.inl h1)
          simp only [G', deleteEdges_adj] at hadj'
          rw [Sym2.eq_swap] at hadj'
          exact hadj'.2 (orientWalk_mem_edges q h2)
        · have hadj' : G'.Adj y x := (hdir'_adj y x).mpr (Or.inl h2)
          simp only [G', deleteEdges_adj] at hadj'
          rw [Sym2.eq_swap] at hadj'
          exact hadj'.2 (orientWalk_mem_edges q h1)
        · exact orientWalk_antisymm hq h1 h2
      · intro x
        have hout_disj : Disjoint (Finset.univ.filter fun y => dir' x y)
            (Finset.univ.filter fun y => orientWalk q x y) := by
          rw [Finset.disjoint_left]
          intro y hy1 hy2
          exact hdisj_dir x y (Finset.mem_filter.mp hy1).2 (Finset.mem_filter.mp hy2).2
        have hin_disj : Disjoint (Finset.univ.filter fun y => dir' y x)
            (Finset.univ.filter fun y => orientWalk q y x) := by
          rw [Finset.disjoint_left]
          intro y hy1 hy2
          exact hdisj_dir y x (Finset.mem_filter.mp hy1).2 (Finset.mem_filter.mp hy2).2
        have hout_card : (Finset.univ.filter fun w => dir x w).card =
            (Finset.univ.filter fun w => dir' x w).card +
              (Finset.univ.filter fun w => orientWalk q x w).card := by
          have heq : (Finset.univ.filter fun w => dir x w) =
              (Finset.univ.filter fun w => dir' x w) ∪
                (Finset.univ.filter fun w => orientWalk q x w) := by
            ext y; simp [dir]
          rw [heq, Finset.card_union_of_disjoint hout_disj]
        have hin_card : (Finset.univ.filter fun w => dir w x).card =
            (Finset.univ.filter fun w => dir' w x).card +
              (Finset.univ.filter fun w => orientWalk q w x).card := by
          have heq : (Finset.univ.filter fun w => dir w x) =
              (Finset.univ.filter fun w => dir' w x) ∪
                (Finset.univ.filter fun w => orientWalk q w x) := by
            ext y; simp [dir]
          rw [heq, Finset.card_union_of_disjoint hin_disj]
        have hbal_q := orientWalk_balance hq x
        have hbal' := hdir'_bal x
        have hdeg'_sum : (Finset.univ.filter fun y => dir' x y).card +
            (Finset.univ.filter fun y => dir' y x).card = G'.degree x := by
          rw [← G'.card_neighborFinset_eq_degree]
          have hdisj_nb : Disjoint (Finset.univ.filter fun y => dir' x y)
              (Finset.univ.filter fun y => dir' y x) := by
            rw [Finset.disjoint_left]
            intro y hy1 hy2
            exact hdir'_anti x y (Finset.mem_filter.mp hy1).2 (Finset.mem_filter.mp hy2).2
          have hunion : (Finset.univ.filter fun y => dir' x y) ∪
              (Finset.univ.filter fun y => dir' y x) = G'.neighborFinset x := by
            ext y
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              mem_neighborFinset]
            exact (hdir'_adj x y).symm
          rw [← hunion, Finset.card_union_of_disjoint hdisj_nb]
        have hdeg_eq : G'.degree x + q.edges.countP (fun e => decide (x ∈ e)) = G.degree x := by
          have hG'_sub : G'.neighborFinset x ⊆ G.neighborFinset x := fun y hy =>
            (G.mem_neighborFinset x y).mpr ((G'.mem_neighborFinset x y).mp hy).1
          have hcnt_q : (G.neighborFinset x \ G'.neighborFinset x).card =
              q.edges.countP (fun e => decide (x ∈ e)) := by
            have h1 : q.edges.countP (fun e => decide (x ∈ e)) =
                (hq.edgesFinset.filter (fun e => x ∈ e)).card := by
              rw [List.countP_eq_length_filter]
              have hnd : (q.edges.filter (fun e => decide (x ∈ e))).Nodup :=
                hq.edges_nodup.filter _
              rw [← List.toFinset_card_of_nodup hnd]
              congr 1; ext e
              simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
              rfl
            rw [h1]
            refine Finset.card_bij (fun y _ => s(x, y)) ?_ ?_ ?_
            · intro y hy
              rw [Finset.mem_sdiff, mem_neighborFinset, mem_neighborFinset] at hy
              have hadjG : G.Adj x y := hy.1
              have hnotG' : ¬ G'.Adj x y := hy.2
              simp only [G', deleteEdges_adj, not_and, not_not] at hnotG'
              exact Finset.mem_filter.mpr ⟨hnotG' hadjG, by simp⟩
            · intro y₁ hy₁ y₂ hy₂ heq
              rw [Finset.mem_sdiff, mem_neighborFinset] at hy₁ hy₂
              rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, hxy2⟩
              · rfl
              · exact False.elim (hy₁.1.ne hxy2.symm)
            · intro e he
              have he' := Finset.mem_filter.mp he
              have hadjG : G.Adj x (Sym2.Mem.other he'.2) := by
                have hed := q.edges_subset_edgeSet he'.1
                rw [← Sym2.other_spec he'.2] at hed
                exact hed
              refine ⟨Sym2.Mem.other he'.2, Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x _).mpr hadjG, ?_⟩, ?_⟩
              · rw [mem_neighborFinset]
                simp only [G', deleteEdges_adj, not_and, not_not]
                intro _
                rw [Sym2.other_spec he'.2]
                exact he'.1
              · exact Sym2.other_spec he'.2
          rw [← G'.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree, ← hcnt_q, add_comm]
          exact Finset.card_sdiff_add_card_eq_card hG'_sub
        have hbal'_zero_of_even : Even (G'.degree x) →
            (Finset.univ.filter fun w => dir' x w).card =
              (Finset.univ.filter fun w => dir' w x).card := by
          rintro ⟨t, ht⟩
          omega
        have hout_eq : ∀ {inst : DecidablePred (fun w => dir x w)},
            (Finset.univ.filter fun w => dir x w).card =
              (Finset.univ.filter fun w => dir' x w).card +
                (Finset.univ.filter fun y => orientWalk q x y).card := by
          intro inst
          convert hout_card
        have hin_eq : ∀ {inst : DecidablePred (fun w => dir w x)},
            (Finset.univ.filter fun w => dir w x).card =
              (Finset.univ.filter fun w => dir' w x).card +
                (Finset.univ.filter fun y => orientWalk q y x).card := by
          intro inst
          convert hin_card
        rw [hout_eq, hin_eq]
        by_cases huw : u = w
        · have hG_ev : Even (G.degree x) := hpar_eq huw x
          have hq_ev : Even (q.edges.countP fun e => decide (x ∈ e)) :=
            (hq.even_countP_edges_iff x).mpr (fun h => (h huw).elim)
          have hG'_ev : Even (G'.degree x) := (Nat.even_add.mp (hdeg_eq ▸ hG_ev)).mpr hq_ev
          have heq' := hbal'_zero_of_even hG'_ev
          have hq0 : ((Finset.univ.filter fun y => orientWalk q x y).card : ℤ) -
              ((Finset.univ.filter fun y => orientWalk q y x).card : ℤ) = 0 := by
            rw [hbal_q, huw]; simp
          omega
        · by_cases hx : x = u ∨ x = w
          · have hG_odd : Odd (G.degree x) := by
              rcases hx with rfl | rfl
              · exact (hpar_ne huw).1
              · exact (hpar_ne huw).2
            have hq_odd : Odd (q.edges.countP fun e => decide (x ∈ e)) := by
              rw [← Nat.not_even_iff_odd]
              intro hev
              have := (hq.even_countP_edges_iff x).mp hev huw
              rcases hx with rfl | rfl
              · exact this.1 rfl
              · exact this.2 rfl
            have hG'_ev : Even (G'.degree x) := by
              obtain ⟨a, ha⟩ := hG_odd
              obtain ⟨b, hb⟩ := hq_odd
              exact ⟨a - b, by omega⟩
            have heq' := hbal'_zero_of_even hG'_ev
            rcases hx with hxu | hxw
            · have hq1 : ((Finset.univ.filter fun y => orientWalk q x y).card : ℤ) -
                  ((Finset.univ.filter fun y => orientWalk q y x).card : ℤ) = 1 := by
                rw [hbal_q, hxu, if_pos rfl, if_neg huw]; norm_num
              omega
            · have hq1 : ((Finset.univ.filter fun y => orientWalk q x y).card : ℤ) -
                  ((Finset.univ.filter fun y => orientWalk q y x).card : ℤ) = -1 := by
                rw [hbal_q, hxw, if_neg (Ne.symm huw), if_pos rfl]; norm_num
              omega
          · push Not at hx
            have hq0 : ((Finset.univ.filter fun y => orientWalk q x y).card : ℤ) -
                ((Finset.univ.filter fun y => orientWalk q y x).card : ℤ) = 0 := by
              rw [hbal_q, if_neg hx.1, if_neg hx.2]; norm_num
            omega

private lemma exists_balanced_orientation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ dir : V → V → Prop,
      (∀ u v, G.Adj u v ↔ dir u v ∨ dir v u) ∧
      (∀ u v, dir u v → ¬ dir v u) ∧
      (∀ v : V,
        (Finset.univ.filter fun w => dir v w).card ≤ (G.degree v + 1) / 2 ∧
        (Finset.univ.filter fun w => dir w v).card ≤ (G.degree v + 1) / 2) := by
  obtain ⟨dir, hadj, hanti, hbal⟩ :=
    exists_balanced_orientation_aux G.edgeFinset.card G le_rfl
  refine ⟨dir, hadj, hanti, fun v => ?_⟩
  have hsum : (Finset.univ.filter fun w => dir v w).card +
      (Finset.univ.filter fun w => dir w v).card = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree]
    have hdisj : Disjoint (Finset.univ.filter fun w => dir v w)
        (Finset.univ.filter fun w => dir w v) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      exact hanti v w (Finset.mem_filter.mp hw1).2 (Finset.mem_filter.mp hw2).2
    have hun : (Finset.univ.filter fun w => dir v w) ∪
        (Finset.univ.filter fun w => dir w v) = G.neighborFinset v := by
      ext w
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
      exact (hadj v w).symm
    rw [← hun, Finset.card_union_of_disjoint hdisj]
  have hb := hbal v
  omega

end BalancedOrientation

section FiniteLLL

private lemma indep_split_product {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (U : Finset (Fin n)) (E F : Finset (Fin n → α))
    (hE : ∀ X Y : Fin n → α, (∀ u ∈ U, X u = Y u) → (X ∈ E ↔ Y ∈ E))
    (hF : ∀ X Y : Fin n → α, (∀ u ∉ U, X u = Y u) → (X ∈ F ↔ Y ∈ F)) :
    (E ∩ F).card * (Fintype.card α) ^ n = E.card * F.card := by
  let a₀ : α := Classical.arbitrary α
  let e : (Fin n → α) ≃ ((u : {x // x ∈ U}) → α) × ((u : {x // x ∉ U}) → α) :=
    { toFun := fun X => (fun u => X u.1, fun u => X u.1)
      invFun := fun ⟨X1, X2⟩ x => if hx : x ∈ U then X1 ⟨x, hx⟩ else X2 ⟨x, hx⟩
      left_inv := fun X => by
        ext x; dsimp only; split_ifs <;> rfl
      right_inv := fun ⟨X1, X2⟩ => by
        ext ⟨x, hx⟩
        · simp [dif_pos hx]
        · simp [dif_neg hx] }
  let E1 : Finset ((u : {x // x ∈ U}) → α) :=
    Finset.univ.filter fun X1 => e.symm (X1, fun _ => a₀) ∈ E
  let F2 : Finset ((u : {x // x ∉ U}) → α) :=
    Finset.univ.filter fun X2 => e.symm (fun _ => a₀, X2) ∈ F
  have hmemE : ∀ X, X ∈ E ↔ (e X).1 ∈ E1 := by
    intro X
    rw [mem_filter]
    refine ⟨fun h => ⟨mem_univ _, (hE X _ fun u hu => ?_).mp h⟩,
      fun h => (hE _ X fun u hu => ?_).mp h.2⟩
    · simp [e, dif_pos hu]
    · simp [e, dif_pos hu]
  have hmemF : ∀ X, X ∈ F ↔ (e X).2 ∈ F2 := by
    intro X
    rw [mem_filter]
    refine ⟨fun h => ⟨mem_univ _, (hF X _ fun u hu => ?_).mp h⟩,
      fun h => (hF _ X fun u hu => ?_).mp h.2⟩
    · simp [e, dif_neg hu]
    · simp [e, dif_neg hu]
  have hcE : E.card = E1.card * (Fintype.card α) ^ (Finset.univ \ U).card := by
    have : E.card = (E1 ×ˢ (Finset.univ : Finset ((u : {x // x ∉ U}) → α))).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_product]; exact ⟨(hmemE X).mp hX, mem_univ _⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), ?_, e.apply_symm_apply _⟩
        rw [hmemE]; simpa using hmem.1
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun]
    congr 2
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x _; exact mem_sdiff.mpr ⟨mem_univ _, x.2⟩
    · intro _ _ _ _ h; exact Subtype.ext h
    · intro y hy; exact ⟨⟨y, (mem_sdiff.mp hy).2⟩, mem_univ _, rfl⟩
  have hcF : F.card = (Fintype.card α) ^ U.card * F2.card := by
    have : F.card = ((Finset.univ : Finset ((u : {x // x ∈ U}) → α)) ×ˢ F2).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_product]; exact ⟨mem_univ _, (hmemF X).mp hX⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), ?_, e.apply_symm_apply _⟩
        rw [hmemF]; simpa using hmem.2
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_coe]
  have hcEF : (E ∩ F).card = E1.card * F2.card := by
    have : (E ∩ F).card = (E1 ×ˢ F2).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_inter] at hX; rw [mem_product]
        exact ⟨(hmemE X).mp hX.1, (hmemF X).mp hX.2⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), mem_inter.mpr ⟨?_, ?_⟩, e.apply_symm_apply _⟩
        · rw [hmemE]; simpa using hmem.1
        · rw [hmemF]; simpa using hmem.2
    rw [this, Finset.card_product]
  have hsum_card : U.card + (Finset.univ \ U).card = n := by
    have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) U
    simpa [Finset.inter_comm, add_comm] using this
  rw [hcEF, hcE, hcF]
  calc (E1.card * F2.card) * (Fintype.card α) ^ n
      = (E1.card * F2.card) * (Fintype.card α) ^ (U.card + (Finset.univ \ U).card) := by
        rw [hsum_card]
    _ = (E1.card * (Fintype.card α) ^ (Finset.univ \ U).card) * ((Fintype.card α) ^ U.card * F2.card) := by
        rw [pow_add]; ring

private lemma finite_lll_nat {n D : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (hD : 1 ≤ D)
    (supp : Fin n → Finset (Fin n))
    (Bad : Fin n → Finset (Fin n → α))
    (hBad_dep : ∀ u (X Y : Fin n → α), (∀ x ∈ supp u, X x = Y x) → (X ∈ Bad u ↔ Y ∈ Bad u))
    (hdeg : ∀ u : Fin n,
      (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)).card ≤ D)
    (hprob : ∀ u : Fin n, (Bad u).card * (D + 1) ^ 2 ≤ (Fintype.card α) ^ n) :
    (Finset.univ.filter fun X : Fin n → α => ∀ u : Fin n, X ∉ Bad u).Nonempty := by
  let q := Fintype.card α
  have hq : 0 < q := Fintype.card_pos
  let Good (T : Finset (Fin n)) : Finset (Fin n → α) :=
    Finset.univ.filter fun X => ∀ w ∈ T, X ∉ Bad w
  have hclaim : ∀ m : ℕ, ∀ T : Finset (Fin n), T.card = m →
      0 < (Good T).card ∧
      ∀ u : Fin n, u ∉ T → (D + 1) * ((Good T) ∩ Bad u).card ≤ (Good T).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hm
      have ih' : ∀ T' : Finset (Fin n), T'.card < T.card →
          0 < (Good T').card ∧
          ∀ u : Fin n, u ∉ T' → (D + 1) * ((Good T') ∩ Bad u).card ≤ (Good T').card :=
        fun T' hlt => ih T'.card (hm ▸ hlt) T' rfl
      by_cases hT_empty : T = ∅
      · subst hT_empty
        have hG : Good ∅ = Finset.univ := by ext X; simp [Good]
        rw [hG, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        refine ⟨pow_pos hq n, fun u _ => ?_⟩
        rw [Finset.univ_inter]
        have hp := hprob u
        have hd1 : D + 1 ≤ (D + 1) ^ 2 := by nlinarith
        calc (D + 1) * (Bad u).card
            ≤ (D + 1) ^ 2 * (Bad u).card := Nat.mul_le_mul_right _ hd1
          _ = (Bad u).card * (D + 1) ^ 2 := mul_comm _ _
          _ ≤ q ^ n := hp
      · have step_ind : ∀ u : Fin n,
            (D + 1) * (Good T ∩ Bad u).card ≤ (Good T).card ∧ 0 < (Good T).card := by
          intro u
          let T1 := T.filter fun w => ¬ Disjoint (supp w) (supp u)
          let T2 := T \ T1
          have hT_split : T = T2 ∪ T1 := by
            ext w; simp [T2, T1]; tauto
          have hGood_T_le_T2 : (Good T).card ≤ (Good T2).card := by
            refine Finset.card_le_card fun X hX => ?_
            rw [mem_filter] at hX ⊢
            exact ⟨mem_univ _, fun w hw => hX.2 w (Finset.sdiff_subset hw)⟩
          have hT1_card : T1.card ≤ D := by
            refine (Finset.card_le_card ?_).trans (hdeg u)
            intro w hw
            rw [mem_filter] at hw ⊢
            exact ⟨mem_univ _, hw.2⟩
          have hT2_good_Bad : (Good T2 ∩ Bad u).card * q ^ n = (Bad u).card * (Good T2).card := by
            rw [Finset.inter_comm]
            refine indep_split_product (supp u) (Bad u) (Good T2) (hBad_dep u) ?_
            intro X Y hXY
            simp only [Good, mem_filter, mem_univ, true_and]
            refine forall₂_congr fun w hw => ?_
            have hdisj : Disjoint (supp w) (supp u) := by
              have := (Finset.mem_sdiff.mp hw).2
              simpa [T1, Finset.mem_filter, (Finset.mem_sdiff.mp hw).1] using this
            refine not_congr (hBad_dep w X Y fun x hx => ?_)
            exact hXY x (Finset.disjoint_left.mp hdisj hx)
          by_cases hT1_empty : T1 = ∅
          · have hTT2 : T = T2 := by rw [hT_split, hT1_empty, Finset.union_empty]
            rw [hTT2]
            have hT2_pos : 0 < (Good T2).card := by
              by_cases hu_empty : T2 = ∅
              · rw [hu_empty]
                have : Good ∅ = Finset.univ := by ext X; simp [Good]
                rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
                exact pow_pos hq n
              · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hu_empty
                have hlt : (T2.erase w).card < T.card := by
                  rw [hTT2]
                  exact Finset.card_erase_lt_of_mem hw
                have hprev := (ih' (T2.erase w) hlt).2 w (Finset.notMem_erase _ _)
                have hpos_er := (ih' (T2.erase w) hlt).1
                have heq_er : Good T2 = Good (T2.erase w) \ (Good (T2.erase w) ∩ Bad w) := by
                  ext X
                  simp only [Good, mem_sdiff, mem_filter, mem_univ, true_and, mem_inter]
                  constructor
                  · intro h
                    refine ⟨fun y hy => h y (Finset.erase_subset _ _ hy), fun ⟨_, hbad⟩ => h w hw hbad⟩
                  · rintro ⟨h1, h2⟩ y hy
                    by_cases hyw : y = w
                    · subst hyw; intro hb; exact h2 ⟨h1, hb⟩
                    · exact h1 y (Finset.mem_erase.mpr ⟨hyw, hy⟩)
                rw [heq_er, Finset.card_sdiff, Finset.inter_eq_left.mpr Finset.inter_subset_left]
                have hle : (D + 1) * (Good (T2.erase w) ∩ Bad w).card ≤ (Good (T2.erase w)).card := hprev
                have : (Good (T2.erase w) ∩ Bad w).card < (Good (T2.erase w)).card := by
                  nlinarith [hD, hpos_er, hle]
                omega
            refine ⟨?_, hT2_pos⟩
            have h1 : (D + 1) * (Good T2 ∩ Bad u).card * q ^ n =
                (D + 1) * (Bad u).card * (Good T2).card := by
              calc (D + 1) * (Good T2 ∩ Bad u).card * q ^ n
                  = (D + 1) * ((Good T2 ∩ Bad u).card * q ^ n) := by ring
                _ = (D + 1) * ((Bad u).card * (Good T2).card) := by rw [hT2_good_Bad]
                _ = (D + 1) * (Bad u).card * (Good T2).card := by ring
            have h2 : (D + 1) * (Bad u).card * (Good T2).card ≤ q ^ n * (Good T2).card := by
              have hp := hprob u
              have hd1 : D + 1 ≤ (D + 1) ^ 2 := by nlinarith
              calc (D + 1) * (Bad u).card * (Good T2).card
                  ≤ (D + 1) ^ 2 * (Bad u).card * (Good T2).card := by gcongr
                _ = (Bad u).card * (D + 1) ^ 2 * (Good T2).card := by ring
                _ ≤ q ^ n * (Good T2).card := by gcongr
            rw [mul_comm (q ^ n) _] at h2
            exact Nat.le_of_mul_le_mul_right (h1.trans_le h2) (pow_pos hq n)
          · have hT1_ne : T1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT1_empty
            have hT2_lt : T2.card < T.card := by
              refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
              intro h
              obtain ⟨w, hw⟩ := hT1_ne
              have hwT : w ∈ T := (Finset.mem_filter.mp hw).1
              exact (Finset.mem_sdiff.mp (h hwT)).2 hw
            have hT2_pos : 0 < (Good T2).card := (ih' T2 hT2_lt).1
            have hdiff_bd : ∀ A : Finset (Fin n), A ⊆ T1 → T2.card + A.card ≤ T.card →
                (D + 1) * ((Good T2).card - (Good (T2 ∪ A)).card) ≤ A.card * (Good T2).card := by
              intro A hAT1 _
              induction A using Finset.induction_on with
              | empty => simp
              | @insert a A' ha ihA =>
                have haT1 : a ∈ T1 := hAT1 (mem_insert_self a A')
                have ha_not : a ∉ T2 ∪ A' := fun h => by
                  rw [mem_union] at h
                  rcases h with h | h
                  · exact (Finset.mem_sdiff.mp h).2 haT1
                  · exact ha h
                have hlt' : (T2 ∪ A').card < T.card := by
                  have hsub : T2 ∪ A' ⊆ T \ {a} := by
                    intro w hw
                    rw [mem_sdiff, mem_singleton]
                    rw [mem_union] at hw
                    refine ⟨?_, fun h => ha_not (h ▸ (mem_union.mpr hw))⟩
                    rcases hw with hw | hw
                    · exact Finset.sdiff_subset hw
                    · exact (Finset.mem_filter.mp (hAT1 (mem_insert_of_mem hw))).1
                  have : (T \ {a}).card < T.card := by
                    refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
                    intro h
                    have haT : a ∈ T := (Finset.mem_filter.mp haT1).1
                    exact (Finset.mem_sdiff.mp (h haT)).2 (mem_singleton_self a)
                  exact (Finset.card_le_card hsub).trans_lt this
                have hstep_a := (ih' (T2 ∪ A') hlt').2 a ha_not
                have hle_T2 : (Good (T2 ∪ A')).card ≤ (Good T2).card := by
                  refine Finset.card_le_card fun X hX => ?_
                  rw [mem_filter] at hX ⊢
                  exact ⟨mem_univ _, fun w hw => hX.2 w (mem_union_left _ hw)⟩
                have hstep_le : (D + 1) * (Good (T2 ∪ A') ∩ Bad a).card ≤ (Good T2).card :=
                  hstep_a.trans hle_T2
                have hsplit_a : Good (T2 ∪ insert a A') =
                    Good (T2 ∪ A') \ (Good (T2 ∪ A') ∩ Bad a) := by
                  ext X
                  simp only [Good, mem_sdiff, mem_filter, mem_univ, true_and, mem_inter, mem_union, mem_insert]
                  constructor
                  · intro h
                    refine ⟨fun w hw => h w (by tauto), fun ⟨_, hb⟩ => h a (by tauto) hb⟩
                  · rintro ⟨h1, h2⟩ w (hw | rfl | hw)
                    · exact h1 w (Or.inl hw)
                    · intro hb; exact h2 ⟨h1, hb⟩
                    · exact h1 w (Or.inr hw)
                have hcard_a : (Good (T2 ∪ insert a A')).card =
                    (Good (T2 ∪ A')).card - (Good (T2 ∪ A') ∩ Bad a).card := by
                  rw [hsplit_a, Finset.card_sdiff, Finset.inter_eq_left.mpr Finset.inter_subset_left]
                have hih := ihA (Finset.Subset.trans (Finset.subset_insert _ _) hAT1) (by
                  have := Finset.card_le_card (Finset.subset_insert a A')
                  omega)
                rw [Finset.card_insert_of_notMem ha]
                have hint_le : (Good (T2 ∪ A') ∩ Bad a).card ≤ (Good (T2 ∪ A')).card :=
                  Finset.card_le_card Finset.inter_subset_left
                have heq_diff : (Good T2).card - (Good (T2 ∪ insert a A')).card =
                    ((Good T2).card - (Good (T2 ∪ A')).card) + (Good (T2 ∪ A') ∩ Bad a).card := by
                  omega
                rw [heq_diff, mul_add]
                calc (D + 1) * ((Good T2).card - (Good (T2 ∪ A')).card) +
                      (D + 1) * (Good (T2 ∪ A') ∩ Bad a).card
                    ≤ A'.card * (Good T2).card + (Good T2).card := by gcongr
                  _ = (A'.card + 1) * (Good T2).card := by ring
            have hT_bd := hdiff_bd T1 (Finset.Subset.refl _) (by
              have hs := Finset.card_sdiff_add_card_inter T T1
              have hinter : T ∩ T1 = T1 := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
              rw [hinter] at hs
              dsimp only [T2]
              omega)
            rw [← hT_split] at hT_bd
            have hT2_le_D1 : (Good T2).card ≤ (D + 1) * (Good T).card := by
              have h1 : (D + 1) * ((Good T2).card - (Good T).card) ≤ D * (Good T2).card :=
                hT_bd.trans (Nat.mul_le_mul_right _ hT1_card)
              have hdiff_eq : (Good T).card + ((Good T2).card - (Good T).card) = (Good T2).card :=
                Nat.add_sub_cancel' hGood_T_le_T2
              nlinarith [h1, hdiff_eq]
            have hT_pos : 0 < (Good T).card := by nlinarith [hT2_pos, hT2_le_D1]
            refine ⟨?_, hT_pos⟩
            have hsub_inter : (Good T ∩ Bad u).card ≤ (Good T2 ∩ Bad u).card := by
              refine Finset.card_le_card fun X hX => ?_
              rw [mem_inter] at hX ⊢
              refine ⟨?_, hX.2⟩
              rw [mem_filter] at hX ⊢
              exact ⟨mem_univ _, fun w hw => hX.1.2 w (Finset.sdiff_subset hw)⟩
            have hmul : (D + 1) * (Good T ∩ Bad u).card * q ^ n ≤ (Good T).card * q ^ n := by
              calc (D + 1) * (Good T ∩ Bad u).card * q ^ n
                  ≤ (D + 1) * (Good T2 ∩ Bad u).card * q ^ n := by gcongr
                _ = (D + 1) * ((Good T2 ∩ Bad u).card * q ^ n) := by ring
                _ = (D + 1) * (Bad u).card * (Good T2).card := by rw [hT2_good_Bad]; ring
                _ ≤ (D + 1) * (Bad u).card * ((D + 1) * (Good T).card) := by gcongr
                _ = (Bad u).card * (D + 1) ^ 2 * (Good T).card := by ring
                _ ≤ q ^ n * (Good T).card := by gcongr; exact hprob u
                _ = (Good T).card * q ^ n := by ring
            exact Nat.le_of_mul_le_mul_right hmul (pow_pos hq n)
        obtain ⟨u₀, _⟩ := Finset.nonempty_iff_ne_empty.mpr hT_empty
        exact ⟨(step_ind u₀).2, fun u _ => (step_ind u).1⟩
  have hfinal := (hclaim (Fintype.card (Fin n)) Finset.univ rfl).1
  have : (Finset.univ.filter fun X : Fin n → α => ∀ u : Fin n, X ∉ Bad u) = Good Finset.univ := by
    ext X; simp [Good]
  rw [this]
  exact Finset.card_pos.mp hfinal

end FiniteLLL

section FiniteChernoff

private lemma exp_le_quad {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp t ≤ 1 + t + 2 * t ^ 2 := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  rw [Real.exp_neg] at h1
  have hpos : 0 < 1 - t := by linarith
  have h2 : Real.exp t ≤ (1 - t)⁻¹ := by
    rw [← inv_inv (Real.exp t)]
    exact inv_anti₀ hpos h1
  exact h2.trans ((inv_le_iff_one_le_mul₀ hpos).mpr (by nlinarith))

private lemma chernoff_fiber_bound {n p k : ℕ} [NeZero p]
    (s : Finset (Fin n)) (a : ZMod p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ((Finset.univ.filter fun f : ↥s → ZMod p =>
        k + 1 ≤ (Finset.univ.filter fun i : ↥s => f i = a).card).card : ℝ) *
      Real.exp (t * ((k : ℝ) + 1)) ≤
      (p : ℝ) ^ s.card * Real.exp ((s.card : ℝ) * (t + 2 * t ^ 2) / p) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (NeZero.pos p)
  have hp1_real : (1 : ℝ) ≤ p := by exact_mod_cast (NeZero.pos p)
  let w : ZMod p → ℝ := fun x => if x = a then Real.exp t else 1
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => by
    dsimp [w]; split_ifs
    · exact (Real.exp_pos t).le
    · norm_num
  have hprod_val : ∀ f : ↥s → ZMod p,
      (∏ i : ↥s, w (f i)) =
        Real.exp (t * ((Finset.univ.filter fun i : ↥s => f i = a).card : ℝ)) := by
    intro f
    have hsplit : (∏ i : ↥s, w (f i)) =
        (∏ _i ∈ Finset.univ.filter (fun i : ↥s => f i = a), Real.exp t) *
          (∏ _i ∈ Finset.univ.filter (fun i : ↥s => f i ≠ a), (1 : ℝ)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ↥s => f i = a)
        (fun i => w (f i))]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        simp [w, (Finset.mem_filter.mp hi).2]
      · apply Finset.prod_congr rfl
        intro i hi
        simp [w, (Finset.mem_filter.mp hi).2]
    rw [hsplit, Finset.prod_const, Finset.prod_const_one, mul_one, ← Real.exp_nat_mul, mul_comm]
  have hsum_all : (∑ f : ↥s → ZMod p, ∏ i : ↥s, w (f i)) =
      (Real.exp t + ((p : ℝ) - 1)) ^ s.card := by
    rw [← Fintype.prod_sum (fun (_ : ↥s) (x : ZMod p) => w x)]
    have h1 : (∑ x : ZMod p, w x) = Real.exp t + ((p : ℝ) - 1) := by
      rw [← Finset.add_sum_erase Finset.univ w (Finset.mem_univ a)]
      have hw_a : w a = Real.exp t := by simp [w]
      have hw_rest : (∑ x ∈ Finset.univ.erase a, w x) = (p : ℝ) - 1 := by
        have hcon : (∑ x ∈ Finset.univ.erase a, w x) = ∑ _x ∈ Finset.univ.erase a, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [w, (Finset.mem_erase.mp hx).1]
        rw [hcon, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
        have hp1 : 1 ≤ p := NeZero.pos p
        rw [Nat.cast_sub hp1, Nat.cast_one]
      rw [hw_a, hw_rest]
    simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  let B := Finset.univ.filter fun f : ↥s → ZMod p =>
    k + 1 ≤ (Finset.univ.filter fun i : ↥s => f i = a).card
  have hmarkov : (B.card : ℝ) * Real.exp (t * ((k : ℝ) + 1)) ≤
      ∑ f : ↥s → ZMod p, ∏ i : ↥s, w (f i) := by
    calc (B.card : ℝ) * Real.exp (t * ((k : ℝ) + 1))
        = ∑ _f ∈ B, Real.exp (t * ((k : ℝ) + 1)) := by simp [nsmul_eq_mul]
      _ ≤ ∑ f ∈ B, ∏ i : ↥s, w (f i) := by
          apply Finset.sum_le_sum
          intro f hf
          rw [hprod_val f]
          apply Real.exp_le_exp.mpr
          have hcnt : ((k : ℝ) + 1) ≤ ((Finset.univ.filter fun i : ↥s => f i = a).card : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp hf).2
          exact mul_le_mul_of_nonneg_left hcnt ht0
      _ ≤ ∑ f : ↥s → ZMod p, ∏ i : ↥s, w (f i) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro f
          exact Finset.prod_nonneg fun i _ => hw_nonneg (f i)
  rw [hsum_all] at hmarkov
  apply hmarkov.trans
  have hexp_ge : 0 ≤ Real.exp t + ((p : ℝ) - 1) := by linarith [Real.exp_pos t, hp1_real]
  have hid : Real.exp t + ((p : ℝ) - 1) = (p : ℝ) * (1 + (Real.exp t - 1) / p) := by
    field_simp; ring
  have hquad : Real.exp t - 1 ≤ t + 2 * t ^ 2 := by linarith [exp_le_quad ht0 ht1]
  have hbase : Real.exp t + ((p : ℝ) - 1) ≤ (p : ℝ) * Real.exp ((t + 2 * t ^ 2) / p) := by
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ hp_pos.le
    calc 1 + (Real.exp t - 1) / p ≤ Real.exp ((Real.exp t - 1) / p) := by
          linarith [Real.add_one_le_exp ((Real.exp t - 1) / p)]
      _ ≤ Real.exp ((t + 2 * t ^ 2) / p) := by
          apply Real.exp_le_exp.mpr
          exact div_le_div_of_nonneg_right hquad hp_pos.le
  calc (Real.exp t + ((p : ℝ) - 1)) ^ s.card
      ≤ ((p : ℝ) * Real.exp ((t + 2 * t ^ 2) / p)) ^ s.card :=
        pow_le_pow_left₀ hexp_ge hbase s.card
    _ = (p : ℝ) ^ s.card * Real.exp ((s.card : ℝ) * (t + 2 * t ^ 2) / p) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1; ring_nf

private lemma chernoff_vertex_bound {n p k d : ℕ} [NeZero p]
    (v : Fin n) (s : Finset (Fin n)) (hvs : v ∉ s) (hs : s.card ≤ d)
    (shift : ZMod p → ZMod p) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hk : (1 + 4 * t) * (d : ℝ) / p ≤ (k : ℝ) + 1) :
    ((Finset.univ.filter fun X : Fin n → ZMod p =>
        k + 1 ≤ (s.filter fun u => X u = shift (X v)).card).card : ℝ) ≤
      (p : ℝ) ^ n * Real.exp (-(2 * t ^ 2 * (d : ℝ) / p)) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (NeZero.pos p)
  let R := Finset.univ \ insert v s
  have hR_card : 1 + s.card + R.card = n := by
    have hs1 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) (insert v s)
    rw [Finset.univ_inter, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem hvs] at hs1
    change R.card + (s.card + 1) = n at hs1
    omega
  let mkX (xv : ZMod p) (xs : ↥s → ZMod p) (xr : ↥R → ZMod p) : Fin n → ZMod p := fun x =>
    if hxv : x = v then xv
    else if hxs : x ∈ s then xs ⟨x, hxs⟩
    else xr ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hxv, hxs]⟩⟩
  let BadAll := Finset.univ.filter fun X : Fin n → ZMod p =>
    k + 1 ≤ (s.filter fun u => X u = shift (X v)).card
  let Fiber (xv : ZMod p) := Finset.univ.filter fun xs : ↥s → ZMod p =>
    k + 1 ≤ (Finset.univ.filter fun u : ↥s => xs u = shift xv).card
  have hcnt_eq : ∀ X : Fin n → ZMod p,
      (s.filter fun u => X u = shift (X v)).card =
        (Finset.univ.filter fun u : ↥s => X u.1 = shift (X v)).card := by
    intro X
    refine Finset.card_bij (fun u hu => ⟨u, (Finset.mem_filter.mp hu).1⟩) ?_ ?_ ?_
    · intro u hu; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    · intro u₁ _ u₂ _ h; exact congrArg Subtype.val h
    · intro ⟨u, hu⟩ hmem
      exact ⟨u, Finset.mem_filter.mpr ⟨hu, (Finset.mem_filter.mp hmem).2⟩, rfl⟩
  have hBad_bij : BadAll.card = ∑ xv : ZMod p, (Fiber xv).card * p ^ R.card := by
    have hsplit : BadAll.card =
        ((Finset.univ : Finset (ZMod p)).sigma (fun xv =>
          (Fiber xv) ×ˢ (Finset.univ : Finset (↥R → ZMod p)))).card := by
      refine Finset.card_bij
        (fun X _ => ⟨X v, (fun u : ↥s => X u.1, fun u : ↥R => X u.1)⟩) ?_ ?_ ?_
      · intro X hX
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, true_and]
        have hX' := (Finset.mem_filter.mp hX).2
        rw [hcnt_eq] at hX'
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX'⟩, trivial⟩
      · intro X₁ _ X₂ _ heq
        have hfv : X₁ v = X₂ v := congrArg Sigma.fst heq
        have hpair : (fun u : ↥s => X₁ u.1, fun u : ↥R => X₁ u.1) =
            (fun u : ↥s => X₂ u.1, fun u : ↥R => X₂ u.1) :=
          eq_of_heq (Sigma.ext_iff.mp heq).2
        have hfs : (fun u : ↥s => X₁ u.1) = (fun u : ↥s => X₂ u.1) := congrArg Prod.fst hpair
        have hfr : (fun u : ↥R => X₁ u.1) = (fun u : ↥R => X₂ u.1) := congrArg Prod.snd hpair
        funext x
        by_cases hxv : x = v
        · subst hxv; exact hfv
        · by_cases hxs : x ∈ s
          · exact congrFun hfs ⟨x, hxs⟩
          · exact congrFun hfr ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hxv, hxs]⟩⟩
      · rintro ⟨xv, xs, xr⟩ hmem
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_product, true_and] at hmem
        refine ⟨mkX xv xs xr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [hcnt_eq]
          have hv_eq : mkX xv xs xr v = xv := by simp [mkX]
          have hxs_eq : ∀ u : ↥s, mkX xv xs xr u.1 = xs u := fun ⟨u, hu⟩ => by
            have huv : u ≠ v := fun h => hvs (h ▸ hu)
            simp [mkX, huv, hu]
          simpa [hv_eq, hxs_eq] using (Finset.mem_filter.mp hmem.1).2
        · have hv_eq : mkX xv xs xr v = xv := by simp [mkX]
          have hxs_eq : (fun u : ↥s => mkX xv xs xr u.1) = xs := by
            funext ⟨u, hu⟩
            have huv : u ≠ v := fun h => hvs (h ▸ hu)
            simp [mkX, huv, hu]
          have hxr_eq : (fun u : ↥R => mkX xv xs xr u.1) = xr := by
            funext ⟨u, hu⟩
            have hu' := Finset.mem_sdiff.mp hu
            simp only [Finset.mem_insert, not_or] at hu'
            simp [mkX, hu'.2.1, hu'.2.2]
          simp [hv_eq, hxs_eq, hxr_eq]
    rw [hsplit, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro xv _
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
  have hfib_bd : ∀ xv : ZMod p, ((Fiber xv).card : ℝ) ≤
      (p : ℝ) ^ s.card * Real.exp (-(2 * t ^ 2 * (d : ℝ) / p)) := by
    intro xv
    have hch := chernoff_fiber_bound (k := k) s (shift xv) t ht0 ht1
    have hexp_pos : 0 < Real.exp (t * ((k : ℝ) + 1)) := Real.exp_pos _
    rw [← le_div_iff₀ hexp_pos] at hch
    apply hch.trans
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp_pos.le _)
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hsd : (s.card : ℝ) ≤ d := by exact_mod_cast hs
    have hquad_nn : 0 ≤ t + 2 * t ^ 2 := by positivity
    have h1 : (s.card : ℝ) * (t + 2 * t ^ 2) / p ≤ (d : ℝ) * (t + 2 * t ^ 2) / p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsd hquad_nn) hp_pos.le
    have h2 : t * ((1 + 4 * t) * (d : ℝ) / p) ≤ t * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hk ht0
    linarith [show (d : ℝ) * (t + 2 * t ^ 2) / p - t * ((1 + 4 * t) * (d : ℝ) / p) =
      -(2 * t ^ 2 * (d : ℝ) / p) by ring]
  rw [hBad_bij]
  push_cast
  calc (∑ xv : ZMod p, ((Fiber xv).card : ℝ) * (p : ℝ) ^ R.card)
      ≤ ∑ _xv : ZMod p,
          ((p : ℝ) ^ s.card * Real.exp (-(2 * t ^ 2 * (d : ℝ) / p))) * (p : ℝ) ^ R.card := by
        apply Finset.sum_le_sum
        intro xv _
        exact mul_le_mul_of_nonneg_right (hfib_bd xv) (pow_nonneg hp_pos.le _)
    _ = (p : ℝ) * ((p : ℝ) ^ s.card * (p : ℝ) ^ R.card *
          Real.exp (-(2 * t ^ 2 * (d : ℝ) / p))) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        ring
    _ = (p : ℝ) ^ (1 + s.card + R.card) * Real.exp (-(2 * t ^ 2 * (d : ℝ) / p)) := by
        rw [pow_add, pow_add, pow_one]
        ring
    _ = (p : ℝ) ^ n * Real.exp (-(2 * t ^ 2 * (d : ℝ) / p)) := by
        rw [hR_card]

end FiniteChernoff

section KonigEdgeColoring

private lemma card_filter_fst_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (u : V) :
    (E.filter fun e => e.1 = u).card = ∑ v : V, (if (u, v) ∈ E then 1 else 0) := by
  rw [← Finset.card_filter]
  refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
  · intro e he
    obtain ⟨hE, rfl⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hE⟩
  · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    have ha₁ := (Finset.mem_filter.mp h₁).2
    have ha₂ := (Finset.mem_filter.mp h₂).2
    dsimp only at heq
    subst ha₁ ha₂ heq
    rfl
  · intro v hv
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, rfl⟩, rfl⟩

private lemma card_filter_snd_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (v : V) :
    (E.filter fun e => e.2 = v).card = ∑ u : V, (if (u, v) ∈ E then 1 else 0) := by
  rw [← Finset.card_filter]
  refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
  · intro e he
    obtain ⟨hE, rfl⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hE⟩
  · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    have hb₁ := (Finset.mem_filter.mp h₁).2
    have hb₂ := (Finset.mem_filter.mp h₂).2
    dsimp only at heq
    subst hb₁ hb₂ heq
    rfl
  · intro u hu
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).2, rfl⟩, rfl⟩

private lemma exists_regularization {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (E : Finset (V × V))
    (hout : ∀ u : V, (E.filter fun e => e.1 = u).card ≤ k)
    (hin : ∀ v : V, (E.filter fun e => e.2 = v).card ≤ k) :
    ∃ dummy : V → V → ℕ,
      (∀ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) = k) ∧
      (∀ v : V, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) = k) := by
  have aux : ∀ m : ℕ, ∀ dummy : V → V → ℕ,
      (∀ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) ≤ k) →
      (∀ v : V, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) ≤ k) →
      k * Fintype.card V - ∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) ≤ m →
      ∃ dummy' : V → V → ℕ,
        (∀ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v) = k) ∧
        (∀ v : V, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v) = k) := by
    intro m
    induction m with
    | zero =>
      intro dummy hrow hcol hm
      refine ⟨dummy, fun u => ?_, fun v => ?_⟩
      · by_contra hne
        have hlt : ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) < k :=
          lt_of_le_of_ne (hrow u) hne
        have hsum_lt : (∑ u' : V, ∑ v : V, ((if (u', v) ∈ E then 1 else 0) + dummy u' v)) <
            ∑ _u' : V, k :=
          Finset.sum_lt_sum (fun u' _ => hrow u') ⟨u, Finset.mem_univ u, hlt⟩
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm (Fintype.card V) k] at hsum_lt
        omega
      · by_contra hne
        have hlt : ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) < k :=
          lt_of_le_of_ne (hcol v) hne
        have hsum_lt : (∑ v' : V, ∑ u : V, ((if (u, v') ∈ E then 1 else 0) + dummy u v')) <
            ∑ _v' : V, k :=
          Finset.sum_lt_sum (fun v' _ => hcol v') ⟨v, Finset.mem_univ v, hlt⟩
        rw [Finset.sum_comm] at hsum_lt
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm (Fintype.card V) k] at hsum_lt
        omega
    | succ m ih =>
      intro dummy hrow hcol hm
      by_cases hdone : (∀ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) = k) ∧
          (∀ v : V, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) = k)
      · exact ⟨dummy, hdone.1, hdone.2⟩
      · have htot_lt : (∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v)) <
            k * Fintype.card V := by
          by_contra hge
          have heq : ∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) =
              k * Fintype.card V := by
            have hle : ∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) ≤
                ∑ _u : V, k := Finset.sum_le_sum fun u _ => hrow u
            simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hle
            omega
          exact hdone ⟨fun u => by
            by_contra hne
            have := Finset.sum_lt_sum (fun u' _ => hrow u')
              ⟨u, Finset.mem_univ u, lt_of_le_of_ne (hrow u) hne⟩
            simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at this
            omega, fun v => by
            by_contra hne
            have := Finset.sum_lt_sum (fun v' _ => hcol v')
              ⟨v, Finset.mem_univ v, lt_of_le_of_ne (hcol v) hne⟩
            rw [Finset.sum_comm] at this
            simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at this
            omega⟩
        have hex_u : ∃ u₀ : V, ∑ v : V, ((if (u₀, v) ∈ E then 1 else 0) + dummy u₀ v) < k := by
          by_contra hno
          push Not at hno
          have : k * Fintype.card V ≤ ∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) := by
            calc k * Fintype.card V = ∑ _u : V, k := by simp [mul_comm]
              _ ≤ _ := Finset.sum_le_sum fun u _ => hno u
          omega
        have hex_v : ∃ v₀ : V, ∑ u : V, ((if (u, v₀) ∈ E then 1 else 0) + dummy u v₀) < k := by
          by_contra hno
          push Not at hno
          have : k * Fintype.card V ≤ ∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) := by
            rw [Finset.sum_comm]
            calc k * Fintype.card V = ∑ _v : V, k := by simp [mul_comm]
              _ ≤ _ := Finset.sum_le_sum fun v _ => hno v
          omega
        obtain ⟨u₀, hu₀⟩ := hex_u
        obtain ⟨v₀, hv₀⟩ := hex_v
        let dummy' : V → V → ℕ := fun u v => dummy u v + if u = u₀ ∧ v = v₀ then 1 else 0
        have hrow' : ∀ u, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v) ≤ k := by
          intro u
          by_cases hu : u = u₀
          · subst hu
            have : (∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
                (∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v)) + 1 := by
              simp only [dummy', ← add_assoc]
              rw [Finset.sum_add_distrib]
              simp
            omega
          · have : (∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
                ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) := by
              apply Finset.sum_congr rfl; intro v _; simp [dummy', hu]
            rw [this]; exact hrow u
        have hcol' : ∀ v, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v) ≤ k := by
          intro v
          by_cases hv : v = v₀
          · subst hv
            have : (∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
                (∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v)) + 1 := by
              simp only [dummy', ← add_assoc]
              rw [Finset.sum_add_distrib]
              simp
            omega
          · have : (∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
                ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v) := by
              apply Finset.sum_congr rfl; intro u _; simp [dummy', hv]
            rw [this]; exact hcol v
        have hsum_inc : (∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
            (∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v)) + 1 := by
          have hadd : (∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy' u v)) =
              (∑ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + dummy u v)) +
                (∑ u : V, ∑ v : V, if u = u₀ ∧ v = v₀ then 1 else 0) := by
            simp only [dummy', ← add_assoc, Finset.sum_add_distrib]
          have h1 : (∑ u : V, ∑ v : V, if u = u₀ ∧ v = v₀ then 1 else 0) = 1 := by
            rw [← Fintype.sum_prod_type']
            have hf : (Finset.univ.filter fun x : V × V => x.1 = u₀ ∧ x.2 = v₀) = {(u₀, v₀)} := by
              ext ⟨a, b⟩; simp
            rw [← Finset.card_filter, hf, Finset.card_singleton]
          rw [hadd, h1]
        exact ih dummy' hrow' hcol' (by omega)
  have hrow0 : ∀ u : V, ∑ v : V, ((if (u, v) ∈ E then 1 else 0) + 0) ≤ k := fun u => by
    simpa [← card_filter_fst_eq_sum E u] using hout u
  have hcol0 : ∀ v : V, ∑ u : V, ((if (u, v) ∈ E then 1 else 0) + 0) ≤ k := fun v => by
    simpa [← card_filter_snd_eq_sum E v] using hin v
  exact aux (k * Fintype.card V) (fun _ _ => 0) hrow0 hcol0 (Nat.sub_le _ _)

private lemma konig_decompose {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ k : ℕ, ∀ E : Finset (V × V),
      (∀ u : V, (E.filter fun e => e.1 = u).card ≤ k) →
      (∀ v : V, (E.filter fun e => e.2 = v).card ≤ k) →
      ∃ F : Fin k → Finset (V × V),
        (∀ j : Fin k, F j ⊆ E) ∧
        (∀ j : Fin k, ∀ u : V,
          ((F j).filter fun e => e.1 = u).card ≤ 1 ∧
          ((F j).filter fun e => e.2 = u).card ≤ 1) ∧
        (∀ e, e ∈ E ↔ ∃! j : Fin k, e ∈ F j)
  | 0, E, hout, _ => by
    have hE : E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ h
      have := hout u
      have hp : 0 < (E.filter fun e => e.1 = u).card :=
        Finset.card_pos.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨h, rfl⟩⟩
      omega
    refine ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun e => ?_⟩
    subst hE
    simp
  | k + 1, E, hout, hin => by
    obtain ⟨dummy, hrow, hcol⟩ := exists_regularization (k + 1) E hout hin
    let mult (u v : V) : ℕ := (if (u, v) ∈ E then 1 else 0) + dummy u v
    let adj (u : V) : Finset V := Finset.univ.filter fun v => 0 < mult u v
    have hhall : ∀ S : Finset V, S.card ≤ (S.biUnion adj).card := by
      intro S
      have h1 : (k + 1) * S.card = ∑ u ∈ S, ∑ v : V, mult u v := by
        calc (k + 1) * S.card = ∑ _u ∈ S, (k + 1) := by simp [mul_comm]
          _ = _ := Finset.sum_congr rfl fun u _ => (hrow u).symm
      have h2 : ∑ u ∈ S, ∑ v : V, mult u v = ∑ u ∈ S, ∑ v ∈ S.biUnion adj, mult u v := by
        apply Finset.sum_congr rfl
        intro u hu
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro v _ hv
        by_contra hpos
        have hnz : 0 < mult u v := Nat.pos_of_ne_zero hpos
        exact hv (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnz⟩⟩)
      have h3 : ∑ u ∈ S, ∑ v ∈ S.biUnion adj, mult u v ≤
          ∑ u : V, ∑ v ∈ S.biUnion adj, mult u v :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      have h4 : ∑ u : V, ∑ v ∈ S.biUnion adj, mult u v = (k + 1) * (S.biUnion adj).card := by
        rw [Finset.sum_comm]
        calc ∑ v ∈ S.biUnion adj, ∑ u : V, mult u v
            = ∑ _v ∈ S.biUnion adj, (k + 1) := Finset.sum_congr rfl fun v _ => hcol v
          _ = (k + 1) * (S.biUnion adj).card := by simp [mul_comm]
      have hmul : (k + 1) * S.card ≤ (k + 1) * (S.biUnion adj).card :=
        h1.trans_le (h2.symm ▸ h3.trans_eq h4)
      exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos k)
    obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hhall
    have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
    let F0 : Finset (V × V) := E.filter fun e => e.2 = f e.1
    let E' : Finset (V × V) := E \ F0
    have hout' : ∀ u : V, (E'.filter fun e => e.1 = u).card ≤ k := by
      intro u
      by_cases hu : (u, f u) ∈ E
      · have huF0 : (u, f u) ∈ F0 := Finset.mem_filter.mpr ⟨hu, rfl⟩
        have hsub : E'.filter (fun e => e.1 = u) ⊆ (E.filter fun e => e.1 = u).erase (u, f u) := by
          intro e he
          have he' := Finset.mem_filter.mp he
          have he1 := Finset.mem_sdiff.mp he'.1
          exact Finset.mem_erase.mpr
            ⟨fun h => he1.2 (h ▸ huF0), Finset.mem_filter.mpr ⟨he1.1, he'.2⟩⟩
        have hc := Finset.card_le_card hsub
        have hm_mem : (u, f u) ∈ E.filter (fun e => e.1 = u) := Finset.mem_filter.mpr ⟨hu, rfl⟩
        rw [Finset.card_erase_of_mem hm_mem] at hc
        have := hout u
        omega
      · have hm : 0 < mult u (f u) := (Finset.mem_filter.mp (hf_mem u)).2
        have hd : 1 ≤ dummy u (f u) := by
          dsimp [mult] at hm
          rw [if_neg hu, zero_add] at hm
          exact hm
        have hle : (E'.filter fun e => e.1 = u).card ≤ (E.filter fun e => e.1 = u).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
        have hrow_u : (∑ v : V, if (u, v) ∈ E then 1 else 0) + (∑ v : V, dummy u v) = k + 1 := by
          simpa [Finset.sum_add_distrib] using hrow u
        have hsum_dum : 1 ≤ ∑ v : V, dummy u v :=
          hd.trans (Finset.single_le_sum (f := fun v => dummy u v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (f u)))
        rw [← card_filter_fst_eq_sum E u] at hrow_u
        omega
    have hin' : ∀ v : V, (E'.filter fun e => e.2 = v).card ≤ k := by
      intro v
      obtain ⟨u, rfl⟩ := hf_surj v
      by_cases hu : (u, f u) ∈ E
      · have huF0 : (u, f u) ∈ F0 := Finset.mem_filter.mpr ⟨hu, rfl⟩
        have hsub : E'.filter (fun e => e.2 = f u) ⊆
            (E.filter fun e => e.2 = f u).erase (u, f u) := by
          intro e he
          have he' := Finset.mem_filter.mp he
          have he1 := Finset.mem_sdiff.mp he'.1
          exact Finset.mem_erase.mpr
            ⟨fun h => he1.2 (h ▸ huF0), Finset.mem_filter.mpr ⟨he1.1, he'.2⟩⟩
        have hc := Finset.card_le_card hsub
        have hm_mem : (u, f u) ∈ E.filter (fun e => e.2 = f u) := Finset.mem_filter.mpr ⟨hu, rfl⟩
        rw [Finset.card_erase_of_mem hm_mem] at hc
        have := hin (f u)
        omega
      · have hm : 0 < mult u (f u) := (Finset.mem_filter.mp (hf_mem u)).2
        have hd : 1 ≤ dummy u (f u) := by
          dsimp [mult] at hm
          rw [if_neg hu, zero_add] at hm
          exact hm
        have hle : (E'.filter fun e => e.2 = f u).card ≤ (E.filter fun e => e.2 = f u).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
        have hcol_v : (∑ u' : V, if (u', f u) ∈ E then 1 else 0) + (∑ u' : V, dummy u' (f u)) = k + 1 := by
          simpa [Finset.sum_add_distrib] using hcol (f u)
        have hsum_dum : 1 ≤ ∑ u' : V, dummy u' (f u) :=
          hd.trans (Finset.single_le_sum (f := fun u' => dummy u' (f u)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u))
        rw [← card_filter_snd_eq_sum E (f u)] at hcol_v
        omega
    obtain ⟨F', hF'sub, hF'deg, hF'part⟩ := konig_decompose k E' hout' hin'
    refine ⟨Fin.cons F0 F', ?_, ?_, ?_⟩
    · intro j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact Finset.filter_subset _ _
      · exact (hF'sub j').trans Finset.sdiff_subset
    · intro j u
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp only [Fin.cons_zero]
        constructor
        · rw [Finset.card_le_one]
          rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂
          have h₁' := Finset.mem_filter.mp h₁
          have h₂' := Finset.mem_filter.mp h₂
          have ha₁ : a₁ = u := h₁'.2
          have ha₂ : a₂ = u := h₂'.2
          have hb₁ : b₁ = f a₁ := (Finset.mem_filter.mp h₁'.1).2
          have hb₂ : b₂ = f a₂ := (Finset.mem_filter.mp h₂'.1).2
          subst ha₁ ha₂ hb₁ hb₂
          rfl
        · rw [Finset.card_le_one]
          rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂
          have h₁' := Finset.mem_filter.mp h₁
          have h₂' := Finset.mem_filter.mp h₂
          have hb₁ : b₁ = u := h₁'.2
          have hb₂ : b₂ = u := h₂'.2
          have hfa₁ : b₁ = f a₁ := (Finset.mem_filter.mp h₁'.1).2
          have hfa₂ : b₂ = f a₂ := (Finset.mem_filter.mp h₂'.1).2
          have ha : a₁ = a₂ := hf_inj (hfa₁.symm.trans (hb₁.trans (hb₂.symm.trans hfa₂)))
          subst ha hb₁ hb₂
          rfl
      · exact hF'deg j' u
    · intro e
      constructor
      · intro he
        by_cases he0 : e ∈ F0
        · refine ⟨0, by simpa using he0, ?_⟩
          intro j hj
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · rfl
          · exfalso
            have he' : e ∈ E' := hF'sub j' (by simpa using hj)
            exact (Finset.mem_sdiff.mp he').2 he0
        · have he' : e ∈ E' := Finset.mem_sdiff.mpr ⟨he, he0⟩
          obtain ⟨j', hj', huniq⟩ := (hF'part e).mp he'
          refine ⟨j'.succ, by simpa using hj', ?_⟩
          intro j hj
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j'', rfl⟩
          · exact False.elim (he0 (by simpa using hj))
          · exact congrArg Fin.succ (huniq j'' (by simpa using hj))
      · rintro ⟨j, hj, _⟩
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · have hj0 : e ∈ F0 := by simpa using hj
          exact (Finset.mem_filter.mp hj0).1
        · exact Finset.sdiff_subset (hF'sub j' (by simpa using hj))

end KonigEdgeColoring

section CycleBreakingAndGreedy

private def toGraph {V : Type*} (F : Finset (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ F)

private lemma toGraph_adj {V : Type*} (F : Finset (V × V)) {u v : V} :
    (toGraph F).Adj u v ↔ u ≠ v ∧ ((u, v) ∈ F ∨ (v, u) ∈ F) :=
  SimpleGraph.fromRel_adj _ _ _

private lemma isLinearForest_toGraph_of_deg_le_one_acyclic {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (V × V))
    (_hanti : ∀ u v, (u, v) ∈ F → (v, u) ∉ F)
    (hdeg : ∀ v : V, (F.filter fun e => e.1 = v).card ≤ 1 ∧ (F.filter fun e => e.2 = v).card ≤ 1)
    (hacyc : (toGraph F).IsAcyclic) :
    IsLinearForest (toGraph F) := by
  refine ⟨hacyc, fun v => ?_⟩
  have hsub : (toGraph F).neighborFinset v ⊆
      (F.filter fun e => e.1 = v).image Prod.snd ∪
        (F.filter fun e => e.2 = v).image Prod.fst := by
    intro w hw
    have hadj := (toGraph_adj F).mp ((mem_neighborFinset _ v w).mp hw)
    rcases hadj.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(v, w), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(w, v), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩)
  have hc : ((toGraph F).neighborFinset v).card ≤ 2 := by
    calc ((toGraph F).neighborFinset v).card
        ≤ ((F.filter fun e => e.1 = v).image Prod.snd ∪
            (F.filter fun e => e.2 = v).image Prod.fst).card := Finset.card_le_card hsub
      _ ≤ ((F.filter fun e => e.1 = v).image Prod.snd).card +
            ((F.filter fun e => e.2 = v).image Prod.fst).card := Finset.card_union_le _ _
      _ ≤ (F.filter fun e => e.1 = v).card + (F.filter fun e => e.2 = v).card :=
          Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ 1 + 1 := Nat.add_le_add (hdeg v).1 (hdeg v).2
  simpa only [← Set.ncard_coe_finset, coe_neighborFinset] using hc

private lemma cycle_getVert_ne_add_two {V : Type*} {G : SimpleGraph V} {v₀ : V}
    {w : G.Walk v₀ v₀} (hw : w.IsCycle) {i : ℕ} (hi : i + 2 ≤ w.length) :
    w.getVert i ≠ w.getVert (i + 2) := by
  have hnd : w.support.tail.Nodup := hw.support_nodup
  have h3 : 3 ≤ w.length := hw.three_le_length
  have hlen : w.support.length = w.length + 1 := w.length_support
  have hlen_tail : w.support.tail.length = w.length := by simp [hlen]
  have hget_tail : ∀ j : ℕ, (hj : j < w.length) →
      w.support.tail[j]'(by omega) = w.getVert (j + 1) := by
    intro j hj
    rw [List.getElem_tail, w.getVert_eq_support_getElem (by omega)]
  by_cases hi0 : i = 0
  · subst hi0
    have hw0 : w.getVert 0 = v₀ := w.getVert_zero
    have hwm : w.getVert w.length = v₀ := w.getVert_length
    intro heq
    have heq' : w.getVert w.length = w.getVert (0 + 2) := hwm.trans (hw0.symm.trans heq)
    have h1 : w.support.tail[w.length - 1]'(by omega) = w.support.tail[1]'(by omega) := by
      rw [hget_tail (w.length - 1) (by omega), hget_tail 1 (by omega)]
      simpa [show w.length - 1 + 1 = w.length by omega] using heq'
    have hidx := (List.Nodup.getElem_inj_iff hnd).mp h1
    omega
  · intro heq
    have h1' : w.support.tail[i - 1]'(by omega) = w.support.tail[i + 1]'(by omega) := by
      rw [hget_tail (i - 1) (by omega), hget_tail (i + 1) (by omega)]
      simpa [show i - 1 + 1 = i by omega] using heq
    have hidx := (List.Nodup.getElem_inj_iff hnd).mp h1'
    omega

private lemma residue_cut_acyclic {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℕ) [Fact p.Prime] (r j : ZMod p) (hr : r ≠ 0) (c : V → ZMod p)
    (F : Finset (V × V))
    (_hirr : ∀ e ∈ F, e.1 ≠ e.2)
    (_hanti : ∀ u v, (u, v) ∈ F → (v, u) ∉ F)
    (hdeg : ∀ v : V, (F.filter fun e => e.1 = v).card ≤ 1 ∧ (F.filter fun e => e.2 = v).card ≤ 1)
    (hdiff : ∀ e ∈ F, c e.2 - c e.1 = r) :
    (toGraph (F.filter fun e => c e.1 ≠ j)).IsAcyclic := by
  let F' := F.filter fun e => c e.1 ≠ j
  have hF'sub : F' ⊆ F := Finset.filter_subset _ _
  have hout1 : ∀ v u₁ u₂, (v, u₁) ∈ F' → (v, u₂) ∈ F' → u₁ = u₂ := by
    intro v u₁ u₂ h1 h2
    have hle := Finset.card_le_one.mp (hdeg v).1
    exact congrArg Prod.snd (hle _ (Finset.mem_filter.mpr ⟨hF'sub h1, rfl⟩)
      _ (Finset.mem_filter.mpr ⟨hF'sub h2, rfl⟩))
  have hin1 : ∀ v u₁ u₂, (u₁, v) ∈ F' → (u₂, v) ∈ F' → u₁ = u₂ := by
    intro v u₁ u₂ h1 h2
    have hle := Finset.card_le_one.mp (hdeg v).2
    exact congrArg Prod.fst (hle _ (Finset.mem_filter.mpr ⟨hF'sub h1, rfl⟩)
      _ (Finset.mem_filter.mpr ⟨hF'sub h2, rfl⟩))
  intro v₀ w hw
  let m := w.length
  have hm3 : 3 ≤ m := hw.three_le_length
  have hadj0 : (toGraph F').Adj (w.getVert 0) (w.getVert 1) := w.adj_getVert_succ (by omega)
  rcases ((toGraph_adj F').mp hadj0).2 with hfwd0 | hbwd0
  · have hstep : ∀ i : ℕ, i < m → (w.getVert i, w.getVert (i + 1)) ∈ F' := by
      intro i
      induction i with
      | zero => intro _; exact hfwd0
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hadj := (toGraph_adj F').mp (w.adj_getVert_succ (by omega : i + 1 < m))
        rcases hadj.2 with h | h
        · exact h
        · exfalso
          have heq := hin1 (w.getVert (i + 1)) (w.getVert i) (w.getVert (i + 2)) hprev h
          exact cycle_getVert_ne_add_two hw (by omega) heq
    have hc_val : ∀ i : ℕ, i ≤ m → c (w.getVert i) = c (w.getVert 0) + (i : ZMod p) * r := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hmem := hF'sub (hstep i (by omega))
        have hd := hdiff _ hmem
        dsimp only at hd
        rw [Nat.cast_add, Nat.cast_one]
        linear_combination hprev + hd
    have hloop : (m : ZMod p) * r = 0 := by
      have hm_eq := hc_val m le_rfl
      have h0 : w.getVert 0 = v₀ := w.getVert_zero
      have hm : w.getVert m = v₀ := w.getVert_length
      rw [h0, hm] at hm_eq
      linear_combination -hm_eq
    have hm_zmod : (m : ZMod p) = 0 := (mul_eq_zero.mp hloop).resolve_right hr
    have hpdvd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hm_zmod
    have hpm : p ≤ m := Nat.le_of_dvd (by omega) hpdvd
    let t : ℕ := ((j - c (w.getVert 0)) * r⁻¹).val
    have htp : t < p := ZMod.val_lt _
    have htm : t < m := htp.trans_le hpm
    have hmem_t := hstep t htm
    have hneq_j : c (w.getVert t) ≠ j := (Finset.mem_filter.mp hmem_t).2
    have hct : c (w.getVert t) = j := by
      rw [hc_val t htm.le]
      have ht_cast : (t : ZMod p) = (j - c (w.getVert 0)) * r⁻¹ := ZMod.natCast_zmod_val _
      rw [ht_cast, mul_assoc, ZMod.inv_mul_of_unit _ (Ne.isUnit hr), mul_one]
      ring
    exact hneq_j hct
  · have hstep : ∀ i : ℕ, i < m → (w.getVert (i + 1), w.getVert i) ∈ F' := by
      intro i
      induction i with
      | zero => intro _; exact hbwd0
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hadj := (toGraph_adj F').mp (w.adj_getVert_succ (by omega : i + 1 < m))
        rcases hadj.2 with h | h
        · exfalso
          have heq := hout1 (w.getVert (i + 1)) (w.getVert i) (w.getVert (i + 2)) hprev h
          exact cycle_getVert_ne_add_two hw (by omega) heq
        · exact h
    have hc_val : ∀ i : ℕ, i ≤ m → c (w.getVert i) = c (w.getVert 0) - (i : ZMod p) * r := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have hprev := ih (by omega)
        have hmem := hF'sub (hstep i (by omega))
        have hd := hdiff _ hmem
        dsimp only at hd
        rw [Nat.cast_add, Nat.cast_one]
        linear_combination hprev - hd
    have hloop : (m : ZMod p) * r = 0 := by
      have hm_eq := hc_val m le_rfl
      have h0 : w.getVert 0 = v₀ := w.getVert_zero
      have hm : w.getVert m = v₀ := w.getVert_length
      rw [h0, hm] at hm_eq
      linear_combination hm_eq
    have hm_zmod : (m : ZMod p) = 0 := (mul_eq_zero.mp hloop).resolve_right hr
    have hpdvd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hm_zmod
    have hpm : p ≤ m := Nat.le_of_dvd (by omega) hpdvd
    let t : ℕ := ((c (w.getVert 0) - j) * r⁻¹).val
    have htp : t < p := ZMod.val_lt _
    have htm : t < m := htp.trans_le hpm
    by_cases ht0 : t = 0
    · have hmem_m := hstep (m - 1) (by omega)
      have hneq_j : c (w.getVert m) ≠ j := by
        simpa [show m - 1 + 1 = m by omega] using (Finset.mem_filter.mp hmem_m).2
      have hcm : c (w.getVert m) = j := by
        have h0m : w.getVert m = w.getVert 0 := w.getVert_length.trans w.getVert_zero.symm
        rw [h0m]
        have ht_cast : (t : ZMod p) = (c (w.getVert 0) - j) * r⁻¹ := ZMod.natCast_zmod_val _
        rw [ht0, Nat.cast_zero] at ht_cast
        have hz : c (w.getVert 0) - j = 0 := by
          calc c (w.getVert 0) - j
              = ((c (w.getVert 0) - j) * r⁻¹) * r := by
                rw [mul_assoc, ZMod.inv_mul_of_unit _ (Ne.isUnit hr), mul_one]
            _ = 0 := by rw [← ht_cast, zero_mul]
        exact sub_eq_zero.mp hz
      exact hneq_j hcm
    · have hmem_t := hstep (t - 1) (by omega)
      have hneq_j : c (w.getVert t) ≠ j := by
        simpa [show t - 1 + 1 = t by omega] using (Finset.mem_filter.mp hmem_t).2
      have hct : c (w.getVert t) = j := by
        rw [hc_val t htm.le]
        have ht_cast : (t : ZMod p) = (c (w.getVert 0) - j) * r⁻¹ := ZMod.natCast_zmod_val _
        rw [ht_cast, mul_assoc, ZMod.inv_mul_of_unit _ (Ne.isUnit hr), mul_one]
        ring
      exact hneq_j hct

private lemma isLinearForest_of_deg_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (M : SimpleGraph V) (hdeg : ∀ v : V, (M.neighborSet v).ncard ≤ 1) :
    IsLinearForest M := by
  refine ⟨?_, fun v => (hdeg v).trans (by omega)⟩
  intro v w hw
  have h1 : M.Adj v w.snd := w.adj_snd hw.not_nil
  have h2 : M.Adj v w.penultimate := (w.adj_penultimate hw.not_nil).symm
  have hne : w.snd ≠ w.penultimate := hw.snd_ne_penultimate
  have hle : ({w.snd, w.penultimate} : Finset V).card ≤ (M.neighborFinset v).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (M.mem_neighborFinset v _).mpr h1
    · exact (M.mem_neighborFinset v _).mpr h2
  rw [Finset.card_pair hne, ← Set.ncard_coe_finset, M.coe_neighborFinset] at hle
  have := hdeg v
  omega

private lemma greedy_edge_coloring_aux {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (hD : 1 ≤ D) :
    ∀ m : ℕ, ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      H.edgeFinset.card ≤ m → (∀ v : V, H.degree v ≤ D) →
      ∃ col : Sym2 V → Fin (2 * D),
        ∀ c : Fin (2 * D), ∀ v : V,
          (H.edgeFinset.filter fun e => v ∈ e ∧ col e = c).card ≤ 1
  | m, H, _, hm, hdeg => by
    by_cases hempty : H.edgeFinset = ∅
    · refine ⟨fun _ => ⟨0, by omega⟩, fun c v => ?_⟩
      simp [hempty]
    · have hne : H.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨e, he⟩ := hne
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : H.Adj u v := H.mem_edgeFinset.mp he
        let H' : SimpleGraph V := H.deleteEdges {s(u, v)}
        have hH'_sub : H' ≤ H := fun _ _ h => h.1
        have hH'_card : H'.edgeFinset.card < H.edgeFinset.card := by
          have hss : H'.edgeFinset ⊂ H.edgeFinset := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro e' he'
              induction e' using Sym2.ind with
              | _ a b => exact H.mem_edgeFinset.mpr (hH'_sub (H'.mem_edgeFinset.mp he'))
            · intro heq
              have he' := he
              rw [← heq] at he'
              have := H'.mem_edgeFinset.mp he'
              simp [H'] at this
          exact Finset.card_lt_card hss
        have hH'_deg : ∀ w : V, H'.degree w ≤ D := fun w => by
          have hsub : H'.neighborFinset w ⊆ H.neighborFinset w := fun z hz =>
            (H.mem_neighborFinset w z).mpr (hH'_sub ((H'.mem_neighborFinset w z).mp hz))
          rw [← H'.card_neighborFinset_eq_degree]
          exact (Finset.card_le_card hsub).trans ((H.card_neighborFinset_eq_degree w).symm ▸ hdeg w)
        obtain ⟨col, hcol⟩ := greedy_edge_coloring_aux D hD (m - 1) H' (by omega) hH'_deg
        have hu_deg : H'.degree u ≤ D - 1 := by
          have hsub : H'.neighborFinset u ⊆ (H.neighborFinset u).erase v := by
            intro w hw
            have hw' := (H'.mem_neighborFinset u w).mp hw
            simp only [H', deleteEdges_adj, Set.mem_singleton_iff] at hw'
            exact Finset.mem_erase.mpr ⟨fun h => hw'.2 (h ▸ rfl), (H.mem_neighborFinset u w).mpr hw'.1⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem ((H.mem_neighborFinset u v).mpr hadj),
            H.card_neighborFinset_eq_degree, H'.card_neighborFinset_eq_degree] at hc
          have := hdeg u
          omega
        have hv_deg : H'.degree v ≤ D - 1 := by
          have hsub : H'.neighborFinset v ⊆ (H.neighborFinset v).erase u := by
            intro w hw
            have hw' := (H'.mem_neighborFinset v w).mp hw
            simp only [H', deleteEdges_adj, Set.mem_singleton_iff] at hw'
            exact Finset.mem_erase.mpr
              ⟨fun h => hw'.2 (by rw [h, Sym2.eq_swap]), (H.mem_neighborFinset v w).mpr hw'.1⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem ((H.mem_neighborFinset v u).mpr hadj.symm),
            H.card_neighborFinset_eq_degree, H'.card_neighborFinset_eq_degree] at hc
          have := hdeg v
          omega
        let forb := (H'.neighborFinset u).image (fun w => col s(u, w)) ∪
          (H'.neighborFinset v).image (fun w => col s(v, w))
        have hforb_card : forb.card < 2 * D := by
          calc forb.card
              ≤ ((H'.neighborFinset u).image (fun w => col s(u, w))).card +
                  ((H'.neighborFinset v).image (fun w => col s(v, w))).card :=
                Finset.card_union_le _ _
            _ ≤ (H'.neighborFinset u).card + (H'.neighborFinset v).card :=
                Nat.add_le_add Finset.card_image_le Finset.card_image_le
            _ = H'.degree u + H'.degree v := by
                rw [H'.card_neighborFinset_eq_degree, H'.card_neighborFinset_eq_degree]
            _ ≤ (D - 1) + (D - 1) := Nat.add_le_add hu_deg hv_deg
            _ < 2 * D := by omega
        have hex_free : (Finset.univ \ forb).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hem
          have hsub : (Finset.univ : Finset (Fin (2 * D))) ⊆ forb :=
            Finset.sdiff_eq_empty_iff_subset.mp hem
          have hc := Finset.card_le_card hsub
          rw [Finset.card_univ, Fintype.card_fin] at hc
          omega
        obtain ⟨c₀, hc₀⟩ := hex_free
        have hc₀_not : c₀ ∉ forb := (Finset.mem_sdiff.mp hc₀).2
        let col' : Sym2 V → Fin (2 * D) := fun e' => if e' = s(u, v) then c₀ else col e'
        refine ⟨col', fun c w => ?_⟩
        by_cases hcc₀ : c = c₀
        · subst hcc₀
          by_cases hwu : w = u ∨ w = v
          · have hnone : (H'.edgeFinset.filter fun e' => w ∈ e' ∧ col e' = c).card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro e' he'
              have he'' := Finset.mem_filter.mp he'
              have heH' : e' ∈ H'.edgeSet := H'.mem_edgeFinset.mp he''.1
              have hmemw : w ∈ e' := he''.2.1
              have hcole' : col e' = c := he''.2.2
              have hadjw : H'.Adj w (Sym2.Mem.other hmemw) := by
                rw [← Sym2.other_spec hmemw] at heH'; exact heH'
              have he'_eq : s(w, Sym2.Mem.other hmemw) = e' := Sym2.other_spec hmemw
              rw [← he'_eq] at hcole'
              rcases hwu with rfl | rfl
              · exact hc₀_not (Finset.mem_union_left _ (Finset.mem_image.mpr
                  ⟨_, (H'.mem_neighborFinset _ _).mpr hadjw, hcole'⟩))
              · exact hc₀_not (Finset.mem_union_right _ (Finset.mem_image.mpr
                  ⟨_, (H'.mem_neighborFinset _ _).mpr hadjw, hcole'⟩))
            have hsub : H.edgeFinset.filter (fun e' => w ∈ e' ∧ col' e' = c) ⊆
                insert s(u, v) (H'.edgeFinset.filter fun e' => w ∈ e' ∧ col e' = c) := by
              intro e' he'
              have he'' := Finset.mem_filter.mp he'
              by_cases heuv : e' = s(u, v)
              · rw [heuv]; exact Finset.mem_insert_self _ _
              · have heH' : e' ∈ H'.edgeFinset := by
                  have h1 := H.mem_edgeFinset.mp he''.1
                  induction e' using Sym2.ind with
                  | _ x y => exact H'.mem_edgeFinset.mpr (deleteEdges_adj.mpr ⟨h1, by simpa using heuv⟩)
                have hcol_eq : col e' = c := by simpa [col', heuv] using he''.2.2
                exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨heH', he''.2.1, hcol_eq⟩)
            have hc1 := Finset.card_le_card hsub
            exact hc1.trans ((Finset.card_insert_le _ _).trans (by omega))
          · push Not at hwu
            have hnot_w : w ∉ s(u, v) := by simp [hwu.1, hwu.2]
            have heq_f : H.edgeFinset.filter (fun e' => w ∈ e' ∧ col' e' = c) =
                H'.edgeFinset.filter (fun e' => w ∈ e' ∧ col e' = c) := by
              ext e'
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨he1, he2, he3⟩
                have heuv : e' ≠ s(u, v) := fun h => hnot_w (h ▸ he2)
                have heH' : e' ∈ H'.edgeFinset := by
                  have h1 := H.mem_edgeFinset.mp he1
                  induction e' using Sym2.ind with
                  | _ x y => exact H'.mem_edgeFinset.mpr (deleteEdges_adj.mpr ⟨h1, by simpa using heuv⟩)
                exact ⟨heH', he2, by simpa [col', heuv] using he3⟩
              · rintro ⟨he1, he2, he3⟩
                have heuv : e' ≠ s(u, v) := fun h => hnot_w (h ▸ he2)
                have heH : e' ∈ H.edgeFinset := H.mem_edgeFinset.mpr
                  (edgeSet_mono hH'_sub (H'.mem_edgeFinset.mp he1))
                exact ⟨heH, he2, by simpa [col', heuv] using he3⟩
            rw [heq_f]
            exact hcol c w
        · have heq_f : H.edgeFinset.filter (fun e' => w ∈ e' ∧ col' e' = c) =
              H'.edgeFinset.filter (fun e' => w ∈ e' ∧ col e' = c) := by
            ext e'
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨he1, he2, he3⟩
              have heuv : e' ≠ s(u, v) := by
                rintro rfl
                simp [col'] at he3
                exact hcc₀ he3.symm
              have heH' : e' ∈ H'.edgeFinset := by
                have h1 := H.mem_edgeFinset.mp he1
                induction e' using Sym2.ind with
                | _ x y => exact H'.mem_edgeFinset.mpr (deleteEdges_adj.mpr ⟨h1, by simpa using heuv⟩)
              exact ⟨heH', he2, by simpa [col', heuv] using he3⟩
            · rintro ⟨he1, he2, he3⟩
              have heuv : e' ≠ s(u, v) := by
                rintro rfl
                have := H'.mem_edgeFinset.mp he1
                simp [H'] at this
              have heH : e' ∈ H.edgeFinset := H.mem_edgeFinset.mpr
                (edgeSet_mono hH'_sub (H'.mem_edgeFinset.mp he1))
              exact ⟨heH, he2, by simpa [col', heuv] using he3⟩
          rw [heq_f]
          exact hcol c w

private lemma greedy_matching_decompose {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (D : ℕ) (hD : 1 ≤ D) (hdeg : ∀ v : V, H.degree v ≤ D) :
    ∃ M : Fin (2 * D) → SimpleGraph V,
      (∀ i, IsLinearForest (M i) ∧ M i ≤ H) ∧
      ∀ u v, H.Adj u v ↔ ∃! i, (M i).Adj u v := by
  obtain ⟨col, hcol⟩ := greedy_edge_coloring_aux D hD H.edgeFinset.card H le_rfl hdeg
  let M (i : Fin (2 * D)) : SimpleGraph V := SimpleGraph.fromEdgeSet {e ∈ H.edgeSet | col e = i}
  have hM_adj : ∀ i u v, (M i).Adj u v ↔ H.Adj u v ∧ col s(u, v) = i := by
    intro i u v
    simp only [M, fromEdgeSet_adj, Set.mem_ofPred_eq, mem_edgeSet]
    exact ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, h1.ne⟩⟩
  refine ⟨M, fun i => ⟨?_, fun u v h => ((hM_adj i u v).mp h).1⟩, fun u v => ?_⟩
  · apply isLinearForest_of_deg_le_one
    intro v
    have hsub : (M i).neighborFinset v ⊆
        (H.edgeFinset.filter fun e => v ∈ e ∧ col e = i).image
          (fun e => if h : v ∈ e then Sym2.Mem.other h else v) := by
      intro w hw
      obtain ⟨hadj, hci⟩ := (hM_adj i v w).mp ((mem_neighborFinset _ v w).mp hw)
      refine Finset.mem_image.mpr ⟨s(v, w), Finset.mem_filter.mpr
        ⟨H.mem_edgeFinset.mpr hadj, by simp, hci⟩, ?_⟩
      rw [dif_pos (by simp)]
      have hspec := @Sym2.other_spec _ v s(v, w) (by simp)
      rcases Sym2.eq_iff.mp hspec with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact False.elim (hadj.ne h1)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (hcol i v))
    simpa only [← Set.ncard_coe_finset, coe_neighborFinset] using hc
  · constructor
    · intro h
      refine ⟨col s(u, v), (hM_adj _ u v).mpr ⟨h, rfl⟩, fun j hj => ?_⟩
      exact ((hM_adj j u v).mp hj).2.symm
    · rintro ⟨i, hi, _⟩
      exact ((hM_adj i u v).mp hi).1

private lemma toGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (V × V)) (D : ℕ)
    (hdeg : ∀ v : V, (F.filter fun e => e.1 = v).card + (F.filter fun e => e.2 = v).card ≤ D)
    (v : V) : (toGraph F).degree v ≤ D := by
  have hsub : (toGraph F).neighborFinset v ⊆
      (F.filter fun e => e.1 = v).image Prod.snd ∪
        (F.filter fun e => e.2 = v).image Prod.fst := by
    intro w hw
    rcases ((toGraph_adj F).mp ((mem_neighborFinset _ v w).mp hw)).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(v, w), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(w, v), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩)
  rw [← (toGraph F).card_neighborFinset_eq_degree]
  calc ((toGraph F).neighborFinset v).card
      ≤ ((F.filter fun e => e.1 = v).image Prod.snd ∪
          (F.filter fun e => e.2 = v).image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ ((F.filter fun e => e.1 = v).image Prod.snd).card +
          ((F.filter fun e => e.2 = v).image Prod.fst).card := Finset.card_union_le _ _
    _ ≤ (F.filter fun e => e.1 = v).card + (F.filter fun e => e.2 = v).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ D := hdeg v

end CycleBreakingAndGreedy

section MainTheorem

private lemma alon_fin_case (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ₀ : ℕ, 1 ≤ Δ₀ ∧ ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        HasLinearForestDecomposition G
          (((Nat.find (Nat.exists_infinite_primes (Nat.ceil (32 / min ε (1 / 2)) + 1))) - 1) *
              (Nat.floor ((1 + 4 * (min ε (1 / 2) / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
                (Nat.find (Nat.exists_infinite_primes (Nat.ceil (32 / min ε (1 / 2)) + 1)))) + 1) +
            2 * (4 * (Nat.floor ((1 + 4 * (min ε (1 / 2) / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
                (Nat.find (Nat.exists_infinite_primes (Nat.ceil (32 / min ε (1 / 2)) + 1)))) + 1) +
              2 * (Nat.find (Nat.exists_infinite_primes (Nat.ceil (32 / min ε (1 / 2)) + 1))))) := by
  let δ : ℝ := min ε (1 / 2)
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  let p_spec := Nat.exists_infinite_primes (Nat.ceil (32 / δ) + 1)
  let p : ℕ := Nat.find p_spec
  have hp_spec : Nat.ceil (32 / δ) + 1 ≤ p ∧ p.Prime := Nat.find_spec p_spec
  have hp_ge : Nat.ceil (32 / δ) + 1 ≤ p := hp_spec.1
  have hp_prime : p.Prime := hp_spec.2
  have : Fact p.Prime := ⟨hp_prime⟩
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  have hp_gt_32 : 32 / δ < (p : ℝ) := by
    have h1 : 32 / δ ≤ (Nat.ceil (32 / δ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (32 / δ) : ℝ) + 1 ≤ p := by exact_mod_cast hp_ge
    linarith
  have hp_65 : 65 ≤ p := by
    have h64_real : (64 : ℝ) < (p : ℝ) := by
      have : (64 : ℝ) ≤ 32 / δ := by
        rw [le_div_iff₀ hδ_pos]; linarith
      linarith
    have h64 : 64 < p := by exact_mod_cast h64_real
    omega
  let t : ℝ := δ / 16
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_half : t ≤ 1 / 2 := by dsimp [t]; linarith
  let c₂ : ℝ := 2 * t ^ 2 / p
  have hc₂_pos : 0 < c₂ := by dsimp [c₂]; positivity
  let d₀ : ℕ := Nat.ceil (96000 * (p : ℝ) / c₂ ^ 5) + 1
  have hd₀_pos : 1 ≤ d₀ := by dsimp [d₀]; omega
  let Δ₀ : ℕ := max (2 * d₀) 2
  refine ⟨Δ₀, by dsimp [Δ₀]; omega, fun Δ hΔ n hn G _ hG => ?_⟩
  let d : ℕ := (Δ + 1) / 2
  have hd_ge : d₀ ≤ d := by
    have h2 : 2 * d₀ ≤ Δ := (le_max_left _ _).trans hΔ
    dsimp [d]; omega
  have hd_pos : 1 ≤ d := hd₀_pos.trans hd_ge
  let k : ℕ := Nat.floor ((1 + 4 * t) * (d : ℝ) / p) + 1
  have hk_pos : 1 ≤ k := by dsimp [k]; omega
  -- Step 1: Balanced orientation
  obtain ⟨dir, hdir_adj, hdir_anti, hdir_deg⟩ := exists_balanced_orientation G
  have hdir_out_le : ∀ v : Fin n, (Finset.univ.filter fun w => dir v w).card ≤ d := fun v => by
    have h1 := (hdir_deg v).1
    have h2 : G.degree v ≤ Δ := (G.degree_le_maxDegree v).trans hG
    omega
  have hdir_in_le : ∀ v : Fin n, (Finset.univ.filter fun w => dir w v).card ≤ d := fun v => by
    have h1 := (hdir_deg v).2
    have h2 : G.degree v ≤ Δ := (G.degree_le_maxDegree v).trans hG
    omega
  -- Step 2: Chernoff + LLL for good coloring c : Fin n → ZMod p
  let supp (v : Fin n) : Finset (Fin n) := insert v (G.neighborFinset v)
  let Bad (v : Fin n) : Finset (Fin n → ZMod p) :=
    Finset.univ.filter fun c => ∃ r : ZMod p,
      k + 1 ≤ ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card ∨
      k + 1 ≤ ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card
  have hBad_dep : ∀ v (X Y : Fin n → ZMod p),
      (∀ x ∈ supp v, X x = Y x) → (X ∈ Bad v ↔ Y ∈ Bad v) := by
    intro v X Y hXY
    have hv : X v = Y v := hXY v (Finset.mem_insert_self v _)
    have hcongr_out : ∀ r : ZMod p,
        ((Finset.univ.filter fun w => dir v w).filter fun w => X w = X v + r) =
          ((Finset.univ.filter fun w => dir v w).filter fun w => Y w = Y v + r) := by
      intro r; apply Finset.filter_congr; intro w hw
      have hadj : G.Adj v w := (hdir_adj v w).mpr (Or.inl (Finset.mem_filter.mp hw).2)
      have hwx := hXY w (Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr hadj))
      rw [hv, hwx]
    have hcongr_in : ∀ r : ZMod p,
        ((Finset.univ.filter fun w => dir w v).filter fun w => X w = X v - r) =
          ((Finset.univ.filter fun w => dir w v).filter fun w => Y w = Y v - r) := by
      intro r; apply Finset.filter_congr; intro w hw
      have hadj : G.Adj v w := (hdir_adj v w).mpr (Or.inr (Finset.mem_filter.mp hw).2)
      have hwx := hXY w (Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr hadj))
      rw [hv, hwx]
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, h | h⟩
      · exact ⟨r, Or.inl (by simpa [hcongr_out r] using h)⟩
      · exact ⟨r, Or.inr (by simpa [hcongr_in r] using h)⟩
    · rintro ⟨r, h | h⟩
      · exact ⟨r, Or.inl (by simpa [← hcongr_out r] using h)⟩
      · exact ⟨r, Or.inr (by simpa [← hcongr_in r] using h)⟩
  let D_lll : ℕ := (Δ + 1) ^ 2
  have hD_lll_pos : 1 ≤ D_lll := by dsimp [D_lll]; nlinarith
  have hdeg_lll : ∀ u : Fin n,
      (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)).card ≤ D_lll := by
    intro u
    have hsub : Finset.univ.filter (fun w : Fin n => ¬ Disjoint (supp w) (supp u)) ⊆
        (supp u).biUnion supp := by
      intro w hw
      obtain ⟨x, hxw, hxu⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hw).2
      refine Finset.mem_biUnion.mpr ⟨x, hxu, ?_⟩
      rcases Finset.mem_insert.mp hxw with rfl | hxw'
      · exact Finset.mem_insert_self x _
      · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset x w).mpr
          ((G.mem_neighborFinset w x).mp hxw').symm)
    have hsupp_card : ∀ x : Fin n, (supp x).card ≤ Δ + 1 := fun x => by
      calc (insert x (G.neighborFinset x)).card
          ≤ (G.neighborFinset x).card + 1 := Finset.card_insert_le _ _
        _ = G.degree x + 1 := by rw [G.card_neighborFinset_eq_degree]
        _ ≤ Δ + 1 := Nat.add_le_add_right ((G.degree_le_maxDegree x).trans hG) 1
    calc (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)).card
        ≤ ((supp u).biUnion supp).card := Finset.card_le_card hsub
      _ ≤ (supp u).card * (Δ + 1) := Finset.card_biUnion_le_card_mul _ _ _ (fun x _ => hsupp_card x)
      _ ≤ (Δ + 1) * (Δ + 1) := Nat.mul_le_mul_right _ (hsupp_card u)
      _ = D_lll := by dsimp [D_lll]; ring
  have hprob_lll : ∀ v : Fin n, (Bad v).card * (D_lll + 1) ^ 2 ≤ (Fintype.card (ZMod p)) ^ n := by
    intro v
    have hk_real : (1 + 4 * t) * (d : ℝ) / p ≤ (k : ℝ) + 1 := by
      have hlt : (1 + 4 * t) * (d : ℝ) / p < (k : ℝ) := by
        dsimp [k]; exact_mod_cast Nat.lt_floor_add_one _
      linarith
    have hBad_sub : Bad v ⊆
        (Finset.univ : Finset (ZMod p)).biUnion (fun r =>
          Finset.univ.filter fun c =>
            k + 1 ≤ ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card) ∪
        (Finset.univ : Finset (ZMod p)).biUnion (fun r =>
          Finset.univ.filter fun c =>
            k + 1 ≤ ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card) := by
      intro c hc
      obtain ⟨r, hr | hr⟩ := (Finset.mem_filter.mp hc).2
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩)
    have hBad_card : ((Bad v).card : ℝ) ≤
        2 * (p : ℝ) * ((p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ)))) := by
      have h1 : (Bad v).card ≤
          (∑ r : ZMod p, (Finset.univ.filter fun c : Fin n → ZMod p =>
            k + 1 ≤ ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card).card) +
          (∑ r : ZMod p, (Finset.univ.filter fun c : Fin n → ZMod p =>
            k + 1 ≤ ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card).card) := by
        exact (Finset.card_le_card hBad_sub).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le))
      have hv_out : v ∉ Finset.univ.filter fun w => dir v w := fun h =>
        hdir_anti v v (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h).2
      have hv_in : v ∉ Finset.univ.filter fun w => dir w v := fun h =>
        hdir_anti v v (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h).2
      have hce_eq : 2 * t ^ 2 * (d : ℝ) / p = c₂ * (d : ℝ) := by dsimp [c₂]; ring
      have hout_bd : ∀ r : ZMod p, ((Finset.univ.filter fun c : Fin n → ZMod p =>
          k + 1 ≤ ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card).card : ℝ) ≤
          (p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ))) := fun r => by
        rw [← hce_eq]
        exact chernoff_vertex_bound v (Finset.univ.filter fun w => dir v w) hv_out (hdir_out_le v)
          (fun z => z + r) t ht_pos.le ht_half hk_real
      have hin_bd : ∀ r : ZMod p, ((Finset.univ.filter fun c : Fin n → ZMod p =>
          k + 1 ≤ ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card).card : ℝ) ≤
          (p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ))) := fun r => by
        rw [← hce_eq]
        exact chernoff_vertex_bound v (Finset.univ.filter fun w => dir w v) hv_in (hdir_in_le v)
          (fun z => z - r) t ht_pos.le ht_half hk_real
      have h1r := (Nat.cast_le (α := ℝ)).mpr h1
      apply h1r.trans
      push_cast
      calc (∑ r : ZMod p, ((Finset.univ.filter fun c : Fin n → ZMod p =>
              k + 1 ≤ ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card).card : ℝ)) +
            (∑ r : ZMod p, ((Finset.univ.filter fun c : Fin n → ZMod p =>
              k + 1 ≤ ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card).card : ℝ))
          ≤ (∑ _r : ZMod p, (p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ)))) +
              (∑ _r : ZMod p, (p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ)))) :=
            add_le_add (Finset.sum_le_sum fun r _ => hout_bd r) (Finset.sum_le_sum fun r _ => hin_bd r)
        _ = 2 * (p : ℝ) * ((p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ)))) := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
            ring
    have hD_bd : ((D_lll + 1 : ℕ) : ℝ) ^ 2 ≤ 400 * (d : ℝ) ^ 4 := by
      have hd_real : (1 : ℝ) ≤ d := by exact_mod_cast hd_pos
      have hΔ_bd : (Δ : ℝ) ≤ 2 * (d : ℝ) := by
        exact_mod_cast (show Δ ≤ 2 * ((Δ + 1) / 2) by omega)
      have hstep1 : ((D_lll + 1 : ℕ) : ℝ) ≤ 5 * (d + 1 : ℝ) ^ 2 := by
        dsimp [D_lll]
        push_cast
        nlinarith
      have hstep2 : (d + 1 : ℝ) ≤ 2 * (d : ℝ) := by linarith
      calc ((D_lll + 1 : ℕ) : ℝ) ^ 2 ≤ (5 * (d + 1 : ℝ) ^ 2) ^ 2 := by gcongr
        _ = 25 * (d + 1 : ℝ) ^ 4 := by ring
        _ ≤ 25 * (2 * (d : ℝ)) ^ 4 := by gcongr
        _ = 400 * (d : ℝ) ^ 4 := by ring
    have hexp_bd : 800 * (p : ℝ) * (d : ℝ) ^ 4 ≤ Real.exp (c₂ * (d : ℝ)) := by
      have hd_nn : (0 : ℝ) ≤ c₂ * (d : ℝ) := by positivity
      have hpow := Real.pow_div_factorial_le_exp (c₂ * (d : ℝ)) hd_nn 5
      have h5 : (Nat.factorial 5 : ℝ) = 120 := by norm_num
      rw [h5] at hpow
      have hd0_le : 96000 * (p : ℝ) / c₂ ^ 5 ≤ (d : ℝ) := by
        have h1 : 96000 * (p : ℝ) / c₂ ^ 5 ≤ (d₀ : ℝ) := by
          have : 96000 * (p : ℝ) / c₂ ^ 5 ≤ (Nat.ceil (96000 * (p : ℝ) / c₂ ^ 5) : ℝ) := Nat.le_ceil _
          have : (Nat.ceil (96000 * (p : ℝ) / c₂ ^ 5) : ℝ) ≤ d₀ := by
            dsimp [d₀]; exact_mod_cast Nat.le_succ _
          linarith
        exact h1.trans (by exact_mod_cast hd_ge)
      have hc5 : 96000 * (p : ℝ) ≤ c₂ ^ 5 * (d : ℝ) := by
        nlinarith [(div_le_iff₀ (show (0 : ℝ) < c₂ ^ 5 by positivity)).mp hd0_le]
      have hmul : 96000 * (p : ℝ) * (d : ℝ) ^ 4 ≤ (c₂ * (d : ℝ)) ^ 5 := by
        calc 96000 * (p : ℝ) * (d : ℝ) ^ 4 ≤ (c₂ ^ 5 * (d : ℝ)) * (d : ℝ) ^ 4 := by gcongr
          _ = (c₂ * (d : ℝ)) ^ 5 := by ring
      linarith
    have hnat_real : ((Bad v).card : ℝ) * ((D_lll + 1 : ℕ) : ℝ) ^ 2 ≤
        ((Fintype.card (ZMod p) : ℝ) ^ n) := by
      rw [ZMod.card]
      calc ((Bad v).card : ℝ) * ((D_lll + 1 : ℕ) : ℝ) ^ 2
          ≤ (2 * (p : ℝ) * ((p : ℝ) ^ n * Real.exp (-(c₂ * (d : ℝ))))) * (400 * (d : ℝ) ^ 4) :=
            mul_le_mul hBad_card hD_bd (by positivity) (by positivity)
        _ = (p : ℝ) ^ n * ((800 * (p : ℝ) * (d : ℝ) ^ 4) * Real.exp (-(c₂ * (d : ℝ)))) := by ring
        _ ≤ (p : ℝ) ^ n * (Real.exp (c₂ * (d : ℝ)) * Real.exp (-(c₂ * (d : ℝ)))) := by
            gcongr
        _ = (p : ℝ) ^ n := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    exact_mod_cast hnat_real
  obtain ⟨c, hc⟩ := finite_lll_nat hD_lll_pos supp Bad hBad_dep hdeg_lll hprob_lll
  have hc_good : ∀ v : Fin n, ∀ r : ZMod p,
      ((Finset.univ.filter fun w => dir v w).filter fun w => c w = c v + r).card ≤ k ∧
      ((Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r).card ≤ k := by
    have hnot := (Finset.mem_filter.mp hc).2
    intro v r
    by_contra hbad
    apply hnot v
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, r, ?_⟩
    rw [not_and_or] at hbad
    rcases hbad with hbad | hbad
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  -- Step 3 & 4: Decompose H_r (r ≠ 0) via Konig and break cycles
  let H_edge (r : ZMod p) : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun e => dir e.1 e.2 ∧ c e.2 - c e.1 = r
  have hH_out : ∀ r : ZMod p, ∀ u : Fin n,
      ((H_edge r).filter fun e => e.1 = u).card ≤ k := by
    intro r u
    have hsub : ((H_edge r).filter fun e => e.1 = u).image Prod.snd ⊆
        (Finset.univ.filter fun w => dir u w).filter fun w => c w = c u + r := by
      intro w hw
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hw
      have h1 := Finset.mem_filter.mp hab
      have h2 := Finset.mem_filter.mp h1.1
      have ha : a = u := h1.2
      subst ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2.1⟩,
        by linear_combination h2.2.2⟩
    have hinj : Set.InjOn Prod.snd (((H_edge r).filter fun e => e.1 = u) : Set (Fin n × Fin n)) := by
      rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      have ha₁ : a₁ = u := (Finset.mem_filter.mp h₁).2
      have ha₂ : a₂ = u := (Finset.mem_filter.mp h₂).2
      dsimp only at heq
      subst ha₁ ha₂ heq
      rfl
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (hc_good u r).1
  have hH_in : ∀ r : ZMod p, ∀ v : Fin n,
      ((H_edge r).filter fun e => e.2 = v).card ≤ k := by
    intro r v
    have hsub : ((H_edge r).filter fun e => e.2 = v).image Prod.fst ⊆
        (Finset.univ.filter fun w => dir w v).filter fun w => c w = c v - r := by
      intro w hw
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hw
      have h1 := Finset.mem_filter.mp hab
      have h2 := Finset.mem_filter.mp h1.1
      have hb : b = v := h1.2
      subst hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.2.1⟩,
        by linear_combination -h2.2.2⟩
    have hinj : Set.InjOn Prod.fst (((H_edge r).filter fun e => e.2 = v) : Set (Fin n × Fin n)) := by
      rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      have hb₁ : b₁ = v := (Finset.mem_filter.mp h₁).2
      have hb₂ : b₂ = v := (Finset.mem_filter.mp h₂).2
      dsimp only at heq
      subst hb₁ hb₂ heq
      rfl
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (hc_good v r).2
  have hkonig : ∀ r : ZMod p, ∃ F : Fin k → Finset (Fin n × Fin n),
      (∀ j : Fin k, F j ⊆ H_edge r) ∧
      (∀ j : Fin k, ∀ u : Fin n,
        ((F j).filter fun e => e.1 = u).card ≤ 1 ∧
        ((F j).filter fun e => e.2 = u).card ≤ 1) ∧
      (∀ e, e ∈ H_edge r ↔ ∃! j : Fin k, e ∈ F j) :=
    fun r => konig_decompose k (H_edge r) (hH_out r) (hH_in r)
  choose F_all hF_sub hF_deg hF_part using hkonig
  let Rnz : Finset (ZMod p) := Finset.univ.erase 0
  have hRnz_card : Rnz.card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  let eRnz : ↥Rnz ≃ Fin (p - 1) :=
    Fintype.equivFinOfCardEq (by simp [hRnz_card])
  let E_rem (r : ZMod p) (j : Fin k) : Finset (Fin n × Fin n) :=
    (F_all r j).filter fun e => c e.1 = (j.val : ZMod p)
  let F_keep (r : ZMod p) (j : Fin k) : Finset (Fin n × Fin n) :=
    (F_all r j).filter fun e => c e.1 ≠ (j.val : ZMod p)
  have hF_keep_forest : ∀ r ∈ Rnz, ∀ j : Fin k, IsLinearForest (toGraph (F_keep r j)) := by
    intro r hr j
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
    have hsub : F_keep r j ⊆ F_all r j := Finset.filter_subset _ _
    have hirr : ∀ e ∈ F_all r j, e.1 ≠ e.2 := by
      intro e he heq
      have hdir := (Finset.mem_filter.mp (hF_sub r j he)).2.1
      rw [heq] at hdir
      exact hdir_anti e.2 e.2 hdir hdir
    have hanti : ∀ u v, (u, v) ∈ F_all r j → (v, u) ∉ F_all r j := by
      intro u v h1 h2
      exact hdir_anti u v (Finset.mem_filter.mp (hF_sub r j h1)).2.1
        (Finset.mem_filter.mp (hF_sub r j h2)).2.1
    have hdiff : ∀ e ∈ F_all r j, c e.2 - c e.1 = r := fun e he =>
      (Finset.mem_filter.mp (hF_sub r j he)).2.2
    have hanti' : ∀ u v, (u, v) ∈ F_keep r j → (v, u) ∉ F_keep r j := fun u v h1 h2 =>
      hanti u v (hsub h1) (hsub h2)
    have hdeg' : ∀ v : Fin n,
        ((F_keep r j).filter fun e => e.1 = v).card ≤ 1 ∧
        ((F_keep r j).filter fun e => e.2 = v).card ≤ 1 := fun v =>
      ⟨(Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hF_deg r j v).1,
       (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hF_deg r j v).2⟩
    exact isLinearForest_toGraph_of_deg_le_one_acyclic (F_keep r j) hanti' hdeg'
      (residue_cut_acyclic p r (j.val : ZMod p) hr0 c (F_all r j) hirr hanti (hF_deg r j) hdiff)
  -- Step 5: Leftover graph L and greedy matching decomposition
  let L_dir : Finset (Fin n × Fin n) :=
    H_edge 0 ∪ (Rnz.biUnion fun r => (Finset.univ : Finset (Fin k)).biUnion fun j => E_rem r j)
  have hL_sub : ∀ e ∈ L_dir, dir e.1 e.2 := by
    intro e he
    rcases Finset.mem_union.mp he with h0 | hrem
    · exact (Finset.mem_filter.mp h0).2.1
    · obtain ⟨r, _, hrem1⟩ := Finset.mem_biUnion.mp hrem
      obtain ⟨j, _, he_rem⟩ := Finset.mem_biUnion.mp hrem1
      exact (Finset.mem_filter.mp (hF_sub r j (Finset.filter_subset _ _ he_rem))).2.1
  let L_graph : SimpleGraph (Fin n) := toGraph L_dir
  have hL_sub_G : L_graph ≤ G := by
    intro u v huv
    rcases ((toGraph_adj L_dir).mp huv).2 with h | h
    · exact (hdir_adj u v).mpr (Or.inl (hL_sub (u, v) h))
    · exact (hdir_adj u v).mpr (Or.inr (hL_sub (v, u) h))
  have hJ_card : ∀ a : ZMod p,
      ((Finset.univ : Finset (Fin k)).filter fun j => (j.val : ZMod p) = a).card ≤ k / p + 1 := by
    intro a
    let J := (Finset.univ : Finset (Fin k)).filter fun j => (j.val : ZMod p) = a
    have hinj : Set.InjOn (fun j : Fin k => j.val / p) (J : Set (Fin k)) := by
      intro j₁ hj₁ j₂ hj₂ heq
      have h1 : (j₁.val : ZMod p) = a := (Finset.mem_filter.mp hj₁).2
      have h2 : (j₂.val : ZMod p) = a := (Finset.mem_filter.mp hj₂).2
      have hmod : j₁.val % p = j₂.val % p := by
        have hv1 : (j₁.val % p : ℕ) = a.val := by
          have := congrArg ZMod.val h1
          simpa [ZMod.val_natCast] using this
        have hv2 : (j₂.val % p : ℕ) = a.val := by
          have := congrArg ZMod.val h2
          simpa [ZMod.val_natCast] using this
        exact hv1.trans hv2.symm
      dsimp only at heq
      apply Fin.ext
      have hd1 := Nat.div_add_mod j₁.val p
      have hd2 := Nat.div_add_mod j₂.val p
      rw [← hd1, ← hd2, heq, hmod]
    have hsub : J.image (fun j : Fin k => j.val / p) ⊆ Finset.range (k / p + 1) := by
      intro q hq
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right j.isLt.le))
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (by simp)
  have hrem_out : ∀ u : Fin n,
      ((Rnz.biUnion fun r => (Finset.univ : Finset (Fin k)).biUnion fun j => E_rem r j).filter
        fun e => e.1 = u).card ≤ k + p := by
    intro u
    let J_u := (Finset.univ : Finset (Fin k)).filter fun j => c u = (j.val : ZMod p)
    have hsub : (Rnz.biUnion fun r => (Finset.univ : Finset (Fin k)).biUnion fun j => E_rem r j).filter
        (fun e => e.1 = u) ⊆
        (Rnz ×ˢ J_u).biUnion (fun p_rj => (E_rem p_rj.1 p_rj.2).filter fun e => e.1 = u) := by
      intro e he
      have he' := Finset.mem_filter.mp he
      obtain ⟨r, hr, hrem1⟩ := Finset.mem_biUnion.mp he'.1
      obtain ⟨j, _, he_rem⟩ := Finset.mem_biUnion.mp hrem1
      have hc_eq : c u = (j.val : ZMod p) := by
        have := (Finset.mem_filter.mp he_rem).2
        rw [← he'.2]; exact this
      exact Finset.mem_biUnion.mpr ⟨(r, j), Finset.mem_product.mpr
        ⟨hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_eq⟩⟩,
        Finset.mem_filter.mpr ⟨he_rem, he'.2⟩⟩
    have hc1 : ∀ p_rj ∈ Rnz ×ˢ J_u, ((E_rem p_rj.1 p_rj.2).filter fun e => e.1 = u).card ≤ 1 := by
      rintro ⟨r, j⟩ _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
        (hF_deg r j u).1
    have hcard_Ju : J_u.card ≤ k / p + 1 := by
      simpa [J_u, eq_comm] using hJ_card (c u)
    have hprod_bd : (Rnz ×ˢ J_u).card ≤ (p - 1) * (k / p + 1) := by
      rw [Finset.card_product, hRnz_card]
      exact Nat.mul_le_mul_left _ hcard_Ju
    have hmul_bd : (p - 1) * (k / p + 1) ≤ k + p := by
      have hk1 : (p - 1) * (k / p) ≤ p * (k / p) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      have hk2 : p * (k / p) ≤ k := Nat.mul_div_le k p
      nlinarith [show p - 1 ≤ p by omega]
    exact ((Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ 1 hc1)).trans
      (by simpa using hprod_bd.trans hmul_bd)
  have hrem_in : ∀ v : Fin n,
      ((Rnz.biUnion fun r => (Finset.univ : Finset (Fin k)).biUnion fun j => E_rem r j).filter
        fun e => e.2 = v).card ≤ k + p := by
    intro v
    have hsub : (Rnz.biUnion fun r => (Finset.univ : Finset (Fin k)).biUnion fun j => E_rem r j).filter
        (fun e => e.2 = v) ⊆
        Rnz.biUnion (fun r =>
          (((Finset.univ : Finset (Fin k)).filter fun j => (j.val : ZMod p) = c v - r)).biUnion
            (fun j => (E_rem r j).filter fun e => e.2 = v)) := by
      intro e he
      have he' := Finset.mem_filter.mp he
      obtain ⟨r, hr, hrem1⟩ := Finset.mem_biUnion.mp he'.1
      obtain ⟨j, _, he_rem⟩ := Finset.mem_biUnion.mp hrem1
      have hdiff : c e.2 - c e.1 = r :=
        (Finset.mem_filter.mp (hF_sub r j (Finset.filter_subset _ _ he_rem))).2.2
      have hce1 : c e.1 = (j.val : ZMod p) := (Finset.mem_filter.mp he_rem).2
      have hj_eq : (j.val : ZMod p) = c v - r := by
        rw [← hce1, ← he'.2]; linear_combination -hdiff
      exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_eq⟩,
          Finset.mem_filter.mpr ⟨he_rem, he'.2⟩⟩⟩
    have hc_r : ∀ r ∈ Rnz,
        ((((Finset.univ : Finset (Fin k)).filter fun j => (j.val : ZMod p) = c v - r)).biUnion
          (fun j => (E_rem r j).filter fun e => e.2 = v)).card ≤ k / p + 1 := by
      intro r _
      have hc1 : ∀ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => (j.val : ZMod p) = c v - r),
          ((E_rem r j).filter fun e => e.2 = v).card ≤ 1 := fun j _ =>
        (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
          (hF_deg r j v).2
      exact (Finset.card_biUnion_le_card_mul _ _ 1 hc1).trans (by simpa using hJ_card (c v - r))
    have hmul_bd : (p - 1) * (k / p + 1) ≤ k + p := by
      have hk1 : (p - 1) * (k / p) ≤ p * (k / p) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      have hk2 : p * (k / p) ≤ k := Nat.mul_div_le k p
      nlinarith [show p - 1 ≤ p by omega]
    exact ((Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le_card_mul _ _ (k / p + 1) hc_r)).trans
      (by rw [hRnz_card]; exact hmul_bd)
  let D_L : ℕ := 4 * k + 2 * p
  have hDL_pos : 1 ≤ D_L := by dsimp [D_L]; omega
  have hL_deg : ∀ v : Fin n, L_graph.degree v ≤ D_L := fun v =>
    toGraph_degree_le L_dir D_L (fun u => by
      have hout_L : (L_dir.filter fun e => e.1 = u).card ≤ 2 * k + p := by
        dsimp only [L_dir]
        rw [Finset.filter_union]
        have h_sum := (Finset.card_union_le _ _).trans (Nat.add_le_add (hH_out 0 u) (hrem_out u))
        omega
      have hin_L : (L_dir.filter fun e => e.2 = u).card ≤ 2 * k + p := by
        dsimp only [L_dir]
        rw [Finset.filter_union]
        have h_sum := (Finset.card_union_le _ _).trans (Nat.add_le_add (hH_in 0 u) (hrem_in u))
        omega
      dsimp only [D_L]; omega) v
  obtain ⟨M, hM_lf, hM_part⟩ := greedy_matching_decompose L_graph D_L hDL_pos hL_deg
  -- Combine all (p - 1) * k + 2 * D_L linear forests
  let eProd : Fin (p - 1) × Fin k ≃ Fin ((p - 1) * k) := finProdFinEquiv
  let D_forest : Fin ((p - 1) * k + 2 * D_L) → SimpleGraph (Fin n) :=
    Fin.addCases
      (fun idx =>
        let pr := eProd.symm idx
        toGraph (F_keep (eRnz.symm pr.1).1 pr.2))
      (fun idx => M idx)
  refine ⟨D_forest, fun i => ?_, fun u v => ?_⟩
  · refine Fin.addCases ?_ ?_ i
    · intro idx
      dsimp only [D_forest]
      erw [Fin.addCases_left]
      let pr := eProd.symm idx
      have hr : (eRnz.symm pr.1).1 ∈ Rnz := (eRnz.symm pr.1).2
      refine ⟨hF_keep_forest _ hr pr.2, fun u v huv => ?_⟩
      rcases ((toGraph_adj _).mp huv).2 with h | h
      · exact (hdir_adj u v).mpr (Or.inl (Finset.mem_filter.mp
          (hF_sub _ pr.2 (Finset.filter_subset _ _ h))).2.1)
      · exact (hdir_adj u v).mpr (Or.inr (Finset.mem_filter.mp
          (hF_sub _ pr.2 (Finset.filter_subset _ _ h))).2.1)
    · intro idx
      dsimp only [D_forest]
      erw [Fin.addCases_right]
      exact ⟨(hM_lf idx).1, (hM_lf idx).2.trans hL_sub_G⟩
  · constructor
    · intro huv
      have hdir_pair : ∃ a b : Fin n, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧ dir a b := by
        rcases (hdir_adj u v).mp huv with h | h
        · exact ⟨u, v, Or.inl ⟨rfl, rfl⟩, h⟩
        · exact ⟨v, u, Or.inr ⟨rfl, rfl⟩, h⟩
      rcases hdir_pair with ⟨a, b, hab_eq, hab_dir⟩
      have hne_uv : u ≠ v := huv.ne
      have hab_mem_H : (a, b) ∈ H_edge (c b - c a) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab_dir, rfl⟩
      have hL_not_Fkeep : (a, b) ∈ L_dir →
          ∀ (r' : ↥Rnz) (j' : Fin k), ¬ (toGraph (F_keep r'.1 j')).Adj u v := by
        intro hL r' j' hadj'
        have hmem_keep : (a, b) ∈ F_keep r'.1 j' := by
          rcases ((toGraph_adj _).mp hadj').2 with h | h
          · have h1 : dir u v := (Finset.mem_filter.mp
              (hF_sub r'.1 j' (Finset.filter_subset _ _ h))).2.1
            rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
            · rw [hau, hbv]; exact h
            · exact False.elim (hdir_anti _ _ hab_dir (by rw [hav, hbu]; exact h1))
          · have h1 : dir v u := (Finset.mem_filter.mp
              (hF_sub r'.1 j' (Finset.filter_subset _ _ h))).2.1
            rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
            · exact False.elim (hdir_anti _ _ hab_dir (by rw [hau, hbv]; exact h1))
            · rw [hav, hbu]; exact h
        have hsub1 := Finset.filter_subset _ _ hmem_keep
        have hsub2 := hF_sub r'.1 j' hsub1
        rcases Finset.mem_union.mp hL with h0 | hrem
        · have hr0 : c b - c a = 0 := (Finset.mem_filter.mp h0).2.2
          have hrr' : c b - c a = r'.1 := (Finset.mem_filter.mp hsub2).2.2
          exact (Finset.mem_erase.mp r'.2).1 (hrr'.symm.trans hr0)
        · obtain ⟨r'', _, hrem1⟩ := Finset.mem_biUnion.mp hrem
          obtain ⟨j'', _, he_rem⟩ := Finset.mem_biUnion.mp hrem1
          have hmem'' := Finset.filter_subset _ _ he_rem
          have hrr'' : c b - c a = r'' := (Finset.mem_filter.mp (hF_sub r'' j'' hmem'')).2.2
          have hrr' : c b - c a = r'.1 := (Finset.mem_filter.mp hsub2).2.2
          have hr_eq : r'' = r'.1 := hrr''.symm.trans hrr'
          subst hr_eq
          have hj_eq : j'' = j' := ((hF_part r'.1 (a, b)).mp (hrr' ▸ hab_mem_H)).unique hmem'' hsub1
          subst hj_eq
          exact (Finset.mem_filter.mp hmem_keep).2 (Finset.mem_filter.mp he_rem).2
      have handle_L : (a, b) ∈ L_dir → ∃! i, (D_forest i).Adj u v := by
        intro hL
        have hLadj : L_graph.Adj u v := (toGraph_adj L_dir).mpr ⟨hne_uv, by
          rcases hab_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl hL
          · exact Or.inr hL⟩
        obtain ⟨iM, hiM, huniqM⟩ := (hM_part u v).mp hLadj
        refine ⟨Fin.natAdd ((p - 1) * k) iM, ?_, ?_⟩
        · simp [D_forest, hiM]
        · intro i hi
          induction i using Fin.addCases with
          | left idx =>
            dsimp only [D_forest] at hi
            erw [Fin.addCases_left] at hi
            exact False.elim (hL_not_Fkeep hL _ _ hi)
          | right idx =>
            dsimp only [D_forest] at hi
            erw [Fin.addCases_right] at hi
            rw [huniqM idx hi]
      by_cases hr0 : c b - c a = 0
      · exact handle_L (Finset.mem_union_left _ (hr0 ▸ hab_mem_H))
      · have hrRnz : c b - c a ∈ Rnz := Finset.mem_erase.mpr ⟨hr0, Finset.mem_univ _⟩
        obtain ⟨j, hj, huniq_j⟩ := (hF_part (c b - c a) (a, b)).mp hab_mem_H
        by_cases hrem : c a = (j.val : ZMod p)
        · exact handle_L (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c b - c a, hrRnz,
            Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hj, hrem⟩⟩⟩))
        · let r' : ↥Rnz := ⟨c b - c a, hrRnz⟩
          let idx0 : Fin ((p - 1) * k) := eProd (eRnz r', j)
          have hkeep_ab : (a, b) ∈ F_keep r'.1 j := Finset.mem_filter.mpr ⟨hj, hrem⟩
          have hkeep_uv : (toGraph (F_keep r'.1 j)).Adj u v := (toGraph_adj _).mpr ⟨hne_uv, by
            rcases hab_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl hkeep_ab
            · exact Or.inr hkeep_ab⟩
          refine ⟨Fin.castAdd (2 * D_L) idx0, ?_, ?_⟩
          · simpa [D_forest, idx0] using hkeep_uv
          · intro i hi
            induction i using Fin.addCases with
            | left idx =>
              dsimp only [D_forest] at hi
              erw [Fin.addCases_left] at hi
              let pr := eProd.symm idx
              let r'' := (eRnz.symm pr.1).1
              have hcab : (a, b) ∈ F_keep r'' pr.2 := by
                rcases ((toGraph_adj _).mp hi).2 with h | h
                · have hdir' := (Finset.mem_filter.mp (hF_sub r'' pr.2 (Finset.filter_subset _ _ h))).2.1
                  rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
                  · rw [hau, hbv]; exact h
                  · exact False.elim (hdir_anti _ _ hab_dir (by rw [hav, hbu]; exact hdir'))
                · have hdir' := (Finset.mem_filter.mp (hF_sub r'' pr.2 (Finset.filter_subset _ _ h))).2.1
                  rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
                  · exact False.elim (hdir_anti _ _ hab_dir (by rw [hau, hbv]; exact hdir'))
                  · rw [hav, hbu]; exact h
              have hsub'' := hF_sub r'' pr.2 (Finset.filter_subset _ _ hcab)
              have hr_eq : r'' = c b - c a := (Finset.mem_filter.mp hsub'').2.2.symm
              have hr_sub : eRnz.symm pr.1 = r' := Subtype.ext hr_eq
              have hr1 : pr.1 = eRnz r' := by rw [← hr_sub, eRnz.apply_symm_apply]
              have hj_eq : pr.2 = j := by
                apply huniq_j pr.2
                rw [← hr_eq]
                exact Finset.filter_subset _ _ hcab
              have hidx_eq : idx = idx0 := by
                apply eProd.symm.injective
                apply Prod.ext <;> simp [idx0, pr, hr1, hj_eq]
              rw [hidx_eq]
            | right idx =>
              dsimp only [D_forest] at hi
              erw [Fin.addCases_right] at hi
              have hLadj := (hM_lf idx).2 hi
              rcases ((toGraph_adj L_dir).mp hLadj).2 with hL | hL
              · have hdir' := hL_sub (u, v) hL
                have hLab : (a, b) ∈ L_dir := by
                  rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
                  · rw [hau, hbv]; exact hL
                  · exact False.elim (hdir_anti _ _ hab_dir (by rw [hav, hbu]; exact hdir'))
                exact False.elim (hL_not_Fkeep hLab r' j hkeep_uv)
              · have hdir' := hL_sub (v, u) hL
                have hLab : (a, b) ∈ L_dir := by
                  rcases hab_eq with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
                  · exact False.elim (hdir_anti _ _ hab_dir (by rw [hau, hbv]; exact hdir'))
                  · rw [hav, hbu]; exact hL
                exact False.elim (hL_not_Fkeep hLab r' j hkeep_uv)
    · rintro ⟨i, hi, _⟩
      induction i using Fin.addCases with
      | left idx =>
        dsimp only [D_forest] at hi
        erw [Fin.addCases_left] at hi
        rcases ((toGraph_adj _).mp hi).2 with h | h
        · exact (hdir_adj u v).mpr (Or.inl (Finset.mem_filter.mp
            (hF_sub _ _ (Finset.filter_subset _ _ h))).2.1)
        · exact (hdir_adj u v).mpr (Or.inr (Finset.mem_filter.mp
            (hF_sub _ _ (Finset.filter_subset _ _ h))).2.1)
      | right idx =>
        dsimp only [D_forest] at hi
        erw [Fin.addCases_right] at hi
        exact hL_sub_G ((hM_lf idx).2 hi)

private lemma isLinearForest_comap {V W : Type} (e : V ≃ W) {F : SimpleGraph W}
    (hF : IsLinearForest F) : IsLinearForest (F.comap e) := by
  refine ⟨?_, fun v => ?_⟩
  · intro v p hp
    let hom : F.comap e →g F := ⟨e, fun h => h⟩
    exact hF.1 _ (hp.map (f := hom) e.injective)
  · have heq : (F.comap e).neighborSet v = e.symm '' F.neighborSet (e v) := by
      ext w
      simp [SimpleGraph.mem_neighborSet]
    rw [heq, Set.ncard_image_of_injective _ e.symm.injective]
    exact hF.2 (e v)

private lemma linearArboricity_alon (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ := by
  let δ : ℝ := min ε (1 / 2)
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_half : δ ≤ 1 / 2 := min_le_right _ _
  let p_spec := Nat.exists_infinite_primes (Nat.ceil (32 / δ) + 1)
  let p : ℕ := Nat.find p_spec
  have hp_spec : Nat.ceil (32 / δ) + 1 ≤ p ∧ p.Prime := Nat.find_spec p_spec
  have hp_ge : Nat.ceil (32 / δ) + 1 ≤ p := hp_spec.1
  have hp_prime : p.Prime := hp_spec.2
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  have hp_gt_32 : 32 / δ < (p : ℝ) := by
    have h1 : 32 / δ ≤ (Nat.ceil (32 / δ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (32 / δ) : ℝ) + 1 ≤ p := by exact_mod_cast hp_ge
    linarith
  obtain ⟨Δ₁, hΔ₁_pos, hfin⟩ := alon_fin_case ε hε
  let Δ₀ : ℕ := max Δ₁ (Nat.ceil ((2 / δ) * (5 * (p : ℝ) + 8)) + 1)
  refine ⟨Δ₀, fun Δ hΔ V _ G _ hG => ?_⟩
  by_cases hempty : IsEmpty V
  · have hbot : HasLinearForestDecomposition G 0 :=
      ⟨Fin.elim0, fun i => Fin.elim0 i, fun u _ => (hempty.false u).elim⟩
    have hla0 : linearArboricity G = 0 :=
      Nat.eq_zero_of_le_zero (Nat.sInf_le hbot)
    rw [hla0, Nat.cast_zero]
    positivity
  · rw [not_isEmpty_iff] at hempty
    let n : ℕ := Fintype.card V
    have hn : 1 ≤ n := Fintype.card_pos
    let e : V ≃ Fin n := Fintype.equivFin V
    let G' : SimpleGraph (Fin n) := G.comap e.symm
    have hG'_max : G'.maxDegree ≤ Δ := by
      apply G'.maxDegree_le_of_forall_degree_le Δ
      intro i
      have hdeg_eq : G'.degree i = G.degree (e.symm i) := by
        rw [← G'.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree]
        refine Finset.card_bij (fun j _ => e.symm j) ?_ ?_ ?_
        · intro j hj
          exact (G.mem_neighborFinset _ _).mpr ((G'.mem_neighborFinset _ _).mp hj)
        · intro j₁ _ j₂ _ h; exact e.symm.injective h
        · intro w hw
          refine ⟨e w, (G'.mem_neighborFinset _ _).mpr ?_, e.symm_apply_apply w⟩
          simpa [G', e.symm_apply_apply] using (G.mem_neighborFinset _ _).mp hw
      rw [hdeg_eq]
      exact (G.degree_le_maxDegree (e.symm i)).trans hG
    have hΔ₁ : Δ₁ ≤ Δ := (le_max_left _ _).trans hΔ
    have hdec' := hfin Δ hΔ₁ n hn G' hG'_max
    obtain ⟨D', hD'lf, hD'part⟩ := hdec'
    let D := fun i => (D' i).comap e
    have hdec : HasLinearForestDecomposition G
        (((Nat.find p_spec) - 1) * (Nat.floor ((1 + 4 * (δ / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
            (Nat.find p_spec)) + 1) +
          2 * (4 * (Nat.floor ((1 + 4 * (δ / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
            (Nat.find p_spec)) + 1) + 2 * (Nat.find p_spec))) := by
      refine ⟨D, fun i => ⟨isLinearForest_comap e (hD'lf i).1, fun u v huv => ?_⟩, fun u v => ?_⟩
      · have h1 := (hD'lf i).2 huv
        simpa [G', e.symm_apply_apply] using h1
      · have h1 : G.Adj u v ↔ G'.Adj (e u) (e v) := by
          simp [G', e.symm_apply_apply]
        rw [h1]
        simpa [D] using hD'part (e u) (e v)
    have hla_le : linearArboricity G ≤
        (((Nat.find p_spec) - 1) * (Nat.floor ((1 + 4 * (δ / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
            (Nat.find p_spec)) + 1) +
          2 * (4 * (Nat.floor ((1 + 4 * (δ / 16)) * (((Δ + 1) / 2 : ℕ) : ℝ) /
            (Nat.find p_spec)) + 1) + 2 * (Nat.find p_spec))) :=
      Nat.sInf_le (s := {k | HasLinearForestDecomposition G k}) hdec
    have hla_real := (Nat.cast_le (α := ℝ)).mpr hla_le
    apply hla_real.trans
    let t : ℝ := δ / 16
    let d : ℕ := (Δ + 1) / 2
    let k : ℕ := Nat.floor ((1 + 4 * t) * (d : ℝ) / p) + 1
    change (((p - 1) * k + 2 * (4 * k + 2 * p) : ℕ) : ℝ) ≤ (1 / 2 + ε) * (Δ : ℝ)
    have hk_le : (k : ℝ) ≤ (1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ)) + 1 := by
      have hfl : (Nat.floor ((1 + 4 * t) * (d : ℝ) / p) : ℝ) ≤ (1 + 4 * t) * (d : ℝ) / p :=
        Nat.floor_le (by positivity)
      have hd_le : (d : ℝ) ≤ ((Δ : ℝ) + 1) / 2 := by
        have : 2 * d ≤ Δ + 1 := Nat.mul_div_le (Δ + 1) 2
        have : (2 : ℝ) * (d : ℝ) ≤ (Δ : ℝ) + 1 := by exact_mod_cast this
        linarith
      have h4t : 1 + 4 * t = 1 + δ / 4 := by dsimp [t]; ring
      rw [h4t] at hfl
      dsimp [k]
      push_cast
      rw [h4t]
      calc (Nat.floor ((1 + δ / 4) * (d : ℝ) / p) : ℝ) + 1
          ≤ (1 + δ / 4) * (d : ℝ) / p + 1 := by linarith
        _ ≤ (1 + δ / 4) * (((Δ : ℝ) + 1) / 2) / p + 1 := by gcongr
        _ = (1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ)) + 1 := by ring
    have hp1 : 1 ≤ p := hp_prime.pos
    have hnat_eq : ((p - 1) * k + 2 * (4 * k + 2 * p) : ℕ) = (p + 7) * k + 4 * p := by
      zify [hp1]; ring
    rw [hnat_eq]
    push_cast
    have h7_le : 7 / (p : ℝ) ≤ δ / 4 := by
      have h1 : 32 < δ * (p : ℝ) := (div_lt_iff₀' hδ_pos).mp hp_gt_32
      rw [div_le_iff₀ hp_pos_real]
      linarith
    have hprod_bd : ((p : ℝ) + 7) * ((1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ)) + 1) + 4 * (p : ℝ) ≤
        (1 / 2 + 17 / 64 * δ) * ((Δ : ℝ) + 1) + 5 * (p : ℝ) + 7 := by
      have hfac : ((p : ℝ) + 7) * ((1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ))) =
          ((1 + 7 / (p : ℝ)) * (1 + δ / 4) / 2) * ((Δ : ℝ) + 1) := by
        field_simp
      have hcoeff : (1 + 7 / (p : ℝ)) * (1 + δ / 4) / 2 ≤ 1 / 2 + 17 / 64 * δ := by
        have h1 : (1 + 7 / (p : ℝ)) * (1 + δ / 4) ≤ (1 + δ / 4) * (1 + δ / 4) := by gcongr
        nlinarith
      calc ((p : ℝ) + 7) * ((1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ)) + 1) + 4 * (p : ℝ)
          = ((p : ℝ) + 7) * ((1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ))) + 5 * (p : ℝ) + 7 := by ring
        _ = ((1 + 7 / (p : ℝ)) * (1 + δ / 4) / 2) * ((Δ : ℝ) + 1) + 5 * (p : ℝ) + 7 := by rw [hfac]
        _ ≤ (1 / 2 + 17 / 64 * δ) * ((Δ : ℝ) + 1) + 5 * (p : ℝ) + 7 := by gcongr
    have hΔ_bd : (2 / δ) * (5 * (p : ℝ) + 8) ≤ (Δ : ℝ) := by
      have h1 : (2 / δ) * (5 * (p : ℝ) + 8) ≤ (Nat.ceil ((2 / δ) * (5 * (p : ℝ) + 8)) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil ((2 / δ) * (5 * (p : ℝ) + 8)) : ℝ) ≤ Δ := by
        exact_mod_cast (le_trans (Nat.le_succ _) ((le_max_right _ _).trans hΔ))
      exact h1.trans h2
    have hlin : 5 * (p : ℝ) + 8 ≤ δ / 2 * (Δ : ℝ) := by
      have : (2 / δ) * (5 * (p : ℝ) + 8) ≤ (Δ : ℝ) := hΔ_bd
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ δ / 2)
      have heq : δ / 2 * ((2 / δ) * (5 * (p : ℝ) + 8)) = 5 * (p : ℝ) + 8 := by
        field_simp
      linarith
    calc ((p : ℝ) + 7) * (k : ℝ) + 4 * (p : ℝ)
        ≤ ((p : ℝ) + 7) * ((1 + δ / 4) * ((Δ : ℝ) + 1) / (2 * (p : ℝ)) + 1) + 4 * (p : ℝ) := by
          gcongr
      _ ≤ (1 / 2 + 17 / 64 * δ) * ((Δ : ℝ) + 1) + 5 * (p : ℝ) + 7 := hprod_bd
      _ ≤ (1 / 2 + δ / 2) * (Δ : ℝ) + (5 * (p : ℝ) + 8) := by nlinarith
      _ ≤ (1 / 2 + δ) * (Δ : ℝ) := by linarith
      _ ≤ (1 / 2 + ε) * (Δ : ℝ) := by gcongr

end MainTheorem

end AlonLinearArboricity

theorem OMA.solution :
    type_of% @LinearArboricityConjecture.linear_arboricity_conjecture.variants.alon :=
  AlonLinearArboricity.linearArboricity_alon
