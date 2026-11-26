import FormalConjectures.ErdosProblems.«767»

/-! Czipszer bound: a vertex of degree at most k+1 exists in every nonempty vertex set (longest-path argument), hence at most (k+1)n edges. -/

open SimpleGraph Erdos767

namespace OMA
lemma edge_from_start_of_isPath {V : Type*} {G : SimpleGraph V} {u w y : V} (q : G.Walk u w)
    (hq : q.IsPath) (he : s(u, y) ∈ q.edges) : y = q.snd := by
  cases q with
  | nil => simp at he
  | cons h r =>
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · simp
    · exact absurd (r.fst_mem_support_of_mem_edges he) hq.2

lemma exists_low_degree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hG : ¬ HasCycleWithIncidentChords G k) (S : Finset V)
    (hS : S.Nonempty) : ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ k + 1 := by
  classical
  obtain ⟨s, hs⟩ := hS
  let P : ℕ → Prop := fun m => ∃ (u w : V) (p : G.Walk u w), p.IsPath ∧
    (∀ z ∈ p.support, z ∈ S) ∧ p.length = m
  have hP0 : P 0 := ⟨s, s, Walk.nil, by simp, by simp [hs], rfl⟩
  have hPb : ∀ m, P m → m ≤ Fintype.card V := by
    rintro m ⟨u, w, p, hp, -, rfl⟩
    exact hp.length_lt.le
  obtain ⟨u, w, p, hp, hpS, hpl⟩ : P (Nat.findGreatest P (Fintype.card V)) :=
    Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ m, P m → m ≤ Nat.findGreatest P (Fintype.card V) :=
    fun m hm => Nat.le_findGreatest (hPb m hm) hm
  refine ⟨u, hpS u p.start_mem_support, ?_⟩
  by_contra hlt
  push Not at hlt
  set N := S.filter (G.Adj u) with hNdef
  have hN : ∀ y ∈ N, y ∈ p.support := by
    intro y hy
    rw [Finset.mem_filter] at hy
    by_contra hyp
    have hP : P (Nat.findGreatest P (Fintype.card V) + 1) := by
      refine ⟨y, w, Walk.cons hy.2.symm p, hp.cons hyp, ?_, by simp [hpl]⟩
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hy.1
      · exact hpS z hz
    have := hmax _ hP
    omega
  have hNne : N.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨x, hxN, hxmax⟩ := N.exists_max_image (fun y => p.support.idxOf y) hNne
  have hxp := hN x hxN
  have hux : G.Adj u x := (Finset.mem_filter.mp hxN).2
  have hxu : x ≠ u := hux.ne.symm
  set q := p.takeUntil x hxp with hqdef
  have hqpath : q.IsPath := hp.takeUntil hxp
  have hsuppq : q.support = p.support.take (p.support.idxOf x + 1) := by
    rw [hqdef, Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
  have hyq : ∀ y ∈ N, y ∈ q.support := by
    intro y hy
    rw [hsuppq, List.mem_take_iff_getElem]
    have hyl : p.support.idxOf y < p.support.length :=
      List.idxOf_lt_length_iff.mpr (hN y hy)
    refine ⟨p.support.idxOf y, ?_, List.getElem_idxOf hyl⟩
    have := hxmax y hy
    omega
  -- index facts
  have hidx_pos : ∀ y ∈ N, 1 ≤ p.support.idxOf y := by
    intro y hy
    have hyu : y ≠ u := ((Finset.mem_filter.mp hy).2).ne.symm
    rw [← Walk.cons_tail_support,List.idxOf_cons_ne _ hyu.symm]
    omega
  have hcard2 : 2 ≤ N.card := by omega
  obtain ⟨y0, hy0N, hy0x⟩ : ∃ y ∈ N, y ≠ x := by
    by_contra hcon
    push Not at hcon
    have : N ⊆ {x} := fun y hy => Finset.mem_singleton.mpr (hcon y hy)
    have := Finset.card_le_card this
    simp at this
    omega
  have hlt0 : p.support.idxOf y0 < p.support.idxOf x := by
    have h1 := hxmax y0 hy0N
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd ((List.idxOf_inj (hN y0 hy0N)).mp h) hy0x
  have hqlen : 2 ≤ q.length := by
    rw [hqdef, Walk.length_takeUntil]
    have := hidx_pos y0 hy0N
    omega
  have hsnd : q.snd ≠ x := by
    rw [hqdef, Walk.snd_takeUntil hxu]
    exact Walk.getVert_lt_length_takeUntil_ne hxp (by rw [← hqdef]; omega)
  -- the cycle
  let c : G.Walk u u := Walk.cons hux q.reverse
  have hc : c.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hqpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    intro he
    exact hsnd (edge_from_start_of_isPath q hqpath he).symm
  set T := (N.erase x).erase q.snd with hT
  have hTcard : k ≤ T.card := by
    have h1 := Finset.pred_card_le_card_erase (s := N) (a := x)
    have h2 := Finset.pred_card_le_card_erase (s := N.erase x) (a := q.snd)
    rw [hT]
    omega
  obtain ⟨T', hT'T, hT'card⟩ := Finset.exists_subset_card_eq hTcard
  refine hG ⟨u, c, hc, fun i => (T'.equivFin.symm (Fin.cast hT'card.symm i)).1, ?_, ?_⟩
  · intro i j hij
    have := Subtype.val_injective hij
    simpa using this
  · intro i
    set y := (T'.equivFin.symm (Fin.cast hT'card.symm i)).1
    have hyT : y ∈ T := hT'T (T'.equivFin.symm (Fin.cast hT'card.symm i)).2
    rw [hT, Finset.mem_erase, Finset.mem_erase] at hyT
    obtain ⟨hysnd, hyx, hyN⟩ := hyT
    rw [Walk.isChord_sym2Mk]
    refine ⟨(Finset.mem_filter.mp hyN).2, ?_, ?_, ?_⟩
    · simp only [c, Walk.edges_cons, Walk.edges_reverse, List.mem_cons, List.mem_reverse]
      rintro (h | h)
      · rw [Sym2.eq_iff] at h
        rcases h with ⟨-, h⟩ | ⟨h, -⟩
        · exact hyx h
        · exact hxu h.symm
      · exact hysnd (edge_from_start_of_isPath q hqpath h)
    · simp [c]
    · simp only [c, Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse]
      exact Or.inr (hyq y hyN)

lemma card_edges_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (hG : ¬ HasCycleWithIncidentChords G k) :
    ∀ S : Finset V, (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S)).card ≤ (k + 1) * S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp only [Finset.card_empty, mul_zero, nonpos_iff_eq_zero, Finset.card_eq_zero]
      rw [Finset.filter_eq_empty_iff]
      intro e _ h
      induction e using Sym2.ind with
      | h a b => simpa using h a (Sym2.mem_mk_left a b)
    · obtain ⟨v, hvS, hv⟩ := exists_low_degree hG S hS
      have hsub : G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S) ⊆
          G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v) ∪
            (S.filter (G.Adj v)).image (fun w => s(v, w)) := by
        intro e he
        induction e using Sym2.ind with
        | h a b =>
          rw [Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at he
          have ha := he.2 a (Sym2.mem_mk_left a b)
          have hb := he.2 b (Sym2.mem_mk_right a b)
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_image, mem_edgeFinset, mem_edgeSet]
          by_cases hav : a = v
          · subst hav
            exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨hb, he.1⟩, rfl⟩
          by_cases hbv : b = v
          · subst hbv
            exact Or.inr ⟨a, Finset.mem_filter.mpr ⟨ha, he.1.symm⟩, Sym2.eq_swap⟩
          refine Or.inl ⟨he.1, ?_⟩
          intro z hz
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨hav, ha⟩
          · exact Finset.mem_erase.mpr ⟨hbv, hb⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (G.edgeFinset.filter (fun e => ∀ z ∈ e, z ∈ S.erase v))
        ((S.filter (G.Adj v)).image (fun w => s(v, w)))
      have h3 := Finset.card_image_le (s := S.filter (G.Adj v)) (f := fun w => s(v, w))
      have h4 := ih (S.erase v) (Finset.erase_ssubset hvS)
      have h5 := Finset.card_erase_of_mem hvS
      have h6 : 1 ≤ S.card := Finset.card_pos.mpr hS
      rw [h5] at h4
      have : (k + 1) * (S.card - 1) + (k + 1) = (k + 1) * S.card := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega

end OMA

theorem OMA.solution : type_of% @Erdos767.erdos_767.variants.czipszer := by
  classical
  intro k n
  unfold Erdos767.g
  apply csSup_le'
  rintro m ⟨G, hG, rfl⟩
  have := OMA.card_edges_le hG Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext e
  simp

