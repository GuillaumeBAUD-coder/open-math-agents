import OMAReductions.R_opg_chords_of_longest_cycles_R1

/-! The spanning longest cycle `c` uses exactly two edges at its base vertex `u`, to `a` and `b`
(`IsCycle.ncard_neighborSet_toSubgraph_eq_two`). If every edge of `G` at `u` were an edge of `c`,
then deleting `{a, b}` (fewer than 3 vertices) would leave `u` with no neighbour. A fourth vertex
`z ∉ {u, a, b}` exists because there are more than 3 vertices, and `u` and `z` would then be
disconnected, contradicting 3-connectivity. So some edge `u w` of `G` is not an edge of `c`. As
`c` is spanning, `w` lies on `c`, so `u w` is a chord. -/

theorem OMA.solution : OMA.R_opg_chords_of_longest_cycles_R1.H1 := by
  intro V _ G hK u c hc hspan
  classical
  unfold OMA.S_opg_chords_of_longest_cycles.IsKConnected at hK
  unfold OMA.S_opg_chords_of_longest_cycles.IsLongestCycle at hc
  obtain ⟨hcard, hconnS⟩ := hK
  by_contra hno
  have hall : ∀ w, G.Adj u w → c.toSubgraph.Adj u w := by
    intro w hw
    by_contra hnot
    apply hno
    unfold OMA.S_opg_chords_of_longest_cycles.HasChord
    refine ⟨u, w, hw, c.start_mem_support, hspan w, fun he => hnot ?_⟩
    exact SimpleGraph.Subgraph.mem_edgeSet.1 ((SimpleGraph.Walk.mem_edges_toSubgraph c).2 he)
  obtain ⟨a, b, hab, hN⟩ :=
    Set.ncard_eq_two.1 (hc.1.ncard_neighborSet_toSubgraph_eq_two c.start_mem_support)
  have ha : c.toSubgraph.Adj u a := by
    show a ∈ c.toSubgraph.neighborSet u
    rw [hN]
    simp
  have hb : c.toSubgraph.Adj u b := by
    show b ∈ c.toSubgraph.neighborSet u
    rw [hN]
    simp
  have hua : u ≠ a := ha.ne
  have hub : u ≠ b := hb.ne
  have hconn := hconnS {a, b} (by have := Finset.card_le_two (a := a) (b := b); omega)
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({u, a, b} : Finset V))
    (t := Finset.univ)
    (by rw [Finset.card_univ]; have := Finset.card_le_three (a := u) (b := a) (c := b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨hzu, hza, hzb⟩ := hz
  have huS : u ∈ ((({a, b} : Finset V) : Set V)ᶜ) := by simp [hua, hub]
  have hzS : z ∈ ((({a, b} : Finset V) : Set V)ᶜ) := by simp [hza, hzb]
  obtain ⟨p⟩ := hconn.preconnected ⟨u, huS⟩ ⟨z, hzS⟩
  have hadj := p.adj_snd (SimpleGraph.Walk.not_nil_of_ne (fun h => hzu (Subtype.mk.inj h).symm))
  have hG : G.Adj u p.snd.1 := SimpleGraph.induce_adj.1 hadj
  have hmem : p.snd.1 ∈ c.toSubgraph.neighborSet u := hall _ hG
  rw [hN] at hmem
  have hout := p.snd.2
  simp only [Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hout
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact hout.1 h
  · exact hout.2 h
