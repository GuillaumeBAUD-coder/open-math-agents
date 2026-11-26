import FormalConjectures.WrittenOnTheWallII.GraphConjecture17

/-! On a diameter path, each pair of positions 3i and 3i+1 has a vertex outside
a fixed maximum independent set. These additional vertices form an independent set. -/

open SimpleGraph

namespace OMA.Diameter

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma two_sets {s t : Finset V} (hs : G.IsIndepSet s) (ht : G.IsIndepSet t)
    (hd : Disjoint s t) : s.card + t.card ≤ G.largestInducedBipartiteSubgraphSize := by
  classical
  have hb : (G.induce (↑(s ∪ t) : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring G _).mpr
    refine ⟨fun v => if v ∈ s then 0 else 1, ?_⟩
    intro v hv w hw h
    by_cases hvs : v ∈ s <;> by_cases hws : w ∈ s
    · exact False.elim (hs hvs hws h.ne h)
    · simp [hvs,hws]
    · simp [hvs,hws]
    · exact False.elim (ht ((Finset.mem_union.mp hv).resolve_left hvs)
        ((Finset.mem_union.mp hw).resolve_left hws) h.ne h)
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨z, _, hz⟩ => hz ▸ z.card_le_univ⟩
  · exact ⟨s ∪ t, hb, Finset.card_union_of_disjoint hd⟩

lemma extra_vertices (s : Finset V) (hs : G.IsIndepSet s) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) :
    ∃ t : Finset V, Disjoint s t ∧ G.IsIndepSet t ∧ t.card = (p.length + 2) / 3 := by
  classical
  let k := (p.length + 2) / 3
  have len (i : Fin k) : 3 * i.val + 1 ≤ p.length := by
    have hi := i.isLt
    dsimp [k] at hi
    omega
  have place (n : ℕ) (hn : n ≤ p.length) : G.dist a (p.getVert n) = n := by
    have h := length_eq_dist_of_subwalk hp (p.isSubwalk_take n)
    simpa [Walk.take_length, Nat.min_eq_left hn] using h.symm
  have pair (i : Fin k) : ∃ v ∉ s, 3*i.val ≤ G.dist a v ∧ G.dist a v ≤ 3*i.val+1 := by
    let n := 3*i.val
    have hn : n+1 ≤ p.length := len i
    have he := p.adj_getVert_succ (show n < p.length by omega)
    by_cases h0 : p.getVert n ∈ s
    · refine ⟨p.getVert (n+1), fun h1 => hs h0 h1 he.ne he, ?_⟩
      rw [place _ hn]
      dsimp [n]
      omega
    · refine ⟨p.getVert n, h0, ?_⟩
      rw [place _ (by omega)]
      dsimp [n]
      omega
  choose f outside lower upper using pair
  have inj : Function.Injective f := by
    intro i j hij
    have he := congrArg (G.dist a) hij
    have := lower i
    have := upper i
    have := lower j
    have := upper j
    apply Fin.ext
    omega
  let e : Fin k ↪ V := ⟨f,inj⟩
  let t := Finset.univ.map e
  refine ⟨t, ?_, ?_, by simp [t,k]⟩
  · apply Finset.disjoint_left.mpr
    intro v hv ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp ht
    exact outside i hv
  · intro u hu v hv huv h
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    have hne : i.val ≠ j.val := fun h => huv (congrArg e (Fin.ext h))
    have gap := h.symm.diff_dist_adj (u := a)
    change G.dist a (f i) = G.dist a (f j) ∨ G.dist a (f i) = G.dist a (f j) + 1 ∨
      G.dist a (f i) = G.dist a (f j) - 1 at gap
    have := lower i
    have := upper i
    have := lower j
    have := upper j
    omega

end OMA.Diameter

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture17.conjecture17 := by
  intro V _ _ _ G hc
  classical
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨s,hs⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨t,hd,ht,hcard⟩ := OMA.Diameter.extra_vertices s hs.isIndepSet p hp
  have h := OMA.Diameter.two_sets hs.isIndepSet ht hd
  rw [hs.card_eq, hcard, hp, hab] at h
  let k := (G.diam + 2) / 3
  have hk : G.diam ≤ 3*k := by dsimp [k]; omega
  have hk' : (G.diam : ℝ) ≤ 3*(k : ℝ) := by exact_mod_cast hk
  have hceil : ⌈(G.diam : ℝ)/3⌉ ≤ (k : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hceil' : (⌈(G.diam : ℝ)/3⌉ : ℝ) ≤ k := by exact_mod_cast hceil
  have h' : (G.indepNum : ℝ) + k ≤ G.b := by unfold SimpleGraph.b; exact_mod_cast h
  linarith
