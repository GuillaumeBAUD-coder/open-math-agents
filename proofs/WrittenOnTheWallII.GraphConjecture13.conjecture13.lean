import FormalConjectures.WrittenOnTheWallII.GraphConjecture13

/-! Insert a star at a chosen vertex into a diameter path. Discard the three
path positions within one distance layer of the centre; edges from the leaves
to the retained path can only meet the two boundary layers. -/

open SimpleGraph

namespace OMA.Star

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma path_vertices {a b x : V} (p : G.Walk a b) (hp : p.length = G.dist a b) :
    ∃ C : Finset V, p.length ≤ C.card + 1 ∧
      (∀ v ∈ C, v = x ∨ G.dist a v + 1 < G.dist a x ∨ G.dist a x + 1 < G.dist a v) ∧
      ∀ v ∈ C, ∀ w ∈ C, G.dist a v = G.dist a w → v = w := by
  classical
  let r := G.dist a x
  let I := (Finset.range (p.length+1)).filter (fun i => i+1 < r ∨ r+1 < i)
  let T := I.image p.getVert
  have pos (i) (hi : i ∈ I) : G.dist a (p.getVert i) = i := by
    have hle : i ≤ p.length := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      omega
    simpa [Walk.take_length, Nat.min_eq_left hle] using
      (length_eq_dist_of_subwalk hp (p.isSubwalk_take i)).symm
  have gap (y) (hy : y ∈ T) : G.dist a y + 1 < r ∨ r + 1 < G.dist a y := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    rw [pos _ hi]
    exact (Finset.mem_filter.mp hi).2
  have hx : x ∉ T := fun h => by
    have := gap x h
    dsimp [r] at this
    omega
  have hcard : T.card = I.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    simpa only [pos i hi, pos j hj] using congrArg (G.dist a) he
  let bad := (Finset.range (p.length+1)).filter (fun i => ¬(i+1 < r ∨ r+1 < i))
  have bound : bad.card ≤ 3 := by
    have incl : bad ⊆ Finset.Icc (r-1) (r+1) := by
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      apply Finset.mem_Icc.mpr
      omega
    have h := Finset.card_le_card incl
    rw [Nat.card_Icc] at h
    omega
  refine ⟨insert x T, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hx, hcard]
    have hpart : I.card + bad.card = p.length+1 := by
      simpa [I,bad] using (Finset.range (p.length+1)).card_filter_add_card_filter_not
        (fun i => i+1 < r ∨ r+1 < i)
    omega
  · intro v hv
    exact (Finset.mem_insert.mp hv).imp_right (gap v)
  · intro v hv w hw he
    rcases Finset.mem_insert.mp hv with rfl | hv <;> rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · have h := gap w hw
      dsimp [r] at h
      omega
    · have h := gap v hv
      dsimp [r] at h
      omega
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      rw [pos _ hi, pos _ hj] at he
      rw [he]

lemma with_neighbors (G : SimpleGraph V) (hc : G.Connected) (x : V) :
    G.diam + G.indepNeighborsCard x ≤ G.largestInducedBipartiteSubgraphSize + 1 := by
  classical
  letI : Nonempty V := ⟨x⟩
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨C,hC,gap,unique⟩ := path_vertices (x := x) p hp
  obtain ⟨N,hN⟩ := (G.induce (G.neighborSet x)).exists_isNIndepSet_indepNum
  let M : Finset V := N.map (Function.Embedding.subtype _)
  have size : M.card = G.indepNeighborsCard x := by simpa [M,indepNeighborsCard] using hN.card_eq
  have adj (v) (hv : v ∈ M) : G.Adj x v := by
    obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hv
    exact y.prop
  have independent : G.IsIndepSet M := by
    intro v hv w hw hne he
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hw
    exact hN.isIndepSet hu hz (fun h => hne (congrArg Subtype.val h)) he
  have disj : Disjoint C M := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    have he := adj v hm
    have hh := he.diff_dist_adj (u := a)
    rcases gap v hv with rfl | h | h
    · exact he.ne rfl
    all_goals omega
  have boundary {v w} (hv : v ∈ M) (hw : w ∈ C) (he : G.Adj v w) :
      G.dist a w % 2 = G.dist a x % 2 := by
    have h1 := (adj v hv).diff_dist_adj (u := a)
    have h2 := he.diff_dist_adj (u := a)
    rcases gap w hw with rfl | h | h <;> omega
  let color (v : V) : Fin 2 :=
    if v ∈ M then 1 else if G.dist a v % 2 = G.dist a x % 2 then 0 else 1
  have bip : (G.induce (↑(C ∪ M) : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring _ _).mpr
    refine ⟨color, ?_⟩
    intro v hv w hw he
    by_cases vm : v ∈ M <;> by_cases wm : w ∈ M
    · exact False.elim (independent vm wm he.ne he)
    · have wc := (Finset.mem_union.mp hw).resolve_right wm
      simp [color,vm,wm,boundary vm wc he]
    · have vc := (Finset.mem_union.mp hv).resolve_right vm
      simp [color,vm,wm,boundary wm vc he.symm]
    · have vc := (Finset.mem_union.mp hv).resolve_right vm
      have wc := (Finset.mem_union.mp hw).resolve_right wm
      have neq : G.dist a v ≠ G.dist a w := fun h => he.ne (unique _ vc _ wc h)
      have hh := he.diff_dist_adj (u := a)
      simp only [color,vm,wm,if_false]
      split_ifs <;> omega
  have sz : (C ∪ M).card ≤ G.largestInducedBipartiteSubgraphSize := by
    apply le_csSup
    · exact ⟨Fintype.card V, fun _ ⟨s,_,hs⟩ => hs ▸ s.card_le_univ⟩
    · exact ⟨_,bip,rfl⟩
  rw [Finset.card_union_of_disjoint disj,size] at sz
  omega

end OMA.Star

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture13.conjecture13 := by
  intro V _ _ _ G hc
  classical
  let vals := Finset.univ.image (fun v => indepNeighborsCard G v)
  have hn : vals.Nonempty := by simp [vals]
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (vals.max'_mem hn)
  have h := OMA.Star.with_neighbors G hc x
  rw [hx] at h
  unfold b
  have h' : (G.diam : ℝ) + (vals.max' hn : ℝ) ≤ G.largestInducedBipartiteSubgraphSize + 1 := by
    exact_mod_cast h
  linarith
