import OMAReductions.R_Erdos184_erdos_184_variants_covering_R1_H2_R1

/-! Strong induction on the length of the path p in A. A first step along an original edge
u - x is kept, and the rest is compressed recursively. A first step u - e into an added vertex
must be followed by a step e - y back to an original vertex, because added vertices are pairwise
non-adjacent and the path ends at an original vertex. Then u and y are distinct endpoints of the
F-edge e, so e = s(u, y) is an edge of G, and the two steps are replaced by it. The compressed
walk only visits original vertices of p, in order, so it is again a path, and every original edge
of p survives. -/

open SimpleGraph in
theorem OMA.solution : OMA.R_Erdos184_erdos_184_variants_covering_R1_H2_R1.H2 := by
  intro V G F A hFG hVV hVE hEE
  have key : ∀ (N : ℕ) (u v : V) (p : A.Walk (.inl u) (.inl v)), p.length ≤ N → p.IsPath →
      ∃ q : G.Walk u v, q.IsPath ∧ (∀ x ∈ q.support, (Sum.inl x : V ⊕ F.edgeSet) ∈ p.support) ∧
        ∀ e : Sym2 V, Sym2.map Sum.inl e ∈ p.edges → e ∈ q.edges := by
    intro N
    induction N with
    | zero =>
      intro u v p hl hp
      cases p with
      | nil => exact ⟨Walk.nil, Walk.IsPath.nil, by simp, by simp⟩
      | cons h p' => rw [Walk.length_cons] at hl; omega
    | succ N ih =>
      intro u v p hl hp
      cases p with
      | nil => exact ⟨Walk.nil, Walk.IsPath.nil, by simp, by simp⟩
      | @cons _ w _ h p' =>
        rw [Walk.cons_isPath_iff] at hp
        rw [Walk.length_cons] at hl
        rcases w with x | e
        · have hG : G.Adj u x := (hVV u x).1 h
          obtain ⟨q', hq', hsupp, hedge⟩ := ih x v p' (by omega) hp.1
          have hu : u ∉ q'.support := fun hu => hp.2 (hsupp u hu)
          refine ⟨Walk.cons hG q', (Walk.cons_isPath_iff hG q').2 ⟨hq', hu⟩, ?_, ?_⟩
          · intro y hy
            rw [Walk.support_cons, List.mem_cons] at hy
            rw [Walk.support_cons, List.mem_cons]
            rcases hy with rfl | hy
            · exact Or.inl rfl
            · exact Or.inr (hsupp y hy)
          · intro e he
            rw [Walk.edges_cons, List.mem_cons] at he
            rw [Walk.edges_cons, List.mem_cons]
            rcases he with he | he
            · left
              apply Sym2.map.injective Sum.inl_injective
              rw [he, Sym2.map_pair_eq]
            · exact Or.inr (hedge e he)
        · have hue : u ∈ (e.val : Sym2 V) := (hVE u e).1 h
          cases p' with
          | @cons _ w2 _ h2 p'' =>
            rcases w2 with y | f
            · have hye : y ∈ (e.val : Sym2 V) := (hVE y e).1 h2.symm
              obtain ⟨hp1, hp2⟩ := hp
              rw [Walk.cons_isPath_iff] at hp1
              rw [Walk.support_cons, List.mem_cons, not_or] at hp2
              have huy : u ≠ y := by
                rintro rfl
                exact hp2.2 p''.start_mem_support
              have hev : (e.val : Sym2 V) = s(u, y) := (Sym2.mem_and_mem_iff huy).1 ⟨hue, hye⟩
              have hF : F.Adj u y := by
                have he := e.property
                rw [hev] at he
                exact (SimpleGraph.mem_edgeSet F).1 he
              have hG : G.Adj u y := hFG hF
              rw [Walk.length_cons] at hl
              obtain ⟨q'', hq'', hsupp, hedge⟩ := ih y v p'' (by omega) hp1.1
              have hu : u ∉ q''.support := fun hu => hp2.2 (hsupp u hu)
              refine ⟨Walk.cons hG q'', (Walk.cons_isPath_iff hG q'').2 ⟨hq'', hu⟩, ?_, ?_⟩
              · intro x hx
                rw [Walk.support_cons, List.mem_cons] at hx
                rw [Walk.support_cons, List.mem_cons, Walk.support_cons, List.mem_cons]
                rcases hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr (Or.inr (hsupp x hx))
              · intro e' he'
                rw [Walk.edges_cons, List.mem_cons, Walk.edges_cons, List.mem_cons] at he'
                rw [Walk.edges_cons, List.mem_cons]
                rcases he' with he' | he' | he'
                · exfalso
                  have hm : (Sum.inr e : V ⊕ F.edgeSet) ∈ Sym2.map Sum.inl e' := by
                    rw [he']; exact Sym2.mem_mk_right _ _
                  obtain ⟨a, -, ha⟩ := Sym2.mem_map.1 hm
                  exact Sum.inl_ne_inr ha
                · exfalso
                  have hm : (Sum.inr e : V ⊕ F.edgeSet) ∈ Sym2.map Sum.inl e' := by
                    rw [he']; exact Sym2.mem_mk_left _ _
                  obtain ⟨a, -, ha⟩ := Sym2.mem_map.1 hm
                  exact Sum.inl_ne_inr ha
                · exact Or.inr (hedge e' he')
            · exact absurd h2 (hEE e f)
  intro u v p hp
  obtain ⟨q, hq, -, he⟩ := key p.length u v p le_rfl hp
  exact ⟨q, hq, he⟩
