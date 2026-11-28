import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1

/-!
Proof of `OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1.H3`:
`χ''(G) ≤ 2 Δ(G) + 1`.

Two elements of `V ⊕ E` conflict when a total colouring must separate them. A greedy colouring
needs only `D + 1` colours as soon as every element has its conflicts inside a list of at most
`D` elements. Such lists of size at most `2 Δ` exist:
* a vertex `v` conflicts with its neighbours and its incident edges `s(v, w)`, `w ∈ N(v)`;
* an edge `s(u, w)` conflicts with its endpoints and with the edges sharing an endpoint.
  Every one of them is the image of a neighbour of `u` (sending `w` to the endpoint `w` and
  `z ≠ w` to the edge `s(u, z)`) or of a neighbour of `w` (symmetrically).
-/

namespace OMAProof.TotalGreedy

open Finset

/-- Greedy colouring: a symmetric irreflexive relation whose neighbourhoods are covered by lists
of size at most `D` admits a proper colouring with `D + 1` colours. -/
theorem greedy {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop)
    (hsymm : ∀ x y, R x y → R y x) (hirr : ∀ x, ¬ R x x) (D : ℕ) (N : α → Finset α)
    (hN : ∀ x y, R x y → y ∈ N x) (hcard : ∀ x, (N x).card ≤ D) :
    ∃ c : α → Fin (D + 1), ∀ x y, R x y → c x ≠ c y := by
  suffices h : ∀ s : Finset α, ∃ c : α → Fin (D + 1), ∀ x ∈ s, ∀ y ∈ s, R x y → c x ≠ c y by
    obtain ⟨c, hc⟩ := h Finset.univ
    exact ⟨c, fun x y hxy => hc x (mem_univ x) y (mem_univ y) hxy⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨k, hk⟩ : ∃ k : Fin (D + 1), k ∉ (N a).image c := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin (D + 1))) ⊆ (N a).image c := fun k _ => hall k
      have h1 := Finset.card_le_card hsub
      have h2 := (Finset.card_image_le (s := N a) (f := c)).trans (hcard a)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    refine ⟨Function.update c a k, ?_⟩
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd hxy (hirr _)
    · have hyx : y ≠ x := fun h => ha (h ▸ hy)
      rw [Function.update_self, Function.update_of_ne hyx]
      intro h
      exact hk (h ▸ Finset.mem_image_of_mem c (hN _ _ hxy))
    · have hxy' : x ≠ y := fun h => ha (h ▸ hx)
      rw [Function.update_self, Function.update_of_ne hxy']
      intro h
      exact hk (h.symm ▸ Finset.mem_image_of_mem c (hN _ _ (hsymm _ _ hxy)))
    · have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hya : y ≠ a := fun h => ha (h ▸ hy)
      rw [Function.update_of_ne hxa, Function.update_of_ne hya]
      exact hc x hx y hy hxy

variable {V : Type*} (G : SimpleGraph V)

/-- The pairs of elements of `V ⊕ E` that a total colouring must separate. -/
def conflict : V ⊕ G.edgeSet → V ⊕ G.edgeSet → Prop
  | .inl u, .inl v => G.Adj u v
  | .inr e, .inr f => e ≠ f ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)
  | .inl v, .inr e => v ∈ (e : Sym2 V)
  | .inr e, .inl v => v ∈ (e : Sym2 V)

theorem conflict_symm : ∀ x y, conflict G x y → conflict G y x := by
  intro x y h
  cases x with
  | inl u =>
    cases y with
    | inl v => exact SimpleGraph.Adj.symm h
    | inr f => exact h
  | inr e =>
    cases y with
    | inl v => exact h
    | inr f =>
      obtain ⟨hne, v, h1, h2⟩ := h
      exact ⟨Ne.symm hne, v, h2, h1⟩

theorem conflict_irrefl : ∀ x, ¬ conflict G x x := by
  intro x h
  cases x with
  | inl u => exact G.irrefl h
  | inr e => exact h.1 rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The edge `s(v, w)` for a neighbour `w` of `v`. -/
def edgeTo (v : V) (w : G.neighborFinset v) : G.edgeSet :=
  ⟨s(v, w.1), (SimpleGraph.mem_edgeSet G).mpr ((G.mem_neighborFinset v w.1).mp w.2)⟩

/-- Every edge through `v` is `edgeTo v w` for some neighbour `w`. -/
theorem exists_edgeTo {v : V} {e : G.edgeSet} (hv : v ∈ (e : Sym2 V)) :
    ∃ w : G.neighborFinset v, edgeTo G v w = e := by
  have hspec : s(v, Sym2.Mem.other hv) = (e : Sym2 V) := Sym2.other_spec hv
  have hadj : G.Adj v (Sym2.Mem.other hv) := by
    rw [← SimpleGraph.mem_edgeSet, hspec]
    exact e.2
  exact ⟨⟨Sym2.Mem.other hv, (G.mem_neighborFinset v _).mpr hadj⟩, Subtype.ext hspec⟩

/-- The image of a neighbour `z` of `u` seen from the edge `s(u, w)`. -/
def fromEnd (u w : V) (z : G.neighborFinset u) : V ⊕ G.edgeSet :=
  if z.1 = w then Sum.inl w else Sum.inr (edgeTo G u z)

theorem exists_cover (x : V ⊕ G.edgeSet) :
    ∃ L : Finset (V ⊕ G.edgeSet), L.card ≤ 2 * G.maxDegree ∧ ∀ y, conflict G x y → y ∈ L := by
  cases x with
  | inl v =>
    refine ⟨(G.neighborFinset v).image Sum.inl ∪
      (G.neighborFinset v).attach.image (fun w => Sum.inr (edgeTo G v w)), ?_, ?_⟩
    · have h1 := Finset.card_image_le (s := G.neighborFinset v) (f := (Sum.inl : V → V ⊕ G.edgeSet))
      have h2 := Finset.card_image_le (s := (G.neighborFinset v).attach)
        (f := fun w => (Sum.inr (edgeTo G v w) : V ⊕ G.edgeSet))
      rw [Finset.card_attach] at h2
      have hd : (G.neighborFinset v).card ≤ G.maxDegree := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact G.degree_le_maxDegree v
      have := Finset.card_union_le ((G.neighborFinset v).image (Sum.inl : V → V ⊕ G.edgeSet))
        ((G.neighborFinset v).attach.image (fun w => (Sum.inr (edgeTo G v w) : V ⊕ G.edgeSet)))
      omega
    · intro y hy
      cases y with
      | inl w =>
        apply Finset.mem_union_left
        exact Finset.mem_image_of_mem _ ((G.mem_neighborFinset v w).mpr hy)
      | inr e =>
        apply Finset.mem_union_right
        obtain ⟨w, hw⟩ := exists_edgeTo G (show v ∈ (e : Sym2 V) from hy)
        exact Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, by rw [hw]⟩
  | inr e =>
    obtain ⟨z, hz⟩ := e
    induction z using Sym2.ind with
    | h u w =>
      have huw : G.Adj u w := (SimpleGraph.mem_edgeSet G).mp hz
      refine ⟨(G.neighborFinset u).attach.image (fromEnd G u w) ∪
        (G.neighborFinset w).attach.image (fromEnd G w u), ?_, ?_⟩
      · have h1 := Finset.card_image_le (s := (G.neighborFinset u).attach) (f := fromEnd G u w)
        have h2 := Finset.card_image_le (s := (G.neighborFinset w).attach) (f := fromEnd G w u)
        rw [Finset.card_attach] at h1 h2
        have hdu : (G.neighborFinset u).card ≤ G.maxDegree := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact G.degree_le_maxDegree u
        have hdw : (G.neighborFinset w).card ≤ G.maxDegree := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact G.degree_le_maxDegree w
        have := Finset.card_union_le ((G.neighborFinset u).attach.image (fromEnd G u w))
          ((G.neighborFinset w).attach.image (fromEnd G w u))
        omega
      · intro y hy
        cases y with
        | inl v =>
          have hv : v ∈ s(u, w) := hy
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · apply Finset.mem_union_right
            refine Finset.mem_image.mpr ⟨⟨v, (G.mem_neighborFinset w v).mpr huw.symm⟩,
              Finset.mem_attach _ _, ?_⟩
            simp [fromEnd]
          · apply Finset.mem_union_left
            refine Finset.mem_image.mpr ⟨⟨v, (G.mem_neighborFinset u v).mpr huw⟩,
              Finset.mem_attach _ _, ?_⟩
            simp [fromEnd]
        | inr f =>
          obtain ⟨hne, v, hve, hvf⟩ := hy
          have hv : v ∈ s(u, w) := hve
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · apply Finset.mem_union_left
            obtain ⟨t, ht⟩ := exists_edgeTo G hvf
            refine Finset.mem_image.mpr ⟨t, Finset.mem_attach _ _, ?_⟩
            have htw : t.1 ≠ w := by
              intro h
              apply hne
              rw [← ht]
              apply Subtype.ext
              simp [edgeTo, h]
            simp [fromEnd, htw, ht]
          · apply Finset.mem_union_right
            obtain ⟨t, ht⟩ := exists_edgeTo G hvf
            refine Finset.mem_image.mpr ⟨t, Finset.mem_attach _ _, ?_⟩
            have htu : t.1 ≠ u := by
              intro h
              apply hne
              rw [← ht]
              apply Subtype.ext
              simp [edgeTo, h, Sym2.eq_swap]
            simp [fromEnd, htu, ht]

end OMAProof.TotalGreedy

open OMAProof.TotalGreedy in
theorem OMA.solution :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R1.H3 := by
  intro V _ _ G _
  choose N hNcard hN using exists_cover G
  obtain ⟨c, hc⟩ := greedy (conflict G) (conflict_symm G) (conflict_irrefl G)
    (2 * G.maxDegree) N hN hNcard
  apply Nat.sInf_le
  show G.TotalColorable (2 * G.maxDegree + 1)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv
    exact hc (Sum.inl u) (Sum.inl v) huv
  · intro e f hef hv
    exact hc (Sum.inr e) (Sum.inr f) ⟨hef, hv⟩
  · intro v e hv
    exact hc (Sum.inl v) (Sum.inr e) hv
