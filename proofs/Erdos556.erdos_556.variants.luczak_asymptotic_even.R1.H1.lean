import OMAReductions.R_Erdos556_erdos_556_variants_luczak_asymptotic_even_R1

/-! A dense component yields a matching by coloring each edge with the sum of its endpoint labels. -/

open SimpleGraph Finset
open scoped SimpleGraph

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_even_R1.H1 := by
  intro t k R _ hk hd
  classical
  let S (c : R.ConnectedComponent) := univ.filter (fun x => R.connectedComponentMk x = c)
  let comp (e : Sym2 (Fin t)) := R.connectedComponentMk e.out.1
  let E (c : R.ConnectedComponent) := R.edgeFinset.filter (fun e => comp e = c)
  have hS : ∑ c, (S c).card = t := by
    simpa [S] using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin t)) univ
      R.connectedComponentMk
  have hE : ∑ c, (E c).card = R.edgeFinset.card := by
    simpa [E] using sum_card_fiberwise_eq_card_filter R.edgeFinset univ comp
  obtain ⟨c, hc⟩ : ∃ c, (k - 1) * (S c).card < (E c).card := by
    by_contra! h
    have hle := sum_le_sum (fun c (_ : c ∈ univ) => h c)
    rw [← mul_sum, hS, hE] at hle
    omega
  have hmem (x : Fin t) : x ∈ S c ↔ x ∈ c.supp := by simp [S]
  have hends {x y : Fin t} (he : s(x,y) ∈ E c) : x ∈ S c ∧ y ∈ S c := by
    obtain ⟨hR, hcomp⟩ := mem_filter.mp he
    have hadj : R.Adj x y := mem_edgeFinset.mp hR
    have hout : (s(x,y) : Sym2 (Fin t)).out.1 ∈ c.supp := hcomp
    have hxy := c.mem_supp_congr_adj hadj
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x,y)) with hx | hy
    · rw [hx] at hout
      exact ⟨(hmem _).mpr hout, (hmem _).mpr (hxy.mp hout)⟩
    · rw [hy] at hout
      exact ⟨(hmem _).mpr (hxy.mpr hout), (hmem _).mpr hout⟩
  have hspos : 0 < (S c).card := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact card_pos.mpr ⟨x, (hmem _).mpr hx⟩
  let : NeZero (S c).card := ⟨hspos.ne'⟩
  -- The finite-set labeling follows the odd_lower_bound sibling proof.
  let equiv : S c ≃ Fin (S c).card := Finset.equivFinOfCardEq rfl
  let label (x : Fin t) : Fin (S c).card := if hx : x ∈ S c then equiv ⟨x, hx⟩ else 0
  have hinj {x y} (hx : x ∈ S c) (hy : y ∈ S c) (h : label x = label y) : x = y := by
    simp only [label, dif_pos hx, dif_pos hy] at h
    exact congrArg Subtype.val (equiv.injective h)
  let color : Sym2 (Fin t) → Fin (S c).card :=
    Sym2.lift ⟨fun x y => label x + label y, fun x y => add_comm _ _⟩
  obtain ⟨a, _, ha⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := E c) (t := univ) (f := color) (fun _ _ => mem_univ _)
    (by simpa [Nat.mul_comm] using hc)
  let F := (E c).filter (fun e => color e = a)
  have hsize : k ≤ F.card := by
    change k - 1 < F.card at ha
    omega
  have uniqueNbr {x y z : Fin t} (hy : s(x,y) ∈ F) (hz : s(x,z) ∈ F) : y = z := by
    obtain ⟨he, hy'⟩ := mem_filter.mp hy
    obtain ⟨hf, hz'⟩ := mem_filter.mp hz
    have h : label x + label y = label x + label z := hy'.trans hz'.symm
    exact hinj (hends he).2 (hends hf).2 (add_left_cancel h)
  let M : R.Subgraph := {
    verts := ↑(F.biUnion Sym2.toFinset)
    Adj := fun x y => s(x,y) ∈ F
    adj_sub := fun h => mem_edgeFinset.mp (mem_filter.mp (mem_filter.mp h).1).1
    edge_vert := fun {x y} h => mem_biUnion.mpr ⟨_, h, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)⟩
    symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩ }
  have incident {x : Fin t} (hx : x ∈ M.verts) : ∃ y, s(x,y) ∈ F := by
    obtain ⟨e, he, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact ⟨y, he⟩
  have disj : (F : Set (Sym2 (Fin t))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx)
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact hne (congrArg (fun w => s(x,w)) (uniqueNbr he hf))
  have inside {x : Fin t} (hx : x ∈ M.verts) : x ∈ c.supp := by
    obtain ⟨y, hy⟩ := incident hx
    exact (hmem x).mp (hends (mem_filter.mp hy).1).1
  refine ⟨M, ?_, ?_, fun _ hu _ hv => c.reachable_of_mem_supp (inside hu) (inside hv)⟩
  · intro x hx
    obtain ⟨y, hy⟩ := incident hx
    exact ⟨y, hy, fun _ hz => uniqueNbr hz hy⟩
  · have hcard (e) (he : e ∈ F) : e.toFinset.card = 2 :=
      e.card_toFinset_of_not_isDiag (R.not_isDiag_of_mem_edgeFinset
        (mem_filter.mp (mem_filter.mp he).1).1)
    change 2 * k ≤ (↑(F.biUnion Sym2.toFinset) : Set (Fin t)).ncard
    rw [Set.ncard_coe_finset, card_biUnion disj, sum_const_nat hcard, Nat.mul_comm F.card]
    omega
