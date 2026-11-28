import OMAReductions.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1

-- Step opg-uniquely-hamiltonian-graphs.R1.H4.R1.H1: hypothesis H1 of reduction opg-uniquely-hamiltonian-graphs.R1.H4.R1
-- Credit: @lettucrisp

/-!
# Spanning 4-regular subgraph preserving a Hamilton cycle

Given an even `r`-regular finite simple graph `G` with `r ≥ 6` and a Hamilton cycle `c`,
removing the edges of `c` leaves a spanning `(r - 2)`-regular simple graph `R` with even
degree `2k ≥ 4`. Decomposing `R` into edge-disjoint directed simple cycles yields a balanced
orientation `D` of `R` (every vertex has in-degree and out-degree equal to `k`). Hall's marriage
theorem then produces a bijection `f : V ≃ V` with `D x (f x)` for all `x`. Since `D` is an
orientation of a simple graph, `f` has no fixed points and no 2-cycles, so its underlying
undirected graph `F ≤ R` is 2-regular and edge-disjoint from `c`. Taking `H = C ⊔ F` yields a
spanning 4-regular subgraph of `G` containing all edges of `c`.
-/

namespace PetersenTwoFactor

open SimpleGraph Finset
open scoped Classical

section CycleSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The simple graph formed by the edges of a walk `c`. -/
private def walkGraph (G : SimpleGraph V) {v : V} (c : G.Walk v v) : SimpleGraph V where
  Adj x y := s(x, y) ∈ c.edges
  symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => G.irrefl (c.edges_subset_edgeSet h)⟩

private lemma walkGraph_le (G : SimpleGraph V) {v : V} (c : G.Walk v v) :
    walkGraph G c ≤ G := fun _ _ h => c.edges_subset_edgeSet h

private lemma getElem_edges_eq {G : SimpleGraph V} {u w : V} (p : G.Walk u w)
    (i : ℕ) (hi : i < p.edges.length) :
    p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | cons h q ih =>
    cases i with
    | zero => simp
    | succ j =>
      simp only [Walk.edges_cons, List.getElem_cons_succ, Walk.getVert_cons_succ]
      exact ih j (by simpa using hi)

/-- In a cycle `p : G.Walk u u`, an edge `s(u, y)` belongs to `p.edges` iff
`y = p.snd` or `y = p.penultimate`. -/
private lemma mem_edges_cycle_iff {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) (y : V) :
    s(u, y) ∈ p.edges ↔ y = p.snd ∨ y = p.penultimate := by
  have hlen3 : 3 ≤ p.length := hp.three_le_length
  have hlen_edges : p.edges.length = p.length := Walk.length_edges p
  constructor
  · intro hmem
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
    rw [getElem_edges_eq p i hi] at heq
    have hi' : i < p.length := hlen_edges ▸ hi
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi0 : i = 0 := by
        rcases (hp.getVert_endpoint_iff (by omega)).mp h1 with h | h
        · exact h
        · omega
      left
      rw [← h2, hi0]
    · have hiL : i + 1 = p.length := by
        rcases (hp.getVert_endpoint_iff (by omega)).mp h2 with h | h
        · omega
        · exact h
      right
      rw [← h1, show i = p.length - 1 by omega]
  · rintro (rfl | rfl)
    · have h0 : 0 < p.edges.length := by omega
      have : p.edges[0] = s(u, p.snd) := by
        rw [getElem_edges_eq p 0 h0, Walk.getVert_zero]
      rw [← this]
      exact List.getElem_mem h0
    · have hL : p.length - 1 < p.edges.length := by omega
      have : p.edges[p.length - 1] = s(u, p.penultimate) := by
        rw [getElem_edges_eq p (p.length - 1) hL,
          show p.length - 1 + 1 = p.length by omega, Walk.getVert_length, Sym2.eq_swap]
      rw [← this]
      exact List.getElem_mem hL

/-- The subgraph of a Hamilton cycle is 2-regular. -/
private lemma walkGraph_isRegular_two (G : SimpleGraph V) {v : V} (c : G.Walk v v)
    (hc : OMA.S_opg_uniquely_hamiltonian_graphs.IsHamiltonCycle G c) :
    (walkGraph G c).IsRegularOfDegree 2 := by
  classical
  intro u
  have hu : u ∈ c.support := hc.2 u
  let p := c.rotate u hu
  have hp : p.IsCycle := hc.1.rotate hu
  have hperm : ∀ e, e ∈ p.edges ↔ e ∈ c.edges := fun _ => (c.rotate_edges u hu).perm.mem_iff
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_pair hp.snd_ne_penultimate]
  congr 1
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  change s(u, y) ∈ c.edges ↔ _
  rw [← hperm, mem_edges_cycle_iff hp]

end CycleSubgraph

section BalancedOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Prefix of a list up to and including the first occurrence of `z`. -/
private def takeTo (z : V) : List V → List V
  | [] => []
  | x :: xs => if x = z then [x] else x :: takeTo z xs

private lemma takeTo_isPrefix (z : V) (l : List V) : (takeTo z l).IsPrefix l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    unfold takeTo
    split_ifs with h
    · exact ⟨xs, rfl⟩
    · obtain ⟨t, ht⟩ := ih
      exact ⟨t, by simp [ht]⟩

private lemma takeTo_ne_nil {z : V} {l : List V} (hz : z ∈ l) : takeTo z l ≠ [] := by
  cases l with
  | nil => simp at hz
  | cons x xs =>
    unfold takeTo
    split_ifs <;> simp

private lemma takeTo_getLast {z : V} {l : List V} (hz : z ∈ l) :
    (takeTo z l).getLast (takeTo_ne_nil hz) = z := by
  induction l with
  | nil => simp at hz
  | cons x xs ih =>
    unfold takeTo
    split_ifs with h
    · simp [h]
    · have hz' : z ∈ xs := (List.mem_cons.mp hz).resolve_left (Ne.symm h)
      have hne : takeTo z xs ≠ [] := takeTo_ne_nil hz'
      simpa [List.getLast_cons hne] using ih hz'

private lemma isChain_of_isPrefix {R : V → V → Prop} {l₁ l₂ : List V}
    (hp : l₁.IsPrefix l₂) (hc : l₂.IsChain R) : l₁.IsChain R := by
  obtain ⟨t, rfl⟩ := hp
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.cons_append, List.cons_append, List.isChain_cons_cons] at hc
      rw [List.isChain_cons_cons]
      exact ⟨hc.1, ih hc.2⟩

/-- Any nonempty finite simple graph with all even degrees contains a simple cycle of length ≥ 3. -/
private lemma exists_simple_cycle (R : SimpleGraph V) [DecidableRel R.Adj]
    (heven : ∀ v : V, Even (R.degree v)) (hne : R.edgeFinset.Nonempty) :
    ∃ cy : List V, 3 ≤ cy.length ∧ cy.Nodup ∧ cy.IsChain R.Adj ∧
      ∃ (hcy : cy ≠ []), R.Adj (cy.getLast hcy) (cy.head hcy) := by
  -- Find an edge to witness a valid simple path of length ≥ 2.
  obtain ⟨e, he⟩ := hne
  rw [SimpleGraph.mem_edgeFinset] at he
  obtain ⟨u, w⟩ := e
  have huw : R.Adj u w := he
  have hgood2 : ∃ L : List V, 2 ≤ L.length ∧ L.Nodup ∧ L.IsChain R.Adj :=
    ⟨[u, w], le_rfl, by simp [huw.ne], by simp [huw]⟩
  -- Pick a valid simple path of maximal length (bounded by Fintype.card V).
  have hbdd : ∀ L : List V, L.Nodup → L.length ≤ Fintype.card V := fun L hnd => by
    simpa [List.toFinset_card_of_nodup hnd] using Finset.card_le_univ L.toFinset
  let S : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter fun k =>
    ∃ L : List V, L.length = k ∧ 2 ≤ L.length ∧ L.Nodup ∧ L.IsChain R.Adj
  have hS_ne : S.Nonempty := by
    obtain ⟨L, hL2, hnd, hch⟩ := hgood2
    exact ⟨L.length, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbdd L hnd)), L, rfl, hL2, hnd, hch⟩⟩
  let M := S.max' hS_ne
  have hM_mem : M ∈ S := Finset.max'_mem S hS_ne
  obtain ⟨L, hLM, hL2, hLnd, hLch⟩ := (Finset.mem_filter.mp hM_mem).2
  rcases L with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hL2
  · simp at hL2
  have hab : R.Adj a b := (List.isChain_cons_cons.mp hLch).1
  -- Since R.degree a is even and ≥ 1, R.degree a ≥ 2, so a has a neighbor z ≠ b.
  have hdeg_pos : 0 < R.degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨b, (SimpleGraph.mem_neighborFinset R a b).mpr hab⟩
  have hdeg_ge2 : 2 ≤ R.degree a := by
    obtain ⟨t, ht⟩ := heven a
    omega
  have hnb_gt1 : 1 < (R.neighborFinset a).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz_nb, hzb⟩ : ∃ z ∈ R.neighborFinset a, z ≠ b := by
    have hsub : ((R.neighborFinset a).erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset R a b).mpr hab)]
      omega
    obtain ⟨z, hz⟩ := hsub
    exact ⟨z, Finset.mem_of_mem_erase hz, Finset.ne_of_mem_erase hz⟩
  have haz : R.Adj a z := (SimpleGraph.mem_neighborFinset R a z).mp hz_nb
  -- By maximality of L, z must already belong to L.
  have hz_mem : z ∈ a :: b :: rest := by
    by_contra hnot
    have hnd' : (z :: a :: b :: rest).Nodup := List.nodup_cons.mpr ⟨hnot, hLnd⟩
    have hch' : (z :: a :: b :: rest).IsChain R.Adj :=
      List.isChain_cons_cons.mpr ⟨haz.symm, hLch⟩
    have hlen' : (z :: a :: b :: rest).length = M + 1 := by
      simp [← hLM]
    have hmem' : M + 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hlen' ▸ hbdd _ hnd')),
       z :: a :: b :: rest, hlen', by omega, hnd', hch'⟩
    have hle' : M + 1 ≤ M := Finset.le_max' S (M + 1) hmem'
    omega
  have hz_rest : z ∈ rest := by
    rcases List.mem_cons.mp hz_mem with rfl | h1
    · exact (R.irrefl haz).elim
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact (hzb rfl).elim
      · exact h2
  -- Take the prefix a :: b :: takeTo z rest.
  let cy : List V := a :: b :: takeTo z rest
  have hpref : cy.IsPrefix (a :: b :: rest) := by
    obtain ⟨t, ht⟩ := takeTo_isPrefix z rest
    exact ⟨t, by simp [cy, ht]⟩
  have hcy_ne : cy ≠ [] := by simp [cy]
  have htake_ne : takeTo z rest ≠ [] := takeTo_ne_nil hz_rest
  refine ⟨cy, ?_, ?_, ?_, hcy_ne, ?_⟩
  · have hpos : 0 < (takeTo z rest).length := List.length_pos_iff.mpr htake_ne
    simp only [cy, List.length_cons]
    omega
  · exact hLnd.sublist hpref.sublist
  · exact isChain_of_isPrefix hpref hLch
  · have hlast : cy.getLast hcy_ne = z := by
      simp only [cy, List.getLast_cons (List.cons_ne_nil b _), List.getLast_cons htake_ne]
      exact takeTo_getLast hz_rest
    rw [hlast]
    exact haz.symm

/-- Every finite simple graph with all even degrees admits a balanced orientation:
each undirected edge is oriented in exactly one direction, and every vertex has
equal in-degree and out-degree. -/
private lemma exists_balanced_orientation :
    ∀ (m : ℕ) (R : SimpleGraph V) [DecidableRel R.Adj],
      R.edgeFinset.card ≤ m →
      (∀ v : V, Even (R.degree v)) →
      ∃ D : V → V → Prop,
        (∀ x y, D x y → R.Adj x y) ∧
        (∀ x y, D x y → ¬ D y x) ∧
        (∀ x y, R.Adj x y → D x y ∨ D y x) ∧
        (∀ v : V,
          (Finset.univ.filter (fun y => D v y)).card = R.degree v / 2 ∧
          (Finset.univ.filter (fun y => D y v)).card = R.degree v / 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro R _ hcard heven
    by_cases hempty : R.edgeFinset = ∅
    · refine ⟨fun _ _ => False, by simp, by simp, ?_, ?_⟩
      · intro x y hxy
        have : s(x, y) ∈ R.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hxy
        rw [hempty] at this
        simp at this
      · intro v
        have hdeg0 : R.degree v = 0 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
          ext y
          simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
          intro hxy
          have : s(v, y) ∈ R.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hxy
          rw [hempty] at this
          simp at this
        simp [hdeg0]
    · have hne : R.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨cy, hcy3, hcy_nd, hcy_ch, hcy_ne, hcy_close⟩ := exists_simple_cycle R heven hne
      let L := cy.length
      have hL3 : 3 ≤ L := hcy3
      -- Directed edges of the cycle cy
      let Dcy : V → V → Prop := fun x y =>
        ∃ i : Fin L, cy[i] = x ∧ cy[(i.val + 1) % L]'(Nat.mod_lt _ (by omega)) = y
      have hDcy_adj : ∀ x y, Dcy x y → R.Adj x y := by
        rintro x y ⟨i, rfl, rfl⟩
        by_cases hi : i.val + 1 < L
        · have hmod : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hi
          simp only [hmod]
          exact List.isChain_iff_getElem.mp hcy_ch i.val hi
        · have hiL : i.val = L - 1 := by omega
          have hmod : (i.val + 1) % L = 0 := by
            rw [show i.val + 1 = L by omega, Nat.mod_self]
          simp only [hmod]
          have h1 : cy[i] = cy.getLast hcy_ne := by
            rw [List.getLast_eq_getElem]
            simp [hiL, L]
          have h2 : cy[0]'(by omega) = cy.head hcy_ne := (List.head_eq_getElem hcy_ne).symm
          rw [h1, h2]
          exact hcy_close
      have hDcy_asym : ∀ x y, Dcy x y → ¬ Dcy y x := by
        rintro x y ⟨i, rfl, rfl⟩ ⟨j, hj1, hj2⟩
        have hji : j.val = (i.val + 1) % L :=
          (List.Nodup.getElem_inj_iff hcy_nd).mp hj1
        have hij : i.val = (j.val + 1) % L :=
          ((List.Nodup.getElem_inj_iff hcy_nd).mp hj2).symm
        rw [hji] at hij
        have hmod : ((i.val + 1) % L + 1) % L = (i.val + 2) % L := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [hmod] at hij
        by_cases h1 : i.val + 2 < L
        · rw [Nat.mod_eq_of_lt h1] at hij
          omega
        · have h2 : i.val + 2 - L < L := by omega
          have hmod2 : (i.val + 2) % L = i.val + 2 - L := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
          rw [hmod2] at hij
          omega
      -- Out-degree and in-degree of Dcy
      have hDcy_out : ∀ v : V,
          (Finset.univ.filter (fun y => Dcy v y)).card = if v ∈ cy then 1 else 0 := by
        intro v
        split_ifs with hv
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
          have hset : Finset.univ.filter (fun y => Dcy cy[i] y) =
              {cy[(i + 1) % L]'(Nat.mod_lt _ (by omega))} := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨j, hj1, rfl⟩
              have hjeq : j.val = i := (List.Nodup.getElem_inj_iff hcy_nd).mp hj1
              simp [hjeq]
            · rintro rfl
              exact ⟨⟨i, hi⟩, rfl, rfl⟩
          rw [hset, Finset.card_singleton]
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro y _ ⟨i, rfl, _⟩
          exact hv (List.getElem_mem i.2)
      have hDcy_in : ∀ v : V,
          (Finset.univ.filter (fun y => Dcy y v)).card = if v ∈ cy then 1 else 0 := by
        intro v
        split_ifs with hv
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
          let prev := (i + L - 1) % L
          have hprev_lt : prev < L := Nat.mod_lt _ (by omega)
          have hprev_next : (prev + 1) % L = i := by
            dsimp [prev]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show i + L - 1 + 1 = i + L by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hi]
          have hset : Finset.univ.filter (fun y => Dcy y cy[i]) = {cy[prev]'hprev_lt} := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨j, rfl, hj2⟩
              have hjmod : (j.val + 1) % L = i := (List.Nodup.getElem_inj_iff hcy_nd).mp hj2
              have hjeq : j.val = prev := by
                dsimp [prev]
                have hstep : (j.val + L) % L = (i + L - 1) % L := by
                  rw [← hjmod]
                  by_cases hjL : j.val + 1 < L
                  · rw [Nat.mod_eq_of_lt hjL]
                    have : j.val + 1 + L - 1 = j.val + L := by omega
                    rw [this]
                  · have hj_last : j.val = L - 1 := by omega
                    rw [show j.val + 1 = L by omega, Nat.mod_self, Nat.zero_add,
                      show j.val + L = (L - 1) + L by omega, Nat.add_mod_right]
                simpa [Nat.add_mod_right, Nat.mod_eq_of_lt j.2] using hstep
              simp [hjeq]
            · rintro rfl
              exact ⟨⟨prev, hprev_lt⟩, rfl, by simp [hprev_next]⟩
          rw [hset, Finset.card_singleton]
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro y _ ⟨i, _, rfl⟩
          exact hv (List.getElem_mem _)
      -- Residual graph R' = R \ E(cy)
      let R' : SimpleGraph V :=
        { Adj := fun x y => R.Adj x y ∧ ¬ Dcy x y ∧ ¬ Dcy y x
          symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
          loopless := ⟨fun _ h => R.irrefl h.1⟩ }
      have hR'_le : R' ≤ R := fun _ _ h => h.1
      have hR'_sub : R'.edgeFinset ⊂ R.edgeFinset := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨SimpleGraph.edgeFinset_mono hR'_le, ?_⟩
        intro heq
        have h0 : Dcy (cy[0]'(by omega)) (cy[1]'(by omega)) :=
          ⟨⟨0, by omega⟩, rfl, by simp [Nat.mod_eq_of_lt (by omega : 1 < L)]⟩
        have hmemR : s(cy[0]'(by omega), cy[1]'(by omega)) ∈ R.edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr (hDcy_adj _ _ h0)
        rw [← heq, SimpleGraph.mem_edgeFinset] at hmemR
        exact hmemR.2.1 h0
      have hR'_card : R'.edgeFinset.card < m :=
        lt_of_lt_of_le (Finset.card_lt_card hR'_sub) hcard
      -- Degree of every vertex in R'
      have hR'_deg : ∀ v : V, R'.degree v + (if v ∈ cy then 2 else 0) = R.degree v := by
        intro v
        let S_out := Finset.univ.filter (fun y => Dcy v y)
        let S_in := Finset.univ.filter (fun y => Dcy y v)
        have hdisj_oi : Disjoint S_out S_in := by
          rw [Finset.disjoint_left]
          intro y hy1 hy2
          exact hDcy_asym v y (Finset.mem_filter.mp hy1).2 (Finset.mem_filter.mp hy2).2
        have hdisj_R' : Disjoint (R'.neighborFinset v) (S_out ∪ S_in) := by
          rw [Finset.disjoint_left]
          intro y hy1 hy2
          have h1 : R'.Adj v y := (SimpleGraph.mem_neighborFinset R' v y).mp hy1
          rcases Finset.mem_union.mp hy2 with hy | hy
          · exact h1.2.1 (Finset.mem_filter.mp hy).2
          · exact h1.2.2 (Finset.mem_filter.mp hy).2
        have hunion : R'.neighborFinset v ∪ (S_out ∪ S_in) = R.neighborFinset v := by
          ext y
          simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, S_out, S_in,
            Finset.mem_filter, Finset.mem_univ, true_and, R']
          constructor
          · rintro (⟨h, _, _⟩ | h | h)
            · exact h
            · exact hDcy_adj v y h
            · exact (hDcy_adj y v h).symm
          · intro h
            by_cases h1 : Dcy v y
            · exact Or.inr (Or.inl h1)
            · by_cases h2 : Dcy y v
              · exact Or.inr (Or.inr h2)
              · exact Or.inl ⟨h, h1, h2⟩
        have hcard_u : R'.degree v + (S_out.card + S_in.card) = R.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree,
            ← SimpleGraph.card_neighborFinset_eq_degree, ← hunion,
            Finset.card_union_of_disjoint hdisj_R', Finset.card_union_of_disjoint hdisj_oi]
        rw [hDcy_out v, hDcy_in v] at hcard_u
        split_ifs at hcard_u ⊢ <;> omega
      have hR'_even : ∀ v : V, Even (R'.degree v) := by
        intro v
        obtain ⟨t, ht⟩ := heven v
        have h := hR'_deg v
        split_ifs at h
        · exact ⟨t - 1, by omega⟩
        · exact ⟨t, by omega⟩
      obtain ⟨D', hD'_adj, hD'_asym, hD'_cov, hD'_deg⟩ :=
        ih R'.edgeFinset.card hR'_card R' le_rfl hR'_even
      -- Combine D' and Dcy
      refine ⟨fun x y => D' x y ∨ Dcy x y, ?_, ?_, ?_, ?_⟩
      · rintro x y (h | h)
        · exact (hD'_adj x y h).1
        · exact hDcy_adj x y h
      · rintro x y (h1 | h1) (h2 | h2)
        · exact hD'_asym x y h1 h2
        · exact (hD'_adj x y h1).2.2 h2
        · exact (hD'_adj y x h2).2.2 h1
        · exact hDcy_asym x y h1 h2
      · intro x y hxy
        by_cases h1 : Dcy x y
        · exact Or.inl (Or.inr h1)
        · by_cases h2 : Dcy y x
          · exact Or.inr (Or.inr h2)
          · rcases hD'_cov x y ⟨hxy, h1, h2⟩ with h' | h'
            · exact Or.inl (Or.inl h')
            · exact Or.inr (Or.inl h')
      · intro v
        have hdisj_out : Disjoint (Finset.univ.filter (fun y => D' v y))
            (Finset.univ.filter (fun y => Dcy v y)) := by
          rw [Finset.disjoint_left]
          intro y h1 h2
          exact (hD'_adj v y (Finset.mem_filter.mp h1).2).2.1 (Finset.mem_filter.mp h2).2
        have hdisj_in : Disjoint (Finset.univ.filter (fun y => D' y v))
            (Finset.univ.filter (fun y => Dcy y v)) := by
          rw [Finset.disjoint_left]
          intro y h1 h2
          exact (hD'_adj y v (Finset.mem_filter.mp h1).2).2.1 (Finset.mem_filter.mp h2).2
        have hdeg := hR'_deg v
        constructor
        · have hc : (Finset.univ.filter (fun y => D' v y ∨ Dcy v y)).card =
              (Finset.univ.filter (fun y => D' v y) ∪ Finset.univ.filter (fun y => Dcy v y)).card := by
            congr 1; ext y; simp
          have hc' : (Finset.univ.filter (fun y => D' v y) ∪ Finset.univ.filter (fun y => Dcy v y)).card =
              R.degree v / 2 := by
            rw [Finset.card_union_of_disjoint hdisj_out, (hD'_deg v).1, hDcy_out v]
            split_ifs at hdeg ⊢ <;> omega
          convert hc' using 1
          congr 1; ext y; simp
        · have hc' : (Finset.univ.filter (fun y => D' y v) ∪ Finset.univ.filter (fun y => Dcy y v)).card =
              R.degree v / 2 := by
            rw [Finset.card_union_of_disjoint hdisj_in, (hD'_deg v).2, hDcy_in v]
            split_ifs at hdeg ⊢ <;> omega
          convert hc' using 1
          congr 1; ext y; simp

/-- Every finite `(2 * k)`-regular simple graph with `k ≥ 1` has a spanning 2-regular subgraph
(Petersen's 2-factor theorem). -/
private lemma exists_two_factor (R : SimpleGraph V) [DecidableRel R.Adj] {k : ℕ}
    (hk : 1 ≤ k) (hreg : R.IsRegularOfDegree (2 * k)) :
    ∃ F : SimpleGraph V, F ≤ R ∧ F.IsRegularOfDegree 2 := by
  classical
  have heven : ∀ v : V, Even (R.degree v) := fun v => ⟨k, by rw [hreg v]; omega⟩
  obtain ⟨D, hD_adj, hD_asym, _, hD_deg⟩ :=
    exists_balanced_orientation R.edgeFinset.card R le_rfl heven
  have hout : ∀ v : V, (Finset.univ.filter (fun y => D v y)).card = k := fun v => by
    rw [(hD_deg v).1, hreg v]; omega
  have hin : ∀ v : V, (Finset.univ.filter (fun y => D y v)).card = k := fun v => by
    rw [(hD_deg v).2, hreg v]; omega
  -- Apply Hall's marriage theorem to the out-neighborhood family.
  let t : V → Finset V := fun x => Finset.univ.filter (fun y => D x y)
  have hHall : ∀ s : Finset V, s.card ≤ (s.biUnion t).card := by
    intro s
    have hcount1 : ∑ x ∈ s, (t x).card = k * s.card := by
      rw [Finset.sum_congr rfl (fun x _ => hout x), Finset.sum_const, smul_eq_mul, mul_comm]
    have hcount2 : ∑ x ∈ s, (t x).card =
        ∑ y ∈ s.biUnion t, (s.filter (fun x => y ∈ t x)).card := by
      have hlhs : ∑ x ∈ s, (t x).card =
          ∑ x ∈ s, ∑ y ∈ s.biUnion t, if y ∈ t x then 1 else 0 := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_biUnion]
        exact ⟨fun hy => ⟨⟨x, hx, hy⟩, hy⟩, fun h => h.2⟩
      rw [hlhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_boole, Nat.cast_id]
    have hle : ∑ y ∈ s.biUnion t, (s.filter (fun x => y ∈ t x)).card ≤ k * (s.biUnion t).card := by
      calc ∑ y ∈ s.biUnion t, (s.filter (fun x => y ∈ t x)).card
          ≤ ∑ y ∈ s.biUnion t, (Finset.univ.filter (fun x => D x y)).card := by
            refine Finset.sum_le_sum fun y _ => Finset.card_le_card ?_
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, t] at hx ⊢
            exact hx.2
        _ = ∑ _y ∈ s.biUnion t, k := Finset.sum_congr rfl fun y _ => hin y
        _ = k * (s.biUnion t).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hmul : k * s.card ≤ k * (s.biUnion t).card := by omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
  let e : V ≃ V := Equiv.ofBijective f hf_bij
  have he_D : ∀ x : V, D x (e x) := fun x => (Finset.mem_filter.mp (hf_mem x)).2
  let F : SimpleGraph V :=
    { Adj := fun x y => e x = y ∨ e y = x
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun x h => by
        rcases h with h | h
        · exact R.irrefl (hD_adj x x (by simpa [h] using he_D x))
        · exact R.irrefl (hD_adj x x (by simpa [h] using he_D x))⟩ }
  refine ⟨F, ?_, ?_⟩
  · rintro x y (rfl | rfl)
    · exact hD_adj x (e x) (he_D x)
    · exact (hD_adj y (e y) (he_D y)).symm
  · intro x
    have hne_symm : e x ≠ e.symm x := by
      intro heq
      have hff : e (e x) = x := by
        rw [heq]
        exact e.apply_symm_apply x
      have h2 : D (e x) x := by simpa [hff] using he_D (e x)
      exact hD_asym x (e x) (he_D x) h2
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_pair hne_symm]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, F, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (e.symm_apply_eq.mpr h.symm).symm
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (e.apply_symm_apply x)

end BalancedOrientation

end PetersenTwoFactor

theorem OMA.solution : OMA.R_opg_uniquely_hamiltonian_graphs_R1_H4_R1.H1 := by
  classical
  intro V _ _ G _ r hr_even hr6 _ hreg v c hc
  let C : SimpleGraph V := PetersenTwoFactor.walkGraph G c
  have hC_le : C ≤ G := PetersenTwoFactor.walkGraph_le G c
  have hC_reg : C.IsRegularOfDegree 2 := PetersenTwoFactor.walkGraph_isRegular_two G c hc
  let R : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ ¬ C.Adj x y
      symm := ⟨fun _ _ h => ⟨h.1.symm, fun hc' => h.2 hc'.symm⟩⟩
      loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hR_le : R ≤ G := fun _ _ h => h.1
  have hR_disj : ∀ x y, ¬ (R.Adj x y ∧ C.Adj x y) := fun _ _ ⟨h1, h2⟩ => h1.2 h2
  obtain ⟨m, hm⟩ := hr_even
  have hm3 : 3 ≤ m := by omega
  have hR_reg : R.IsRegularOfDegree (2 * (m - 1)) := by
    intro x
    have hdisj : Disjoint (R.neighborFinset x) (C.neighborFinset x) := by
      rw [Finset.disjoint_left]
      intro y h1 h2
      rw [SimpleGraph.mem_neighborFinset] at h1 h2
      exact hR_disj x y ⟨h1, h2⟩
    have hunion : R.neighborFinset x ∪ C.neighborFinset x = G.neighborFinset x := by
      ext y
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, R]
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact hC_le h
      · intro h
        by_cases hC : C.Adj x y
        · exact Or.inr hC
        · exact Or.inl ⟨h, hC⟩
    have hsum : R.degree x + C.degree x = G.degree x := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree, ← hunion,
        Finset.card_union_of_disjoint hdisj]
    have hGx := hreg x
    have hCx := hC_reg x
    omega
  obtain ⟨F, hF_le, hF_reg⟩ := PetersenTwoFactor.exists_two_factor R (k := m - 1) (by omega) hR_reg
  let H : SimpleGraph V := C ⊔ F
  refine ⟨H, sup_le hC_le (le_trans hF_le hR_le), ?_, ?_⟩
  · intro x
    have hdisj : Disjoint (C.neighborFinset x) (F.neighborFinset x) := by
      rw [Finset.disjoint_left]
      intro y h1 h2
      rw [SimpleGraph.mem_neighborFinset] at h1 h2
      exact hR_disj x y ⟨hF_le h2, h1⟩
    have h4 : (C.neighborFinset x ∪ F.neighborFinset x).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj,
        SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree,
        hC_reg x, hF_reg x]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← h4]
    congr 1
    ext y
    simp [H, SimpleGraph.mem_neighborFinset]
  · intro e he
    rcases e with ⟨x, y⟩
    exact Or.inl he
